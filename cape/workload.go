package main

// workload.go: アクセス列の生成器。
//
// 論文化のときに出典を示せるよう、YCSB (Cooper et al., "Benchmarking Cloud Serving Systems
// with YCSB", SoCC 2010) のコアワークロードと、その request distribution をそのまま使う。
//   ycsb-a  read 0.5 / update 0.5,              zipfian(0.99)
//   ycsb-b  read 0.95 / update 0.05,            zipfian(0.99)
//   ycsb-c  read 1.0,                           zipfian(0.99)
//   ycsb-d  read 0.95 / insert 0.05,            latest   (人気が新しく挿入されたキーへ移り続ける = 動的な偏り)
//   ycsb-f  read 0.5 / read-modify-write 0.5,   zipfian(0.99)
//   uniform ycsb-a の requestdistribution=uniform
//   hotspot ycsb-a の requestdistribution=hotspot (hotspotdatafraction=0.2, hotspotopnfraction=0.8; YCSB の既定値)
//
// ORAM への写像で YCSB と異なる点:
//   - YCSB の scrambled zipfian はキーをハッシュで並べ替える。ここではランダムな置換で同じことをする
//     (ORAM の配置はアドレスに依存しないので、置換の選び方は結果に影響しない)。
//   - ORAM の容量は N で固定なので、ycsb-d の insert は「最も古いレコードのアドレスへの書き込み」
//     (循環バッファ) として扱う。latest 分布は「挿入順で新しいほど人気」の zipfian(0.99)。
//   - read-modify-write は同じクライアントの連続した 2 回のアクセス (read の次に write)。

import (
	"fmt"
	"math"
	"math/rand"
	"sort"
)

type WorkloadKind int

const (
	WLZipf WorkloadKind = iota
	WLHotspot
	WLLatest
)

const ycsbZipfConst = 0.99

type Workload struct {
	N         int
	Kind      WorkloadKind
	ReadRatio float64 // read の割合 (残りが update / insert / rmw)
	RMW       bool    // read 以外の操作を read-modify-write にする (ycsb-f)
	Distinct  bool    // 1バッチ内で同じアドレスを選ばない (K 分布の参照用)
	Weights   []float64
	cdf       []float64 // zipf: アドレス順の累積 / latest: 新しさの順位の累積
	// hotspot
	hotSet []int
	isHot  []bool
	hotOpn float64
	hotN   int
	// latest
	nextKey int
	ackKey  int // 完了した insert までのキー (YCSB の AcknowledgedCounterGenerator と同じく、read は完了済みのキーだけを選ぶ)
	// rmw: クライアントごとに保留中の write
	pending map[int]int
	last    map[int]lastOp
}

type lastOp struct {
	addr    int
	write   bool
	pending bool
	key     int
}

func zipfCDF(n int, alpha float64) ([]float64, []float64) {
	w := make([]float64, n)
	sum := 0.0
	for r := 0; r < n; r++ {
		w[r] = math.Pow(float64(r+1), -alpha)
		sum += w[r]
	}
	cdf := make([]float64, n)
	acc := 0.0
	for r := range w {
		w[r] /= sum
		acc += w[r]
		cdf[r] = acc
	}
	return w, cdf
}

// NewWorkload: rank r の確率 ∝ r^-alpha。rank とアドレスの対応はランダムな置換。alpha = 0 なら一様。
func NewWorkload(N int, alpha float64, readRatio float64, rng *rand.Rand) *Workload {
	wr, _ := zipfCDF(N, alpha)
	perm := rng.Perm(N)
	w := make([]float64, N)
	for r := 0; r < N; r++ {
		w[perm[r]] = wr[r]
	}
	cdf := make([]float64, N)
	acc := 0.0
	for i := range w {
		acc += w[i]
		cdf[i] = acc
	}
	return &Workload{N: N, Kind: WLZipf, ReadRatio: readRatio, Weights: w, cdf: cdf}
}

// NewYCSB は名前付きワークロードを作る。
func NewYCSB(name string, N int, rng *rand.Rand) (*Workload, error) {
	switch name {
	case "ycsb-a":
		return NewWorkload(N, ycsbZipfConst, 0.5, rng), nil
	case "ycsb-b":
		return NewWorkload(N, ycsbZipfConst, 0.95, rng), nil
	case "ycsb-c":
		return NewWorkload(N, ycsbZipfConst, 1.0, rng), nil
	case "ycsb-f":
		wl := NewWorkload(N, ycsbZipfConst, 0.5, rng)
		wl.RMW = true
		return wl, nil
	case "uniform":
		return NewWorkload(N, 0, 0.5, rng), nil
	case "hotspot":
		perm := rng.Perm(N)
		nh := int(0.2 * float64(N))
		wl := &Workload{N: N, Kind: WLHotspot, ReadRatio: 0.5, hotSet: perm, isHot: make([]bool, N), hotOpn: 0.8}
		wl.Weights = make([]float64, N)
		for _, a := range perm[:nh] {
			wl.isHot[a] = true
			wl.Weights[a] = 0.8 / float64(nh)
		}
		for _, a := range perm[nh:] {
			wl.Weights[a] = 0.2 / float64(N-nh)
		}
		wl.hotN = nh // hotSet[:nh] が hot, [nh:] が cold
		return wl, nil
	case "ycsb-d":
		_, cdf := zipfCDF(N, ycsbZipfConst)
		wl := &Workload{N: N, Kind: WLLatest, ReadRatio: 0.95, cdf: cdf, nextKey: N, ackKey: N}
		wl.Weights = make([]float64, N)
		wl.refreshLatestWeights()
		return wl, nil
	}
	return nil, fmt.Errorf("unknown workload %q", name)
}

// Ack: それまでに発行した insert が完了した (バッチの開始時に呼ぶ)。
func (wl *Workload) Ack() { wl.ackKey = wl.nextKey }

func (wl *Workload) refreshLatestWeights() {
	prev := 0.0
	for r := 0; r < wl.N; r++ {
		a := ((wl.ackKey-1-r)%wl.N + wl.N) % wl.N
		wl.Weights[a] = wl.cdf[r] - prev
		prev = wl.cdf[r]
	}
}

// CurrentWeights は現時点のアドレスごとのアクセス確率 (latest では時間とともに変わる)。
func (wl *Workload) CurrentWeights() []float64 {
	if wl.Kind == WLLatest {
		wl.refreshLatestWeights()
	}
	return wl.Weights
}

func (wl *Workload) Next(rng *rand.Rand) (addr int, write bool) { return wl.NextFor(-1, rng) }

// pendingRMW: 直前に返した操作が read-modify-write の後半 (引き直してはいけない) か。
func (wl *Workload) pendingRMW(client int) bool { return wl.last[client].pending }

// undo は Distinct のための引き直しで、直前の NextFor の副作用 (insert のキー消費) を戻す。
func (wl *Workload) undo(client int) {
	lo := wl.last[client]
	if wl.Kind == WLLatest && lo.write {
		wl.nextKey--
	}
	if wl.RMW && !lo.pending && !lo.write {
		delete(wl.pending, client)
	}
}

func (wl *Workload) NextFor(client int, rng *rand.Rand) (addr int, write bool) {
	if wl.last == nil {
		wl.last = map[int]lastOp{}
		wl.pending = map[int]int{}
	}
	if wl.RMW {
		if a, ok := wl.pending[client]; ok {
			delete(wl.pending, client)
			wl.last[client] = lastOp{addr: a, write: true, pending: true}
			return a, true
		}
	}
	isRead := rng.Float64() < wl.ReadRatio
	switch wl.Kind {
	case WLHotspot:
		nh := wl.hotN
		if rng.Float64() < wl.hotOpn {
			addr = wl.hotSet[rng.Intn(nh)]
		} else {
			addr = wl.hotSet[nh+rng.Intn(wl.N-nh)]
		}
		write = !isRead
	case WLLatest:
		if !isRead { // insert: 最も古いレコードを新しいキーで上書き
			addr = wl.nextKey % wl.N
			wl.nextKey++
			wl.last[client] = lastOp{addr: addr, write: true}
			return addr, true
		}
		r := sort.SearchFloat64s(wl.cdf, rng.Float64())
		if r >= wl.N {
			r = wl.N - 1
		}
		addr = ((wl.ackKey-1-r)%wl.N + wl.N) % wl.N
	default:
		addr = sort.SearchFloat64s(wl.cdf, rng.Float64())
		if addr >= wl.N {
			addr = wl.N - 1
		}
		write = !isRead
	}
	if wl.RMW && !isRead {
		// read-modify-write: まず read、次のアクセスで同じアドレスへ write
		wl.pending[client] = addr
		write = false
	}
	wl.last[client] = lastOp{addr: addr, write: write}
	return addr, write
}
