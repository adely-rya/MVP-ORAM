package main

// sim.go: 決定的なシミュレーション。1 ラウンド = c クライアントが同時に
// getPM → getPS → evict を行う (論文のスタッシュ解析と同じ「最大並列」の最悪ケース)。
// evict の順番はラウンドごとにランダム。

import (
	"fmt"
	"math"
	"math/rand"
	"sort"
)

type Workload struct {
	N         int
	ReadRatio float64
	Weights   []float64 // アドレスごとのアクセス確率
	cdf       []float64
}

// NewZipf: rank r の確率 ∝ r^-alpha。rank とアドレスの対応はランダムな置換。
// alpha = 0 なら一様。
func NewWorkload(N int, alpha float64, readRatio float64, rng *rand.Rand) *Workload {
	w := make([]float64, N)
	perm := rng.Perm(N)
	sum := 0.0
	for r := 0; r < N; r++ {
		p := math.Pow(float64(r+1), -alpha)
		w[perm[r]] = p
		sum += p
	}
	cdf := make([]float64, N)
	acc := 0.0
	for i := range w {
		w[i] /= sum
		acc += w[i]
		cdf[i] = acc
	}
	return &Workload{N: N, ReadRatio: readRatio, Weights: w, cdf: cdf}
}

func (wl *Workload) Next(rng *rand.Rand) (addr int, write bool) {
	u := rng.Float64()
	addr = sort.SearchFloat64s(wl.cdf, u)
	if addr >= wl.N {
		addr = wl.N - 1
	}
	return addr, rng.Float64() >= wl.ReadRatio
}

type Sim struct {
	cfg      *Config
	srv      *Server
	clients  []*Client
	wl       *Workload
	rng      *rand.Rand
	expected []int // 線形化可能性チェック: 直前ラウンドまでに確定した最新の書き込み値
	round    int
	obs      *Observer
	// Strong MVP-ORAM: σ+1 ラウンドを1バッチとし、各クライアントは τ 番目のラウンドだけ実アクセス
	batchOps []Op
	batchTau []int
	// 論文の指標: 1 タイムステップ内で要求された異なるリーフ数 K の分布
	KHist []int
}

const observerID = -1

func NewSim(cfg *Config, clients int, wl *Workload, seed int64) *Sim {
	rng := rand.New(rand.NewSource(seed))
	srv := NewServer(cfg.L, cfg.Z)
	var initPM []pmEntry
	if cfg.EmptyStart {
		initPM = make([]pmEntry, cfg.N)
		for a := range initPM {
			initPM[a] = pmEntry{LocStash, tsBottom}
		}
		srv.stashes = []*stashVersion{{born: 0}}
	} else {
		initPM = initialize(srv, cfg, rng)
	}
	s := &Sim{cfg: cfg, srv: srv, wl: wl, rng: rng, expected: make([]int, cfg.N)}
	for i := 0; i < clients; i++ {
		s.clients = append(s.clients, NewClient(i, cfg, initPM, seed*7919+int64(i)+1))
		srv.cursor[i] = 0
	}
	srv.RegisterReader(observerID)
	s.obs = NewObserver(cfg, initPM)
	return s
}

// initialize: 各ブロックをランダムなリーフのパス上で、最も深い空きスロットに置く(なければスタッシュ)。
func initialize(srv *Server, cfg *Config, rng *rand.Rand) []pmEntry {
	pm := make([]pmEntry, cfg.N)
	var stash []Block
	for a := 0; a < cfg.N; a++ {
		b := Block{Addr: a, Data: 0, TS: TS{0, 0, 0}}
		leaf := rng.Intn(1 << cfg.L)
		slots := PathSlots(cfg.L, cfg.Z, leaf)
		placed := false
		for i := len(slots) - 1; i >= 0; i-- {
			if len(srv.slots[slots[i]]) == 0 {
				srv.slots[slots[i]] = []entry{{b: b, born: 0}}
				pm[a] = pmEntry{slots[i], b.TS}
				placed = true
				break
			}
		}
		if !placed {
			stash = append(stash, b)
			pm[a] = pmEntry{LocStash, b.TS}
		}
	}
	srv.stashes = []*stashVersion{{blocks: stash, born: 0}}
	return pm
}

// RoundStats は1ラウンド(c アクセス)の合計。
type RoundStats struct {
	Accesses, Reads, ViaReplica, Dummies    int
	SZChosen, SZEmpty, SZHadReplica         int
	InSwapped, InCollision, InTarget, Out   int
	RepKept, RepDropped, RepCreated         int
	MlLen, MlLenRead, MlLenWrite, Writes    int
	PMEntries, PSBlocks, PSStash, EvictSlot int
	EvictStash                              int
	CandLeaves                              float64 // アクセス時の候補リーフ数(平均用の合計)
	Client0Stash                            int     // 公開実装の Fig.7 の値: クライアント0が書いた新スタッシュの長さ(ラウンド合計)
}

func (s *Sim) Round() RoundStats {
	s.round++
	c := len(s.clients)
	ops := make([]Op, c)
	var st RoundStats
	sigma := s.cfg.Sigma
	step := (s.round - 1) % (sigma + 1)
	if step == 0 {
		// バッチ開始: 各クライアントが実アクセスの対象を宣言し、同じアドレスを宣言した順に τ を決める
		s.batchOps = make([]Op, c)
		s.batchTau = make([]int, c)
		count := map[int]int{}
		for _, i := range s.rng.Perm(c) {
			addr, write := s.wl.Next(s.rng)
			s.batchOps[i] = Op{Write: write, Addr: addr}
			s.batchTau[i] = count[addr] % (sigma + 1) // σ+1 人を超えたら同じタイムステップを共有する
			count[addr]++
		}
	}
	leaves := map[int]bool{}
	for i, cl := range s.clients {
		if step == s.batchTau[i] {
			ops[i] = s.batchOps[i]
		} else {
			ops[i] = Op{Dummy: true}
		}
		seq, diff := s.srv.GetPM(cl.ID)
		ops[i].Data = seq
		st.PMEntries += s.srv.Stats.GetPMEntries
		leaves[cl.Prepare(seq, diff, ops[i])] = true
		if !ops[i].Dummy {
			st.CandLeaves += float64(intervalsSize(unionLeaves(s.cfg.L, s.cfg.Z, copyLocs(cl.prim, cl.reps, ops[i].Addr))))
		}
	}
	if s.KHist == nil {
		s.KHist = make([]int, c+1)
	}
	s.KHist[len(leaves)]++
	type out struct {
		ml    []LogEntry
		path  map[int]*Block
		stash []Block
	}
	outs := make([]out, c)
	for i, cl := range s.clients {
		path, stashes := s.srv.GetPS(cl.ID, cl.Last.Leaf)
		st.PSBlocks += s.srv.Stats.GetPSBlocks
		st.PSStash += s.srv.Stats.GetPSStash
		ml, P, S := cl.Finish(ops[i], path, stashes)
		outs[i] = out{ml, P, S}
		if !ops[i].Dummy && !ops[i].Write && cl.Last.Data != s.expected[ops[i].Addr] {
			panic(fmt.Sprintf("linearizability violated: round %d client %d addr %d read %d want %d (via copy %d)",
				s.round, cl.ID, ops[i].Addr, cl.Last.Data, s.expected[ops[i].Addr], cl.Last.ViaCopy))
		}
	}
	order := s.rng.Perm(c)
	if s.cfg.FixedEvictOrder {
		for i := range order {
			order[i] = i
		}
	}
	for _, i := range order {
		cl := s.clients[i]
		if i == 0 {
			st.Client0Stash = len(outs[i].stash)
		}
		s.srv.Evict(cl.ID, cl.Last.Leaf, outs[i].ml, outs[i].path, outs[i].stash)
		st.EvictSlot += (s.cfg.L + 1) * s.cfg.Z
		st.EvictStash += len(outs[i].stash)
	}
	// このラウンドの書き込みを反映 (同じアドレスなら seq 最大が勝つ)
	lastSeq := map[int]int{}
	for i := range s.clients {
		if !ops[i].Dummy && ops[i].Write && ops[i].Data > lastSeq[ops[i].Addr] {
			lastSeq[ops[i].Addr] = ops[i].Data
		}
	}
	for a, v := range lastSeq {
		s.expected[a] = v
	}
	for i, cl := range s.clients {
		t := cl.Last
		if ops[i].Dummy {
			st.Dummies++
			st.MlLen += t.MlLen
			st.SZEmpty += t.SZEmpty
			st.SZChosen += t.SZChosen
			st.Out += t.OutStashToPath
			st.InSwapped += t.InStashSwapped
			continue
		}
		st.Accesses++
		if ops[i].Write {
			st.Writes++
			st.MlLenWrite += t.MlLen
		} else {
			st.Reads++
			st.MlLenRead += t.MlLen
		}
		if t.ViaCopy != 0 {
			st.ViaReplica++
		}
		st.SZChosen += t.SZChosen
		st.SZEmpty += t.SZEmpty
		st.SZHadReplica += t.SZHadReplica
		st.InSwapped += t.InStashSwapped
		st.InCollision += t.InStashCollision
		st.InTarget += t.InStashTarget
		st.Out += t.OutStashToPath
		st.RepKept += t.RepKept
		st.RepDropped += t.RepDropped
		st.RepCreated += t.RepCreated
		st.MlLen += t.MlLen
	}
	if s.round%50 == 0 {
		s.obs.Update(s.srv.ReadHistory(observerID))
		s.srv.CompactHistory()
	}
	return st
}

func (r *RoundStats) Add(o RoundStats) {
	r.Accesses += o.Accesses
	r.Dummies += o.Dummies
	r.Reads += o.Reads
	r.Writes += o.Writes
	r.ViaReplica += o.ViaReplica
	r.SZChosen += o.SZChosen
	r.SZEmpty += o.SZEmpty
	r.SZHadReplica += o.SZHadReplica
	r.InSwapped += o.InSwapped
	r.InCollision += o.InCollision
	r.InTarget += o.InTarget
	r.Out += o.Out
	r.RepKept += o.RepKept
	r.RepDropped += o.RepDropped
	r.RepCreated += o.RepCreated
	r.MlLen += o.MlLen
	r.MlLenRead += o.MlLenRead
	r.MlLenWrite += o.MlLenWrite
	r.PMEntries += o.PMEntries
	r.PSBlocks += o.PSBlocks
	r.PSStash += o.PSStash
	r.EvictSlot += o.EvictSlot
	r.EvictStash += o.EvictStash
	r.CandLeaves += o.CandLeaves
	r.Client0Stash += o.Client0Stash
}

// IdealKDist: c 個のリーフを 2^L 個から独立一様に選んだときの異なるリーフ数の分布 (論文の比較対象)。
func IdealKDist(L, c int) []float64 {
	n := float64(int(1) << L)
	p := make([]float64, c+1)
	p[0] = 1
	for j := 0; j < c; j++ {
		q := make([]float64, c+1)
		for k := 0; k <= j; k++ {
			if p[k] == 0 {
				continue
			}
			q[k] += p[k] * float64(k) / n
			q[k+1] += p[k] * (n - float64(k)) / n
		}
		p = q
	}
	return p
}

// KDistanceTV は観測した K の分布と理想分布の全変動距離 (論文 Fig. 5/6 の statistical distance)。
func KDistanceTV(hist []int, ideal []float64) float64 {
	tot := 0
	for _, v := range hist {
		tot += v
	}
	if tot == 0 {
		return 0
	}
	d := 0.0
	for k := range ideal {
		o := 0.0
		if k < len(hist) {
			o = float64(hist[k]) / float64(tot)
		}
		d += math.Abs(o - ideal[k])
	}
	return d / 2
}
