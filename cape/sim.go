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
}

const observerID = -1

func NewSim(cfg *Config, clients int, wl *Workload, seed int64) *Sim {
	rng := rand.New(rand.NewSource(seed))
	srv := NewServer(cfg.L, cfg.Z)
	initPM := initialize(srv, cfg, rng)
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
	Accesses, Reads, ViaReplica             int
	SZChosen, SZEmpty, SZHadReplica         int
	InSwapped, InCollision, InTarget, Out   int
	RepKept, RepDropped, RepCreated         int
	MlLen, MlLenRead, MlLenWrite, Writes    int
	PMEntries, PSBlocks, PSStash, EvictSlot int
	EvictStash                              int
	CandLeaves                              float64 // アクセス時の候補リーフ数(平均用の合計)
}

func (s *Sim) Round() RoundStats {
	s.round++
	c := len(s.clients)
	ops := make([]Op, c)
	var st RoundStats
	for i, cl := range s.clients {
		addr, write := s.wl.Next(s.rng)
		ops[i] = Op{Write: write, Addr: addr}
		seq, diff := s.srv.GetPM(cl.ID)
		ops[i].Data = seq
		st.PMEntries += s.srv.Stats.GetPMEntries
		cl.Prepare(seq, diff, ops[i])
		st.CandLeaves += float64(intervalsSize(unionLeaves(s.cfg.L, s.cfg.Z, copyLocs(cl.prim, cl.reps, addr))))
	}
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
		if !ops[i].Write && cl.Last.Data != s.expected[ops[i].Addr] {
			panic(fmt.Sprintf("linearizability violated: round %d client %d addr %d read %d want %d (via copy %d)",
				s.round, cl.ID, ops[i].Addr, cl.Last.Data, s.expected[ops[i].Addr], cl.Last.ViaCopy))
		}
	}
	for _, i := range s.rng.Perm(c) {
		cl := s.clients[i]
		s.srv.Evict(cl.ID, cl.Last.Leaf, outs[i].ml, outs[i].path, outs[i].stash)
		st.EvictSlot += (s.cfg.L + 1) * s.cfg.Z
		st.EvictStash += len(outs[i].stash)
	}
	// このラウンドの書き込みを反映 (同じアドレスなら seq 最大が勝つ)
	lastSeq := map[int]int{}
	for i := range s.clients {
		if ops[i].Write && ops[i].Data > lastSeq[ops[i].Addr] {
			lastSeq[ops[i].Addr] = ops[i].Data
		}
	}
	for a, v := range lastSeq {
		s.expected[a] = v
	}
	for i, cl := range s.clients {
		t := cl.Last
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
}
