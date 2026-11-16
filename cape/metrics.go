package main

// metrics.go: サーバ状態の検証と安全性指標。
//
// 観測者はサーバのパスマップ履歴を全て consolidate した position map を持ち、
// それを基準に「有効なブロック」を数える(クライアントと同じ判定規則)。

import (
	"math"
	"sort"
)

type Observer struct {
	cfg  *Config
	prim []pmEntry
	reps []map[int]pmEntry
}

func NewObserver(cfg *Config, initPM []pmEntry) *Observer {
	return &Observer{cfg: cfg, prim: append([]pmEntry(nil), initPM...), reps: make([]map[int]pmEntry, cfg.N)}
}

func (o *Observer) Update(diff []LogEntry) { consolidateInto(o.prim, o.reps, diff) }

type GlobalState struct {
	TreePrimary, TreeReplica int
	TotalSlots               int
	StashValid, StashRaw     int
	StashVersions            int
	Lost                     int // 有効な本体が見つからないアドレス
	WrongData                int // 有効なレプリカの値が本体と違う
}

func (s *Sim) Observe() GlobalState {
	s.obs.Update(s.srv.ReadHistory(observerID))
	o := s.obs
	cfg := s.cfg
	var g GlobalState
	found := make([]bool, cfg.N)
	data := make([]int, cfg.N)
	repData := map[[2]int]int{}
	nodes := 1 << (cfg.L + 1)
	for sl := cfg.Z; sl < nodes*cfg.Z; sl++ {
		g.TotalSlots++
		for _, b := range s.srv.AliveSlot(sl) {
			if b.Copy == 0 {
				if o.prim[b.Addr].Loc == sl && o.prim[b.Addr].TS == b.TS {
					g.TreePrimary++
					found[b.Addr] = true
					data[b.Addr] = b.Data
				}
				continue
			}
			r, ok := o.reps[b.Addr][b.Copy]
			if ok && r.Loc == sl && r.TS == b.TS && b.TS.V == o.prim[b.Addr].TS.V {
				g.TreeReplica++
				repData[[2]int{b.Addr, b.Copy}] = b.Data
			}
		}
	}
	for _, st := range s.srv.AliveStashes() {
		g.StashVersions++
		g.StashRaw += len(st)
		for _, b := range st {
			if b.Copy == 0 && o.prim[b.Addr].Loc == LocStash && o.prim[b.Addr].TS == b.TS && !found[b.Addr] {
				found[b.Addr] = true
				data[b.Addr] = b.Data
				g.StashValid++
			}
		}
	}
	for a := 0; a < cfg.N; a++ {
		if !found[a] {
			g.Lost++
		}
	}
	for k, v := range repData {
		if v != data[k[0]] {
			g.WrongData++
		}
	}
	return g
}

// --- 安全性指標 ---

// copyNodes はアドレスの有効なコピーのノード番号 (スタッシュなら nil, true)。
func (o *Observer) copyNodes(a int) (nodes []int, inStash bool) {
	Z := o.cfg.Z
	if o.prim[a].Loc == LocStash {
		inStash = true
	} else {
		nodes = append(nodes, slotNode(Z, o.prim[a].Loc))
	}
	for _, r := range o.reps[a] {
		if r.Loc >= 0 && r.TS.V == o.prim[a].TS.V {
			nodes = append(nodes, slotNode(Z, r.Loc))
		}
	}
	return
}

func isAncestor(a, b int) bool { // a が b の祖先 (a != b)
	for b > a {
		b >>= 1
		if b == a {
			return true
		}
	}
	return false
}

// nonNestedK: 祖先に別コピーがあるコピーは数えない。同じノードの複数コピーは1つ。
func nonNestedK(nodes []int) int {
	uniq := map[int]bool{}
	for _, n := range nodes {
		uniq[n] = true
	}
	k := 0
	for n := range uniq {
		nested := false
		for m := range uniq {
			if m != n && isAncestor(m, n) {
				nested = true
				break
			}
		}
		if !nested {
			k++
		}
	}
	return k
}

// leafDist はパス選択規則に従ったリーフ分布 (長さ 2^L)。
func (o *Observer) leafDist(a int, buf []float64) {
	L, Z := o.cfg.L, o.cfg.Z
	for i := range buf {
		buf[i] = 0
	}
	nodes, inStash := o.copyNodes(a)
	if inStash && o.cfg.LeafRule == LeafUnionUniform {
		u := 1.0 / float64(len(buf))
		for i := range buf {
			buf[i] = u
		}
		return
	}
	switch o.cfg.LeafRule {
	case LeafCopyUniform:
		k := float64(len(nodes))
		if inStash {
			k++
			u := 1.0 / k / float64(len(buf))
			for i := range buf {
				buf[i] += u
			}
		}
		for _, n := range nodes {
			lo, hi := leafRange(L, n)
			u := 1.0 / k / float64(hi-lo)
			for i := lo; i < hi; i++ {
				buf[i] += u
			}
		}
	default:
		locs := make([]int, 0, len(nodes))
		for _, n := range nodes {
			locs = append(locs, n*Z)
		}
		iv := unionLeaves(L, Z, locs)
		u := 1.0 / float64(intervalsSize(iv))
		for _, x := range iv {
			for i := x.lo; i < x.hi; i++ {
				buf[i] = u
			}
		}
	}
}

// SecuritySnapshot は1時点の指標。
type SecuritySnapshot struct {
	// 共通祖先の深さ d (0..L, L は同一リーフ) の分布。H1: 同一ブロック, H0: 別ブロック
	H1, H0 [2][]float64 // [0]=一様にブロック選択, [1]=ワークロード分布
	TV     [2]float64   // 共通祖先の深さによる識別アドバンテージ
	TVLeaf [2]float64   // 同一リーフかどうかだけを見た場合
	// ブロックごとの候補リーフ数と非入れ子コピー数
	Cand      []int  // アドレスごと
	InStash   []bool // アドレスごと
	K         []int  // アドレスごと (スタッシュは -1)
	StashSize int
}

func (s *Sim) Security(weights []float64) SecuritySnapshot {
	s.obs.Update(s.srv.ReadHistory(observerID))
	o := s.obs
	L := s.cfg.L
	N := s.cfg.N
	leaves := 1 << L
	var snap SecuritySnapshot
	snap.Cand = make([]int, N)
	snap.InStash = make([]bool, N)
	snap.K = make([]int, N)
	// prefix[d][p]: 深さ d の接頭辞 p の質量。ブロックごとに計算し、H1/H0 の和を集める。
	wsets := [2][]float64{make([]float64, N), weights}
	for i := range wsets[0] {
		wsets[0][i] = 1.0 / float64(N)
	}
	var same1 [2][]float64 // Σ_b w_b Σ_p P_b(p)^2  (深さごと)
	var sq [2][]float64    // Σ_b w_b^2 Σ_p P_b(p)^2
	var mix [2][][]float64 // Σ_b w_b P_b(p)
	for t := 0; t < 2; t++ {
		same1[t] = make([]float64, L+1)
		sq[t] = make([]float64, L+1)
		mix[t] = make([][]float64, L+1)
		for d := 0; d <= L; d++ {
			mix[t][d] = make([]float64, 1<<d)
		}
	}
	buf := make([]float64, leaves)
	pref := make([][]float64, L+1)
	for d := 0; d <= L; d++ {
		pref[d] = make([]float64, 1<<d)
	}
	for a := 0; a < N; a++ {
		nodes, inStash := o.copyNodes(a)
		snap.InStash[a] = inStash
		if inStash {
			snap.K[a] = -1
			snap.StashSize++
		} else {
			snap.K[a] = nonNestedK(nodes)
		}
		locs := make([]int, 0, len(nodes)+1)
		if inStash {
			locs = append(locs, LocStash)
		}
		for _, n := range nodes {
			locs = append(locs, n*s.cfg.Z)
		}
		snap.Cand[a] = intervalsSize(unionLeaves(L, s.cfg.Z, locs))

		o.leafDist(a, buf)
		copy(pref[L], buf)
		for d := L - 1; d >= 0; d-- {
			for p := range pref[d] {
				pref[d][p] = pref[d+1][2*p] + pref[d+1][2*p+1]
			}
		}
		for d := 0; d <= L; d++ {
			ss := 0.0
			for _, v := range pref[d] {
				ss += v * v
			}
			for t := 0; t < 2; t++ {
				w := wsets[t][a]
				same1[t][d] += w * ss
				sq[t][d] += w * w * ss
				for p, v := range pref[d] {
					mix[t][d][p] += w * v
				}
			}
		}
	}
	for t := 0; t < 2; t++ {
		sumW2 := 0.0
		for _, w := range wsets[t] {
			sumW2 += w * w
		}
		ge1 := make([]float64, L+2) // P(LCA 深さ >= d)
		ge0 := make([]float64, L+2)
		for d := 0; d <= L; d++ {
			mm := 0.0
			for _, v := range mix[t][d] {
				mm += v * v
			}
			ge1[d] = same1[t][d]
			if s.cfg.Sigma > 0 {
				// Strong MVP-ORAM: 同じブロックを狙う2クライアントは別のタイムステップに分かれるので、
				// 同時に観測される2本は「実アクセス」と「一様なダミー」 → 共通祖先が深さ d 以上の確率は 2^-d
				ge1[d] = math.Pow(2, -float64(d))
			}
			ge0[d] = (mm - sq[t][d]) / (1 - sumW2)
		}
		snap.H1[t] = make([]float64, L+1)
		snap.H0[t] = make([]float64, L+1)
		tv := 0.0
		for d := 0; d <= L; d++ {
			snap.H1[t][d] = ge1[d] - ge1[d+1]
			snap.H0[t][d] = ge0[d] - ge0[d+1]
			tv += math.Abs(snap.H1[t][d] - snap.H0[t][d])
		}
		snap.TV[t] = tv / 2
		snap.TVLeaf[t] = math.Abs(ge1[L] - ge0[L])
	}
	return snap
}

func percentile(xs []int, p float64) int {
	if len(xs) == 0 {
		return 0
	}
	ys := append([]int(nil), xs...)
	sort.Ints(ys)
	i := int(p * float64(len(ys)-1))
	return ys[i]
}
