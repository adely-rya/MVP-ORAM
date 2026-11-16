package main

// client.go は MVP-ORAM のクライアント (論文 Algorithm 1, 3) と、その上に載せる
// CAPE のレプリカ (いつ捨ててもよいキャッシュ) を実装する。
//
// レプリカなし (Config.Replicas == ReplicaNone, PackUp == false) のとき、
// 処理は Algorithm 1 / 3 と一致する。

import (
	"math/rand"
	"sort"
)

type ReplicaStrategy int

const (
	ReplicaNone     ReplicaStrategy = iota
	ReplicaFewest                   // 候補リーフ数が最も少ないアドレスから複製 (既存 CAPE と同じ方針)
	ReplicaHot                      // 最近アクセスされた (ts.a が大きい) アドレスから複製
	ReplicaShallow                  // 空きスロットが浅いときだけ、候補リーフ数が最少のアドレスを複製
	ReplicaStashHot                 // スタッシュにいる(=今のパス上にいない)ブロックだけを、a が大きい順に複製
)

type LeafRule int

const (
	LeafUnionUniform LeafRule = iota // 全コピーの候補リーフの和集合から一様
	LeafCopyUniform                  // コピーを一様に選び、その部分木から一様
)

type Config struct {
	L, Z, N   int
	Replicas  ReplicaStrategy
	RMax      int  // 1アドレスあたりのレプリカ数上限
	PackUp    bool // 対照方式: 本体をパス上の空きスロットへ上に詰める
	LeafRule  LeafRule
	MinDepth  int  // ReplicaShallow 用: この深さ以下 (root=0) のスロットにだけ作る
	NoSelfRep bool // アクセス対象ブロックはその回のパスに複製しない (既定 true)
	EvictCold bool // 工夫: スタッシュから木へ戻すブロックを a の小さい順に選ぶ (論文はランダム)
	Sigma     int  // Strong MVP-ORAM: 実アクセス1回につき σ 回のダミーアクセス
	// 公開実装 (github.com/rvassantlal/MVPORAM) 互換の設定
	ReorderOfficial bool // a 昇順で root 側から、埋まっているスロットだけ並べ替え
	EmptyStart      bool // ORAM を空で開始 (書き込みで初めてブロックが生まれる)
	FixedEvictOrder bool // evict の順番を 0..c-1 に固定
}

type pmEntry struct {
	Loc int
	TS  TS
}

type Client struct {
	ID   int
	cfg  *Config
	rng  *rand.Rand
	prim []pmEntry         // 本体の位置
	reps []map[int]pmEntry // レプリカの位置 (Copy ID → entry)
	seq  int
	next int // レプリカ ID 採番
	Last AccessTrace
}

func NewClient(id int, cfg *Config, initPM []pmEntry, seed int64) *Client {
	c := &Client{ID: id, cfg: cfg, rng: rand.New(rand.NewSource(seed))}
	c.prim = append([]pmEntry(nil), initPM...)
	c.reps = make([]map[int]pmEntry, cfg.N)
	return c
}

// Consolidate (Algorithm 3, L1-7) を差分で適用する。レプリカは (addr, copy) ごとに最大 ts を残し、
// 本体より古い版 (V が小さい) や削除済みのものは捨てる。
func (c *Client) Consolidate(diff []LogEntry) {
	consolidateInto(c.prim, c.reps, diff)
}

func consolidateInto(prim []pmEntry, reps []map[int]pmEntry, diff []LogEntry) {
	for _, e := range diff {
		if e.Copy == 0 {
			if e.TS.Greater(prim[e.Addr].TS) {
				prim[e.Addr] = pmEntry{e.Loc, e.TS}
			}
			continue
		}
		m := reps[e.Addr]
		if m == nil {
			m = map[int]pmEntry{}
			reps[e.Addr] = m
		}
		cur, ok := m[e.Copy]
		if !ok || e.TS.Greater(cur.TS) {
			m[e.Copy] = pmEntry{e.Loc, e.TS}
		}
	}
	for _, e := range diff {
		if e.Copy == 0 && reps[e.Addr] == nil {
			continue
		}
		pruneReplicas(prim, reps, e.Addr)
	}
}

func pruneReplicas(prim []pmEntry, reps []map[int]pmEntry, addr int) {
	m := reps[addr]
	for id, r := range m {
		if r.Loc == LocDeleted || r.TS.V != prim[addr].TS.V {
			delete(m, id)
		}
	}
	if len(m) == 0 {
		reps[addr] = nil
	}
}

// --- 位置・候補リーフ ---

func slotNode(Z, sl int) int { return sl / Z }

func nodeDepth(node int) int {
	d := -1
	for node > 0 {
		node >>= 1
		d++
	}
	return d
}

// leafRange はノードの部分木に含まれるリーフ区間 [lo, hi)。
func leafRange(L, node int) (int, int) {
	d := nodeDepth(node)
	lo := (node << (L - d)) - (1 << L)
	return lo, lo + (1 << (L - d))
}

// copyLocs はアドレスの有効なコピー位置 (本体を先頭に)。LocStash を含みうる。
func copyLocs(prim []pmEntry, reps []map[int]pmEntry, addr int) []int {
	locs := []int{prim[addr].Loc}
	for _, r := range reps[addr] {
		if r.Loc >= 0 && r.TS.V == prim[addr].TS.V {
			locs = append(locs, r.Loc)
		}
	}
	return locs
}

type interval struct{ lo, hi int }

func unionLeaves(L, Z int, locs []int) []interval {
	iv := make([]interval, 0, len(locs))
	for _, loc := range locs {
		if loc < 0 {
			return []interval{{0, 1 << L}}
		}
		lo, hi := leafRange(L, slotNode(Z, loc))
		iv = append(iv, interval{lo, hi})
	}
	sort.Slice(iv, func(i, j int) bool { return iv[i].lo < iv[j].lo })
	out := iv[:0:0]
	for _, x := range iv {
		if len(out) > 0 && x.lo <= out[len(out)-1].hi {
			if x.hi > out[len(out)-1].hi {
				out[len(out)-1].hi = x.hi
			}
			continue
		}
		out = append(out, x)
	}
	return out
}

func intervalsSize(iv []interval) int {
	n := 0
	for _, x := range iv {
		n += x.hi - x.lo
	}
	return n
}

// chooseLeaf は Algorithm 1 L4-5 (「sl を通るランダムなパス」) をコピーへ拡張したもの。
// 戻り値: leaf と、そのパス上でアクセスに使うコピーの位置 (本体なら Copy=0)。
func (c *Client) chooseLeaf(addr int) (leaf int, viaCopy int, viaLoc int) {
	L, Z := c.cfg.L, c.cfg.Z
	type cp struct{ id, loc int }
	copies := []cp{{0, c.prim[addr].Loc}}
	for id, r := range c.reps[addr] {
		if r.Loc >= 0 && r.TS.V == c.prim[addr].TS.V {
			copies = append(copies, cp{id, r.Loc})
		}
	}
	sort.Slice(copies[1:], func(i, j int) bool { return copies[1+i].id < copies[1+j].id })
	contains := func(loc, leaf int) bool {
		if loc < 0 {
			return true
		}
		lo, hi := leafRange(L, slotNode(Z, loc))
		return leaf >= lo && leaf < hi
	}
	switch c.cfg.LeafRule {
	case LeafCopyUniform:
		k := copies[c.rng.Intn(len(copies))]
		if k.loc < 0 {
			leaf = c.rng.Intn(1 << L)
		} else {
			lo, hi := leafRange(L, slotNode(Z, k.loc))
			leaf = lo + c.rng.Intn(hi-lo)
		}
	default:
		locs := make([]int, len(copies))
		for i, k := range copies {
			locs[i] = k.loc
		}
		iv := unionLeaves(L, Z, locs)
		r := c.rng.Intn(intervalsSize(iv))
		for _, x := range iv {
			if r < x.hi-x.lo {
				leaf = x.lo + r
				break
			}
			r -= x.hi - x.lo
		}
	}
	// そのリーフのパス上にあるコピーのうち、本体を優先して使う
	for _, k := range copies {
		if contains(k.loc, leaf) {
			return leaf, k.id, k.loc
		}
	}
	panic("no copy on chosen leaf")
}

// --- アクセス (Algorithm 1) ---

type Op struct {
	Write bool
	Addr  int
	Data  int
	Dummy bool // Strong MVP-ORAM のダミーアクセス (ランダムなリーフを読んで退避だけ行う)
}

// AccessTrace はスタッシュの増減とレプリカの動きを記録する。
type AccessTrace struct {
	Leaf, ViaCopy           int
	SZChosen, SZEmpty       int // 交換に選んだ Z スロットと、そのうち本体がいなかった数
	SZHadReplica            int // SZEmpty のうちレプリカが入っていた数
	InStashSwapped          int // 交換で押し出されスタッシュへ入った本体 (アクセス対象を除く)
	InStashCollision        int // スロット衝突で負けてスタッシュに入った本体
	InStashTarget           int // アクセス対象がパスから来てスタッシュに入った
	OutStashToPath          int // スタッシュ由来で木へ出た本体
	StashBefore, StashAfter int // W のスタッシュ由来本体数 / 新スタッシュ長
	RepKept, RepDropped     int
	RepCreated              int
	MlLen                   int
	Data                    int // 読み出した値
}

// Prepare は getPM 後の処理 (consolidate + パス選択)。
func (c *Client) Prepare(seq int, diff []LogEntry, op Op) (leaf int) {
	c.seq = seq
	c.Consolidate(diff)
	c.Last = AccessTrace{}
	if op.Dummy {
		leaf = c.rng.Intn(1 << c.cfg.L)
		c.Last.Leaf = leaf
		return leaf
	}
	leaf, via, _ := c.chooseLeaf(op.Addr)
	c.Last.Leaf, c.Last.ViaCopy = leaf, via
	return leaf
}

// Finish は getPS の結果から W を作り、populatePath した結果を返す (Algorithm 1 L7-13)。
func (c *Client) Finish(op Op, path map[int][]Block, stashes [][]Block) (ml []LogEntry, newPath map[int]*Block, newStash []Block) {
	L, Z := c.cfg.L, c.cfg.Z
	leaf := c.Last.Leaf
	pathSlots := PathSlots(L, Z, leaf)
	onPath := make(map[int]bool, len(pathSlots))
	for _, sl := range pathSlots {
		onPath[sl] = true
	}

	// mergePathStashes (Algorithm 3, L8-11)。重複は addr で除去。
	W := map[int]Block{}
	fromStash := map[int]bool{}
	for _, st := range stashes {
		for _, b := range st {
			if b.Copy == 0 && c.prim[b.Addr].Loc == LocStash && c.prim[b.Addr].TS == b.TS {
				W[b.Addr] = b
				fromStash[b.Addr] = true
			}
		}
	}
	type repAt struct {
		b  Block
		sl int
	}
	var repsOnPath []repAt
	for _, sl := range pathSlots {
		for _, b := range path[sl] {
			if b.Copy == 0 {
				if c.prim[b.Addr].Loc == sl && c.prim[b.Addr].TS == b.TS {
					W[b.Addr] = b
				}
				continue
			}
			r, ok := c.reps[b.Addr][b.Copy]
			if ok && r.Loc == sl && r.TS == b.TS && b.TS.V == c.prim[b.Addr].TS.V {
				repsOnPath = append(repsOnPath, repAt{b, sl})
			}
		}
	}
	c.Last.StashBefore = len(fromStash)
	if op.Dummy {
		return c.populatePath(W, fromStash, repsOnPathSlots(repsOnPath, func(r repAt) (Block, int) { return r.b, r.sl }), pathSlots, onPath, -1, -1)
	}

	// アクセス対象 (Algorithm 1 L8-12)。レプリカ経由なら、レプリカの内容から本体を作り直す
	// (本体は必ずスタッシュへ行くので、元の本体は古い版として無効化される)。
	target, ok := W[op.Addr]
	if !ok {
		for _, r := range repsOnPath {
			if r.b.Addr == op.Addr && r.b.Copy == c.Last.ViaCopy {
				target = Block{Addr: op.Addr, Copy: 0, Data: r.b.Data, TS: r.b.TS}
				ok = true
				break
			}
		}
	}
	if !ok && c.prim[op.Addr].TS == tsBottom {
		// 一度も書かれていないアドレス (公開実装の「空の ORAM から開始」)
		if !op.Write {
			c.Last.Data = 0
			return c.populatePath(W, fromStash, repsOnPathSlots(repsOnPath, func(r repAt) (Block, int) { return r.b, r.sl }), pathSlots, onPath, -1, -1)
		}
		target = Block{Addr: op.Addr}
		ok = true
	}
	if !ok {
		panic("target block not found in working set")
	}
	c.Last.Data = target.Data
	if op.Write {
		target.Data = op.Data
		target.TS = TS{c.seq, c.seq, c.seq}
	} else {
		target.TS = TS{target.TS.V, c.seq, c.seq}
	}
	W[op.Addr] = target

	accessedRepSlot := -1
	if c.Last.ViaCopy != 0 {
		for _, r := range repsOnPath {
			if r.b.Addr == op.Addr && r.b.Copy == c.Last.ViaCopy {
				accessedRepSlot = r.sl
			}
		}
	}
	return c.populatePath(W, fromStash, repsOnPathSlots(repsOnPath, func(r repAt) (Block, int) { return r.b, r.sl }), pathSlots, onPath, op.Addr, accessedRepSlot)
}

type placedRep struct {
	b  Block
	sl int
}

func repsOnPathSlots[T any](xs []T, f func(T) (Block, int)) []placedRep {
	out := make([]placedRep, len(xs))
	for i, x := range xs {
		b, sl := f(x)
		out[i] = placedRep{b, sl}
	}
	return out
}

// populatePath (Algorithm 3, L12-39) + CAPE のレプリカ処理。
func (c *Client) populatePath(W map[int]Block, fromStash map[int]bool, repsOnPath []placedRep,
	pathSlots []int, onPath map[int]bool, addr int, accessedRepSlot int) ([]LogEntry, map[int]*Block, []Block) {

	Z := c.cfg.Z
	seq := c.seq
	P := make(map[int]*Block, len(pathSlots))
	var ml []LogEntry
	used := map[int]bool{}
	targetSlot := LocStash // ⟨sl, ⟩ ← pm[addr] (ダミーなら ⊥)
	if addr >= 0 {
		targetSlot = c.prim[addr].Loc
	}

	// L15-20: 本体を pm の位置へ。衝突時は s が最大のものを置き、残りは W に残す。
	collided := map[int]bool{}
	bySlot := map[int][]int{}
	for a := range W {
		if loc := c.prim[a].Loc; loc >= 0 && onPath[loc] {
			bySlot[loc] = append(bySlot[loc], a)
		}
	}
	for _, sl := range pathSlots {
		cands := bySlot[sl]
		if len(cands) == 0 {
			continue
		}
		sort.Ints(cands)
		best := cands[0]
		for _, a := range cands[1:] {
			if W[a].TS.S > W[best].TS.S || (W[a].TS.S == W[best].TS.S && W[a].TS.Greater(W[best].TS)) {
				best = a
			}
		}
		for _, a := range cands {
			if a != best {
				collided[a] = true
			}
		}
		b := W[best]
		P[sl] = &b
		delete(W, best)
		used[sl] = true
	}

	// L21: SZ ← Z random slots from Pl* (アクセス対象の位置を含む)。
	// CAPE: レプリカ経由で読んだときは、そのレプリカのスロットも含める。
	forced := []int{}
	if targetSlot >= 0 && onPath[targetSlot] {
		forced = append(forced, targetSlot)
	}
	if accessedRepSlot >= 0 && accessedRepSlot != targetSlot {
		forced = append(forced, accessedRepSlot)
	}
	SZ := sampleSlots(c.rng, pathSlots, Z, forced)
	repSlot := map[int]bool{}
	for _, r := range repsOnPath {
		repSlot[r.sl] = true
	}
	// L22: BZ ← Z random blocks from W \ {addr}
	var pool []int
	for a := range W {
		if a != addr {
			pool = append(pool, a)
		}
	}
	sort.Ints(pool)
	c.rng.Shuffle(len(pool), func(i, j int) { pool[i], pool[j] = pool[j], pool[i] })
	if c.cfg.EvictCold {
		// 工夫: アクセスの古い (a が小さい) ブロックから木へ戻し、人気のブロックをスタッシュ(=全パスが候補)に残す
		sort.SliceStable(pool, func(i, j int) bool { return W[pool[i]].TS.A < W[pool[j]].TS.A })
	}
	if len(pool) > Z {
		pool = pool[:Z]
	}
	// L23-25: 交換
	c.Last.SZChosen = len(SZ)
	for i, sl := range SZ {
		if P[sl] != nil {
			b := *P[sl]
			W[b.Addr] = b
			if b.Addr != addr {
				c.Last.InStashSwapped++
			}
		} else {
			c.Last.SZEmpty++
			if repSlot[sl] {
				c.Last.SZHadReplica++
			}
		}
		P[sl] = nil
		if i < len(pool) {
			b := W[pool[i]]
			delete(W, pool[i])
			P[sl] = &b
			if fromStash[b.Addr] {
				c.Last.OutStashToPath++
			}
		}
	}

	// L26-31: 並べ替え。a が大きいブロックほど root 側へ。
	var Bl []Block
	for _, sl := range pathSlots {
		if P[sl] != nil {
			Bl = append(Bl, *P[sl])
		}
	}
	sort.SliceStable(Bl, func(i, j int) bool {
		if Bl[i].TS.A != Bl[j].TS.A {
			if c.cfg.ReorderOfficial {
				return Bl[i].TS.A < Bl[j].TS.A // 公開実装: a の小さい(古い)ブロックを root 側へ
			}
			return Bl[i].TS.A > Bl[j].TS.A
		}
		return Bl[i].Addr < Bl[j].Addr
	})
	var order []int // sort(Sused ∪ SZ), root 側から
	inSZ := map[int]bool{}
	for _, sl := range SZ {
		inSZ[sl] = true
	}
	for _, sl := range pathSlots { // pathSlots は root→leaf 順
		if used[sl] || inSZ[sl] || (c.cfg.PackUp && !repHeld(sl, repsOnPath)) {
			order = append(order, sl)
		}
	}
	if c.cfg.PackUp {
		// 対照方式: 空きスロットも含めて root 側から詰める (レプリカは使わない前提)
		order = order[:0]
		order = append(order, pathSlots...)
	}
	if c.cfg.ReorderOfficial {
		// 公開実装: 埋まっているスロットの位置は変えず、中身だけを並べ替える
		order = order[:0]
		for _, sl := range pathSlots {
			if P[sl] != nil {
				order = append(order, sl)
			}
		}
	}
	for _, sl := range pathSlots {
		P[sl] = nil
	}
	for i, sl := range order {
		if i >= len(Bl) {
			break
		}
		b := Bl[i]
		b.TS.S = seq
		P[sl] = &b
		ml = append(ml, LogEntry{b.Addr, 0, sl, b.TS})
	}

	// L32-38: 新しいスタッシュ
	var S []Block
	keys := make([]int, 0, len(W))
	for a := range W {
		keys = append(keys, a)
	}
	sort.Ints(keys)
	for _, a := range keys {
		b := W[a]
		if c.prim[a].Loc != LocStash || a == addr {
			b.TS.S = seq
			ml = append(ml, LogEntry{a, 0, LocStash, b.TS})
			if a == addr && !fromStash[a] {
				c.Last.InStashTarget++
			} else if collided[a] {
				c.Last.InStashCollision++
			}
		}
		S = append(S, b)
	}
	c.Last.StashAfter = len(S)

	// --- CAPE: レプリカ (本体の配置が確定した後) ---
	if c.cfg.Replicas != ReplicaNone {
		ml = c.placeReplicas(P, S, repsOnPath, pathSlots, addr, accessedRepSlot, ml)
	} else {
		for _, r := range repsOnPath { // 念のため (レプリカ無効時は存在しない)
			ml = append(ml, LogEntry{r.b.Addr, r.b.Copy, LocDeleted, TS{r.b.TS.V, r.b.TS.A, seq}})
		}
	}
	c.Last.MlLen = len(ml)
	return ml, P, S
}

func repHeld(sl int, reps []placedRep) bool {
	for _, r := range reps {
		if r.sl == sl {
			return true
		}
	}
	return false
}

func sampleSlots(rng *rand.Rand, slots []int, z int, forced []int) []int {
	out := append([]int(nil), forced...)
	seen := map[int]bool{}
	for _, s := range forced {
		seen[s] = true
	}
	for _, i := range rng.Perm(len(slots)) {
		if len(out) >= z {
			break
		}
		if !seen[slots[i]] {
			seen[slots[i]] = true
			out = append(out, slots[i])
		}
	}
	return out
}

// placeReplicas: レプリカは本体の動きに影響しない。
//   - 本体が入ったスロットのレプリカ、アクセスに使ったレプリカは削除 (ログに Delete を残す)
//   - 残りのレプリカはそのまま残す (ログ不要)
//   - 残った空きスロットにだけ新しいレプリカを作る (r_max まで)
//   - レプリカはスタッシュには入れない
func (c *Client) placeReplicas(P map[int]*Block, S []Block, repsOnPath []placedRep, pathSlots []int,
	addr int, accessedRepSlot int, ml []LogEntry) []LogEntry {

	L, Z := c.cfg.L, c.cfg.Z
	seq := c.seq
	// 仮想 position map: ここまでのログを反映した上でレプリカ数・候補を数える
	type repInfo struct{ loc int }
	live := map[int][]int{} // addr → 有効コピー位置 (本体含む)
	for _, r := range repsOnPath {
		if P[r.sl] != nil || r.sl == accessedRepSlot {
			ml = append(ml, LogEntry{r.b.Addr, r.b.Copy, LocDeleted, TS{r.b.TS.V, r.b.TS.A, seq}})
			c.Last.RepDropped++
			continue
		}
		b := r.b
		P[r.sl] = &b
		c.Last.RepKept++
	}
	if c.cfg.RMax <= 0 {
		return ml
	}
	// 手元にある最新版のブロック (パス上の本体 + 新スタッシュ)
	src := map[int]Block{}
	for _, sl := range pathSlots {
		if b := P[sl]; b != nil && b.Copy == 0 {
			src[b.Addr] = *b
		}
	}
	for _, b := range S {
		src[b.Addr] = b
	}
	if c.cfg.Replicas == ReplicaStashHot {
		// パス上の本体のコピーを同じパスに置いても入れ子になる(上へ移動したのと同じ)ので、
		// スタッシュのブロックだけを複製元にする。
		src = map[int]Block{}
		for _, b := range S {
			src[b.Addr] = b
		}
	}
	if c.cfg.NoSelfRep {
		delete(src, addr)
	}
	if len(src) == 0 {
		return ml
	}
	// 現在のコピー位置 (このアクセスでの移動・削除を反映)
	moved := map[int]int{}
	deleted := map[[2]int]bool{}
	for _, e := range ml {
		if e.Copy == 0 {
			moved[e.Addr] = e.Loc
		} else if e.Loc == LocDeleted {
			deleted[[2]int{e.Addr, e.Copy}] = true
		}
	}
	nRep := map[int]int{}
	for a := range src {
		loc := c.prim[a].Loc
		if m, ok := moved[a]; ok {
			loc = m
		}
		locs := []int{loc}
		for id, r := range c.reps[a] {
			if r.Loc >= 0 && r.TS.V == c.prim[a].TS.V && !deleted[[2]int{a, id}] {
				locs = append(locs, r.Loc)
				nRep[a]++
			}
		}
		live[a] = locs
	}
	addrs := make([]int, 0, len(src))
	for a := range src {
		addrs = append(addrs, a)
	}
	sort.Ints(addrs)

	for _, sl := range pathSlots { // root 側の空きから
		if P[sl] != nil {
			continue
		}
		depth := nodeDepth(slotNode(Z, sl))
		if c.cfg.Replicas == ReplicaShallow && depth > c.cfg.MinDepth {
			break
		}
		best, bestScore := -1, 0
		for _, a := range addrs {
			if nRep[a] >= c.cfg.RMax {
				continue
			}
			base := live[a]
			if c.cfg.Replicas == ReplicaStashHot {
				// スタッシュ位置は「いずれ木へ戻る」ので、木の中のコピーだけで増分を測る
				base = treeOnly(base)
			}
			cur := intervalsSize(unionLeaves(L, Z, base))
			gain := intervalsSize(unionLeaves(L, Z, append(append([]int(nil), base...), sl))) - cur
			if gain <= 0 {
				continue // 候補リーフが増えない場所 (既存コピーの部分木の内側) には置かない
			}
			var score int
			switch c.cfg.Replicas {
			case ReplicaHot, ReplicaStashHot:
				score = src[a].TS.A
			default: // Fewest / Shallow: 候補リーフが少ないものを優先
				score = -cur
			}
			if best < 0 || score > bestScore {
				best, bestScore = a, score
			}
		}
		if best < 0 {
			continue
		}
		c.next++
		id := seq*1024 + c.next%1024
		b := src[best]
		b.Copy = id
		b.TS.S = seq
		P[sl] = &b
		ml = append(ml, LogEntry{best, id, sl, b.TS})
		live[best] = append(live[best], sl)
		nRep[best]++
		c.Last.RepCreated++
	}
	return ml
}

func treeOnly(locs []int) []int {
	out := make([]int, 0, len(locs))
	for _, l := range locs {
		if l >= 0 {
			out = append(out, l)
		}
	}
	return out
}
