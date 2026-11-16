package main

// server.go は MVP-ORAM のサーバ (論文 Algorithm 2) を実装する。
//
// 論文では getPM 時に context[ci] ← oramState として「その時点の状態への参照」を保持する。
// ここでは木全体を複製する代わりに、各エントリに生成時刻 born と削除時刻 died を持たせる
// (永続データ構造)。クライアント ci のスナップショットは「getPM 時のサーバ時刻 t」だけで表せ、
// 時刻 t で見えるエントリは born <= t かつ (died == 0 || died > t) のもの。
// これにより getPM は O(1)、getPS / evict はパス長に比例するコストになる。

// TS はブロックのタイムスタンプ ⟨v, a, s⟩。
type TS struct{ V, A, S int }

// Greater は論文の比較規則 ⟨v,a,s⟩ > ⟨v',a',s'⟩。
func (x TS) Greater(y TS) bool {
	if x.V != y.V {
		return x.V > y.V
	}
	if x.A != y.A {
		return x.A > y.A
	}
	return x.S > y.S
}

var tsBottom = TS{-1, -1, -1}

const (
	LocStash   = -1 // ⊥ : スタッシュ
	LocDeleted = -2 // レプリカの削除 (CAPE のみ)
)

// Block は ⟨addr, data, ts⟩。Copy==0 が本体、Copy>0 がレプリカ (CAPE)。
type Block struct {
	Addr int
	Copy int
	Data int
	TS   TS
}

// LogEntry はパスマップ Ml の1要素 ⟨addr, sl, ts⟩ (+ レプリカID)。
type LogEntry struct {
	Addr int
	Copy int
	Loc  int
	TS   TS
}

type entry struct {
	b          Block
	born, died int
}

type stashVersion struct {
	blocks     []Block
	born, died int
}

// Server は単一の論理サーバ (BFT 複製はシミュレーションでは省略)。
type Server struct {
	L, Z    int
	slots   [][]entry // index = node*Z + j, node は 1 始まりのヒープ番号
	stashes []*stashVersion
	hist    []LogEntry // パスマップ履歴 HpathMaps (連結して保持)
	histOff int        // 圧縮で捨てた先頭要素数
	clock   int        // サーバ内部の論理時刻 (getPM / evict ごとに進む)
	nextSeq int
	ctx     map[int]int // context[ci] = getPM 時のサーバ時刻
	ctxHist map[int]int // getPM 時点の履歴長 (絶対位置)
	cursor  map[int]int // クライアントが読み終えた履歴位置 (絶対位置)
	Stats   ServerStats
}

type ServerStats struct {
	GetPMEntries int // 直近 getPM で返したログ件数
	GetPSBlocks  int // 直近 getPS で返したパス上ブロック(全版)
	GetPSStash   int // 直近 getPS で返したスタッシュブロック(全版)
}

func NewServer(L, Z int) *Server {
	nodes := 1 << (L + 1)
	return &Server{
		L: L, Z: Z,
		slots:   make([][]entry, nodes*Z),
		nextSeq: 1,
		ctx:     map[int]int{},
		ctxHist: map[int]int{},
		cursor:  map[int]int{},
	}
}

// PathSlots は leaf の root→leaf 順のスロット番号を返す。
func PathSlots(L, Z, leaf int) []int {
	out := make([]int, 0, (L+1)*Z)
	node := (1 << L) + leaf
	nodes := make([]int, L+1)
	for d := L; d >= 0; d-- {
		nodes[d] = node
		node >>= 1
	}
	for _, n := range nodes {
		for j := 0; j < Z; j++ {
			out = append(out, n*Z+j)
		}
	}
	return out
}

func visible(e entry, t int) bool { return e.born <= t && (e.died == 0 || e.died > t) }

// GetPM (Algorithm 2, L4-8)。履歴は前回からの差分だけ返す(consolidate は max マージなので等価)。
func (s *Server) GetPM(ci int) (seq int, diff []LogEntry) {
	seq = s.nextSeq
	s.nextSeq++
	s.clock++
	s.ctx[ci] = s.clock
	end := s.histOff + len(s.hist)
	s.ctxHist[ci] = end
	from := s.cursor[ci]
	if from < s.histOff {
		panic("path map history compacted beyond client cursor")
	}
	diff = append([]LogEntry(nil), s.hist[from-s.histOff:]...)
	s.cursor[ci] = end
	s.Stats.GetPMEntries = len(diff)
	return seq, diff
}

// GetPS (Algorithm 2, L9-11): context の状態から path と全スタッシュを返す。
func (s *Server) GetPS(ci int, leaf int) (path map[int][]Block, stashes [][]Block) {
	t, ok := s.ctx[ci]
	if !ok {
		panic("getPS without context")
	}
	path = make(map[int][]Block, (s.L+1)*s.Z)
	nb := 0
	for _, sl := range PathSlots(s.L, s.Z, leaf) {
		var bs []Block
		for _, e := range s.slots[sl] {
			if visible(e, t) {
				bs = append(bs, e.b)
			}
		}
		nb += len(bs)
		path[sl] = bs
	}
	ns := 0
	for _, sv := range s.stashes {
		if visible(entry{born: sv.born, died: sv.died}, t) {
			stashes = append(stashes, sv.blocks)
			ns += len(sv.blocks)
		}
	}
	s.Stats.GetPSBlocks = nb
	s.Stats.GetPSStash = ns
	return path, stashes
}

// Evict (Algorithm 2, L12-19)。
//
//	T*(l, sl) ← (Tc(l, sl) \ T(l, sl)) ∪ Pl*(sl)
//	S* ← (Sc \ S) ∪ {S}
//	H* ← H ∪ {Ml}
func (s *Server) Evict(ci int, leaf int, ml []LogEntry, newPath map[int]*Block, newStash []Block) {
	t, ok := s.ctx[ci]
	if !ok {
		panic("evict without context")
	}
	delete(s.ctx, ci)
	delete(s.ctxHist, ci)
	s.clock++
	now := s.clock
	for _, sl := range PathSlots(s.L, s.Z, leaf) {
		es := s.slots[sl]
		for i := range es {
			if es[i].died == 0 && es[i].born <= t {
				es[i].died = now // クライアントが読んだ版を置き換える
			}
		}
		if b := newPath[sl]; b != nil {
			es = append(es, entry{b: *b, born: now})
		}
		s.slots[sl] = s.gc(es)
	}
	for _, sv := range s.stashes {
		if sv.died == 0 && sv.born <= t {
			sv.died = now
		}
	}
	s.stashes = append(s.stashes, &stashVersion{blocks: append([]Block(nil), newStash...), born: now})
	s.gcStashes()
	s.hist = append(s.hist, ml...)
}

// minCtx は進行中アクセスのうち最も古いスナップショット時刻。進行中がなければ現在時刻。
func (s *Server) minCtx() int {
	m := s.clock
	for _, t := range s.ctx {
		if t < m {
			m = t
		}
	}
	return m
}

// gc は、どの進行中スナップショットからも見えない削除済みエントリを捨てる。
func (s *Server) gc(es []entry) []entry {
	m := s.minCtx()
	out := es[:0]
	for _, e := range es {
		if e.died != 0 && e.died <= m {
			continue
		}
		out = append(out, e)
	}
	return out
}

func (s *Server) gcStashes() {
	m := s.minCtx()
	out := s.stashes[:0]
	for _, sv := range s.stashes {
		if sv.died != 0 && sv.died <= m {
			continue
		}
		out = append(out, sv)
	}
	s.stashes = out
}

// CompactHistory は全クライアント(観測者を含む)が読み終えた履歴を捨てる
// (論文脚注3の「γ アクセスごとに統合済み position map を送り古い path map を消す」に相当)。
func (s *Server) CompactHistory() {
	if len(s.cursor) == 0 {
		return
	}
	m := s.histOff + len(s.hist)
	for _, c := range s.cursor {
		if c < m {
			m = c
		}
	}
	drop := m - s.histOff
	if drop <= 0 {
		return
	}
	s.hist = append([]LogEntry(nil), s.hist[drop:]...)
	s.histOff = m
}

// RegisterReader は観測者などの読み手の履歴カーソルを登録する。
func (s *Server) RegisterReader(id int) { s.cursor[id] = s.histOff }

// ReadHistory は観測者用: getPM と違い seq や context を作らない。
func (s *Server) ReadHistory(id int) []LogEntry {
	from := s.cursor[id]
	diff := append([]LogEntry(nil), s.hist[from-s.histOff:]...)
	s.cursor[id] = s.histOff + len(s.hist)
	return diff
}

// --- 観測用(サーバ状態の全体像) ---

// AliveSlots は現在の木の各スロットの生きているエントリ。
func (s *Server) AliveSlot(sl int) []Block {
	var out []Block
	for _, e := range s.slots[sl] {
		if e.died == 0 {
			out = append(out, e.b)
		}
	}
	return out
}

func (s *Server) AliveStashes() [][]Block {
	var out [][]Block
	for _, sv := range s.stashes {
		if sv.died == 0 {
			out = append(out, sv.blocks)
		}
	}
	return out
}
