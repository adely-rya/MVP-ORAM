package main

// stash_trace.go は、スタッシュ増加の原因を調べるための長時間計測(実験A)を実装する。
//
// 起動例:
//   go run . -experimentmode=stash-trace -oram=re-mvp-oram
//   STASH_TRACE_ACCESSES=105000 STASH_TRACE_READ_RATIO=0.95 go run . -experimentmode=stash-trace -oram=mvp-oram
//
// 1 ラウンド = 全クライアントが GetPM → GetPS → Evict を同時に行う(既存の sync モードと同じ並列度)。
// アクセスごとの内訳を集計し、ラウンドごとにサーバ状態(木・スタッシュ)を観測者の position map で検証して CSV に出す。

import (
	"encoding/csv"
	"fmt"
	"log"
	"math/rand"
	"os"
	"path/filepath"
	"strconv"
	"sync"
	"time"
)

const stashTraceObserverID = -1000

// ---------------------------------------------------------------------------
// CAPE(re-mvp-oram) の populatePath 内で記録する内訳

type capeEvictTrace struct {
	PathSlots int // 読んだパスの全スロット数 (L+1)*Z

	// 入力パスの状態(クライアントの position map で有効と判定できるブロック)
	InSlotsPrimary   int // 有効な本体(sig0)を含むスロット
	InSlotsReplica   int // 有効なレプリカ(sig!=0)のみを含むスロット
	InSlotsCollision int // 有効ブロックが2個以上入っているスロット(版の衝突)

	// Phase5(本体・アクセス対象を元のスロットに残す)後
	InPlace          int // 元の位置に残ったブロック数
	Unused           int // 空きとして扱われたスロット数(=スタッシュ排水に使える容量)
	UnusedWasReplica int // そのうち入力時に有効レプリカが入っていたスロット
	UnusedWasEmpty   int // そのうち入力時に空(または無効ブロックのみ)だったスロット
	UnusedWasPrimary int // そのうち入力時に有効本体がいたが衝突で負けたスロット

	// Phase5 で元スロットに戻れなかった priority ブロック(=空きスロットかスタッシュへ行く)
	PendingFromStashPrimary int
	PendingFromStashReplica int
	PendingCollisionPrimary int // パス上にいたが衝突で負けた本体
	PendingCollisionReplica int // パス上にいたが衝突で負けたレプリカ(アクセス対象として priority 扱い)

	// 最終的にスタッシュに残ったもの(流入の内訳)
	StashOutRetainedPrimary  int // 元からスタッシュにいた本体
	StashOutRetainedReplica  int // 元からスタッシュにいたレプリカ
	StashOutCollisionPrimary int // 衝突で負けてスタッシュに入った本体
	StashOutCollisionReplica int // 衝突で負けてスタッシュに入ったレプリカ
	DedupDeleted             int // 同一アドレス2個目以降として Delete されたブロック
	DedupDeletedSameKey      int // そのうち残したブロックと (addr,sig) が同じもの(=PM 上で消える)
	DedupDeletedPrimary      int // そのうち sig0

	CopiesCreated   int
	EmptyAfterEvict int
}

func validBlocksInSlot(c *MvpClient, bucketPosition MvpBucketPosition, slotPosition MvpSlotPosition) (primary int, replica int) {
	bucket, ok := c.path[bucketPosition]
	if !ok {
		return 0, 0
	}
	position := MvpPosition{bucket: bucketPosition, slot: slotPosition}
	for _, slot := range bucket.Slots[slotPosition] {
		if slot.IsEmpty() {
			continue
		}
		block := slot.Value
		pm, ok := c.PositionMap[block.Addr][block.signature]
		if !ok || pm.Slot != position || !sameDataVersion(pm.Ts, block.Version) {
			continue
		}
		if block.signature == 0 {
			primary++
		} else {
			replica++
		}
	}
	return primary, replica
}

func (t *capeEvictTrace) recordAfterPlaceInPlace(c *MvpClient, usedSlot []MvpPosition, unusedSlot []MvpPosition, pending []MvpDataBlock) {
	t.PathSlots = len(usedSlot) + len(unusedSlot)
	for bucketPosition := range c.path {
		for i := 0; i < c.Z; i++ {
			p, r := validBlocksInSlot(c, bucketPosition, MvpSlotPosition(i))
			if p > 0 {
				t.InSlotsPrimary++
			} else if r > 0 {
				t.InSlotsReplica++
			}
			if p+r >= 2 {
				t.InSlotsCollision++
			}
		}
	}
	t.InPlace = len(usedSlot)
	t.Unused = len(unusedSlot)
	for _, position := range unusedSlot {
		p, r := validBlocksInSlot(c, position.bucket, position.slot)
		switch {
		case p > 0:
			t.UnusedWasPrimary++
		case r > 0:
			t.UnusedWasReplica++
		default:
			t.UnusedWasEmpty++
		}
	}
	for _, block := range pending {
		fromStash := c.PositionMap[block.Addr][block.signature].Slot == mvpStashPosition
		switch {
		case fromStash && block.signature == 0:
			t.PendingFromStashPrimary++
		case fromStash:
			t.PendingFromStashReplica++
		case block.signature == 0:
			t.PendingCollisionPrimary++
		default:
			t.PendingCollisionReplica++
		}
	}
}

func (t *capeEvictTrace) recordLeftover(c *MvpClient, leftover map[int][]MvpDataBlock) {
	for _, blocks := range leftover {
		if len(blocks) == 0 {
			continue
		}
		kept := blocks[0]
		fromStash := c.PositionMap[kept.Addr][kept.signature].Slot == mvpStashPosition
		switch {
		case fromStash && kept.signature == 0:
			t.StashOutRetainedPrimary++
		case fromStash:
			t.StashOutRetainedReplica++
		case kept.signature == 0:
			t.StashOutCollisionPrimary++
		default:
			t.StashOutCollisionReplica++
		}
		for _, block := range blocks[1:] {
			t.DedupDeleted++
			if block.signature == kept.signature {
				t.DedupDeletedSameKey++
			}
			if block.signature == 0 {
				t.DedupDeletedPrimary++
			}
		}
	}
}

// ---------------------------------------------------------------------------
// サーバ状態の観測(シーケンス番号を進めない、スナップショットも取らない)

type capeTraceStateRequest struct {
	Reply chan capeTraceStateResponse
}

type capeTraceStateResponse struct {
	Seq      Version
	PathMaps []path
	Tree     MvpTree
	Stashs   map[int][]MvpDataBlock
}

func (r capeTraceStateRequest) handle(s *MvpServer) {
	cursor := s.PathMapCursor[stashTraceObserverID]
	if cursor < 0 || cursor > len(s.PathMaps) {
		cursor = len(s.PathMaps)
	}
	diff := append([]path(nil), s.PathMaps[cursor:]...)
	s.PathMapCursor[stashTraceObserverID] = len(s.PathMaps)
	r.Reply <- capeTraceStateResponse{
		Seq:      s.counter,
		PathMaps: diff,
		Tree:     s.tree.Clone(),
		Stashs:   cloneStashs(s.Stashs),
	}
}

type baseTraceStateRequest struct {
	Reply chan baseTraceStateResponse
}

type baseTraceStateResponse struct {
	Seq      Version
	PathMaps []basePath
	Tree     BaseMvpTree
	Stashs   map[int][]BaseMvpDataBlock
}

func (r baseTraceStateRequest) handle(s *BaseMvpServer) {
	cursor := s.PathMapCursor[stashTraceObserverID]
	if cursor < 0 || cursor > len(s.PathMaps) {
		cursor = len(s.PathMaps)
	}
	diff := append([]basePath(nil), s.PathMaps[cursor:]...)
	s.PathMapCursor[stashTraceObserverID] = len(s.PathMaps)
	r.Reply <- baseTraceStateResponse{
		Seq:      s.counter,
		PathMaps: diff,
		Tree:     s.tree.Clone(),
		Stashs:   cloneBaseMvpStashs(s.Stashs),
	}
}

// globalState はラウンド終了時点のサーバ状態を、全 PathMap を反映した position map で検証した結果。
type globalState struct {
	Seq             Version
	TreePrimary     int // 木の中の有効な本体
	TreeReplica     int // 木の中の有効なレプリカ
	TreeOccupied    int // 何らかのブロック(無効含む)が入っている物理スロット
	TotalSlots      int
	StashPrimary    int // 有効な本体(重複除去後)
	StashReplica    int // 有効なレプリカ(重複除去後)
	StashRaw        int // サーバが保持するスタッシュ全版のブロック総数(重複・無効含む)
	StashVersions   int
	LostAddrs       int // 有効なコピーが1つもないアドレス数
	NoPrimaryAddrs  int // sig0 が Delete/無効になっているアドレス数
	MaxValidPerAddr int
}

func observeCape(server chan<- ServerRequest, observer *MvpClient, addrCount int) globalState {
	reply := make(chan capeTraceStateResponse)
	server <- capeTraceStateRequest{Reply: reply}
	res := <-reply
	observer.consolidatePathMaps(res.PathMaps)
	pm := observer.PositionMap

	st := globalState{Seq: res.Seq}
	validKeys := make(map[pathKey]struct{})
	for bucketPosition, bucket := range res.Tree.Tree {
		for slotPosition, versioned := range bucket.Slots {
			st.TotalSlots++
			occupied := false
			for _, slot := range versioned {
				if slot.IsEmpty() {
					continue
				}
				occupied = true
				block := slot.Value
				entry, ok := pm[block.Addr][block.signature]
				position := MvpPosition{bucket: bucketPosition, slot: slotPosition}
				if !ok || entry.Slot != position || !sameDataVersion(entry.Ts, block.Version) {
					continue
				}
				key := pathKey{addr: block.Addr, sig: block.signature}
				if _, seen := validKeys[key]; seen {
					continue
				}
				validKeys[key] = struct{}{}
				if block.signature == 0 {
					st.TreePrimary++
				} else {
					st.TreeReplica++
				}
			}
			if occupied {
				st.TreeOccupied++
			}
		}
	}
	stashKeys := make(map[pathKey]struct{})
	for _, stash := range res.Stashs {
		st.StashVersions++
		st.StashRaw += len(stash)
		for _, block := range stash {
			entry, ok := pm[block.Addr][block.signature]
			if !ok || entry.Slot != mvpStashPosition || !sameDataVersion(entry.Ts, block.Version) {
				continue
			}
			key := pathKey{addr: block.Addr, sig: block.signature}
			if _, seen := stashKeys[key]; seen {
				continue
			}
			stashKeys[key] = struct{}{}
			validKeys[key] = struct{}{}
			if block.signature == 0 {
				st.StashPrimary++
			} else {
				st.StashReplica++
			}
		}
	}
	perAddr := make(map[int]int)
	hasPrimary := make(map[int]bool)
	for key := range validKeys {
		perAddr[key.addr]++
		if key.sig == 0 {
			hasPrimary[key.addr] = true
		}
	}
	for addr := 0; addr < addrCount; addr++ {
		if perAddr[addr] == 0 {
			st.LostAddrs++
		}
		if !hasPrimary[addr] {
			st.NoPrimaryAddrs++
		}
		if perAddr[addr] > st.MaxValidPerAddr {
			st.MaxValidPerAddr = perAddr[addr]
		}
	}
	return st
}

func observeBase(server chan<- BaseMvpServerRequest, observer *BaseMvpClient, addrCount int) globalState {
	reply := make(chan baseTraceStateResponse)
	server <- baseTraceStateRequest{Reply: reply}
	res := <-reply
	observer.consolidatePathMaps(res.PathMaps)
	pm := observer.PositionMap

	st := globalState{Seq: res.Seq}
	valid := make(map[int]struct{})
	for bucketPosition, bucket := range res.Tree.Tree {
		for slotPosition, versioned := range bucket.Slots {
			st.TotalSlots++
			occupied := false
			for _, slot := range versioned {
				if slot.IsEmpty() {
					continue
				}
				occupied = true
				block := slot.Value
				entry, ok := pm[block.Addr]
				position := BaseMvpPosition{bucket: bucketPosition, slot: slotPosition}
				if !ok || entry.Slot != position || !baseMvpSameDataVersion(entry.Ts, block.Version) {
					continue
				}
				if _, seen := valid[block.Addr]; seen {
					continue
				}
				valid[block.Addr] = struct{}{}
				st.TreePrimary++
			}
			if occupied {
				st.TreeOccupied++
			}
		}
	}
	for _, stash := range res.Stashs {
		st.StashVersions++
		st.StashRaw += len(stash)
		for _, block := range stash {
			entry, ok := pm[block.Addr]
			if !ok || entry.Slot != baseMvpStashPosition || !baseMvpSameDataVersion(entry.Ts, block.Version) {
				continue
			}
			if _, seen := valid[block.Addr]; seen {
				continue
			}
			valid[block.Addr] = struct{}{}
			st.StashPrimary++
		}
	}
	for addr := 0; addr < addrCount; addr++ {
		if _, ok := valid[addr]; !ok {
			st.LostAddrs++
			st.NoPrimaryAddrs++
		}
	}
	st.MaxValidPerAddr = 1
	return st
}

// ---------------------------------------------------------------------------
// 実験ドライバ

type stashTraceConfig struct {
	oram        string
	z, l        int
	addrCount   int
	clients     int
	accesses    int
	readRatio   float64
	zipfAlpha   float64
	accessType  string
	seed        int64
	sampleEvery int // 何ラウンドごとにサーバ状態を観測するか
	csvDir      string
}

func readStashTraceConfig(oram string, accessType string) stashTraceConfig {
	l := readStatisticalDistancePositiveIntEnv("STASH_TRACE_L", 10)
	return stashTraceConfig{
		oram:        normalizeOramType(oram),
		z:           readStatisticalDistancePositiveIntEnv("STASH_TRACE_Z", 4),
		l:           l,
		addrCount:   readStatisticalDistancePositiveIntEnv("STASH_TRACE_ADDR_COUNT", 2*(1<<(l-2))),
		clients:     readStatisticalDistancePositiveIntEnv("STASH_TRACE_CLIENTS", 15),
		accesses:    readStatisticalDistancePositiveIntEnv("STASH_TRACE_ACCESSES", 105000),
		readRatio:   readStatisticalDistanceFloatEnv("STASH_TRACE_READ_RATIO", 0.8),
		zipfAlpha:   readStatisticalDistanceFloatEnv("STASH_TRACE_ZIPF_ALPHA", 1.1),
		accessType:  accessType,
		seed:        int64(readStatisticalDistancePositiveIntEnv("STASH_TRACE_SEED", 542)),
		sampleEvery: readStatisticalDistancePositiveIntEnv("STASH_TRACE_SAMPLE_EVERY", 10),
		csvDir:      readStatisticalDistanceStringEnv("STASH_TRACE_DIR", "CSV/stash_trace"),
	}
}

func (cfg stashTraceConfig) newOperation(seed int64) AccessOperation {
	if cfg.accessType == "uniform" || cfg.accessType == "random" {
		return &readRatioUniformOperation{addrCount: cfg.addrCount, readRatio: cfg.readRatio, rng: rand.New(rand.NewSource(seed))}
	}
	return NewZipfAccessOperation(cfg.addrCount, seed, cfg.readRatio, cfg.zipfAlpha)
}

// readRatioUniformOperation は一様アドレス + 指定 Read 比率(既存の Uniform は Read 比率 0.5 固定のため別に用意)。
type readRatioUniformOperation struct {
	addrCount int
	readRatio float64
	rng       *rand.Rand
}

func (o *readRatioUniformOperation) Next() OramOP {
	target := o.rng.Intn(o.addrCount)
	op := Read
	if o.rng.Float64() >= o.readRatio {
		op = Write
	}
	return OramOP{OP: op, target: target, param: fmt.Sprintf("addr-%d", target)}
}

type traceWriter struct {
	file *os.File
	w    *csv.Writer
}

func newTraceWriter(path string, header []string) *traceWriter {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		log.Fatal(err)
	}
	f, err := os.Create(path)
	if err != nil {
		log.Fatal(err)
	}
	w := csv.NewWriter(f)
	_ = w.Write(header)
	return &traceWriter{file: f, w: w}
}

func (t *traceWriter) row(values ...any) {
	rec := make([]string, len(values))
	for i, v := range values {
		switch x := v.(type) {
		case float64:
			rec[i] = strconv.FormatFloat(x, 'f', 6, 64)
		default:
			rec[i] = fmt.Sprint(x)
		}
	}
	_ = t.w.Write(rec)
}

func (t *traceWriter) close() {
	t.w.Flush()
	_ = t.file.Close()
}

func (cfg stashTraceConfig) tag() string {
	return fmt.Sprintf("%s_%s_r%03d_c%d_l%d", cfg.oram, cfg.accessType, int(cfg.readRatio*100+0.5), cfg.clients, cfg.l)
}

var globalHeader = []string{"round", "accesses", "seq", "tree_primary", "tree_replica", "tree_occupied_slots", "total_slots", "fill_valid", "stash_primary", "stash_replica", "stash_valid", "stash_raw", "stash_versions", "lost_addrs", "no_primary_addrs", "max_valid_copies_per_addr"}

func writeGlobalRow(w *traceWriter, round int, accesses int, st globalState) {
	fill := float64(st.TreePrimary+st.TreeReplica) / float64(max(st.TotalSlots, 1))
	w.row(round, accesses, st.Seq, st.TreePrimary, st.TreeReplica, st.TreeOccupied, st.TotalSlots, fill,
		st.StashPrimary, st.StashReplica, st.StashPrimary+st.StashReplica, st.StashRaw, st.StashVersions,
		st.LostAddrs, st.NoPrimaryAddrs, st.MaxValidPerAddr)
}

// RunStashTraceExperiment は実験A(スタッシュ増加の原因の計測)を実行する。
func RunStashTraceExperiment(oram string, accessType string) {
	cfg := readStashTraceConfig(oram, accessType)
	log.Printf("stash-trace: %+v", cfg)
	rand.Seed(cfg.seed)
	started := time.Now()
	switch cfg.oram {
	case "re-mvp-oram":
		runCapeStashTrace(cfg)
	case "mvp-oram":
		runBaseStashTrace(cfg)
	default:
		log.Fatalf("unknown oram %q", cfg.oram)
	}
	log.Printf("stash-trace done: %s elapsed=%s", cfg.tag(), time.Since(started).Round(time.Second))
}

var capeAccessHeader = []string{"round", "client", "op", "via_replica",
	"path_slots", "in_slots_primary", "in_slots_replica", "in_slots_collision",
	"in_place", "unused", "unused_was_replica", "unused_was_empty", "unused_was_primary",
	"pending_from_stash_primary", "pending_from_stash_replica", "pending_collision_primary", "pending_collision_replica",
	"stash_in_size", "stash_out_size",
	"out_retained_primary", "out_retained_replica", "out_collision_primary", "out_collision_replica",
	"outflow_stash_to_path",
	"dedup_deleted", "dedup_deleted_same_key", "dedup_deleted_primary",
	"copies_created", "empty_after_evict", "path_map_len", "stash_dup_in_w"}

type capePrepared struct {
	client   *MvpClient
	op       OramOP
	sig      int
	leaf     MvpPosition
	trace    capeEvictTrace
	path     map[MvpPosition]MvpSlot
	stash    []MvpDataBlock
	pathMap  []path
	stashIn  int // W に入ったスタッシュ由来ブロック数(重複込み)
	stashDup int
}

func runCapeStashTrace(cfg stashTraceConfig) {
	server := NewMvpServer(cfg.z, cfg.l)
	positionMap := server.InitializeRandomData(cfg.addrCount, cfg.seed)
	go server.Run()

	clients := make([]*MvpClient, cfg.clients)
	ops := make([]AccessOperation, cfg.clients)
	for i := range clients {
		clients[i] = NewMvpClient(cfg.l, cfg.z, i, clonePositionMap(positionMap), server.Requests)
		ops[i] = cfg.newOperation(cfg.seed + int64(i))
	}
	observer := NewMvpClient(cfg.l, cfg.z, stashTraceObserverID, clonePositionMap(positionMap), server.Requests)

	accessW := newTraceWriter(filepath.Join(cfg.csvDir, cfg.tag()+"_access.csv"), capeAccessHeader)
	globalW := newTraceWriter(filepath.Join(cfg.csvDir, cfg.tag()+"_global.csv"), globalHeader)
	defer accessW.close()
	defer globalW.close()

	writeGlobalRow(globalW, 0, 0, observeCape(server.Requests, observer, cfg.addrCount))

	rounds := (cfg.accesses + cfg.clients - 1) / cfg.clients
	prepared := make([]*capePrepared, cfg.clients)
	for round := 1; round <= rounds; round++ {
		// GetPM(全員)
		for i, c := range clients {
			op := ops[i].Next()
			version, pms, err := c.GetPM()
			if err != nil {
				log.Fatal(err)
			}
			c.seq = version
			c.consolidatePathMaps(pms)
			sig, leaf, ok := c.choosetargetLeaf(op.target, op.OP)
			if !ok {
				log.Fatalf("round %d client %d: no candidate for addr %d", round, i, op.target)
			}
			prepared[i] = &capePrepared{client: c, op: op, sig: sig, leaf: leaf}
		}
		// GetPS + populatePath(全員)
		var wg sync.WaitGroup
		for _, p := range prepared {
			wg.Add(1)
			go func(p *capePrepared) {
				defer wg.Done()
				c := p.client
				var err error
				c.path, c.Stash, err = c.GetPS(p.leaf)
				if err != nil {
					log.Fatal(err)
				}
				W := c.mergePathStashes()
				seen := make(map[pathKey]bool)
				for _, blocks := range W {
					for _, b := range blocks {
						if c.PositionMap[b.Addr][b.signature].Slot == mvpStashPosition {
							p.stashIn++
							k := pathKey{b.Addr, b.signature}
							if seen[k] {
								p.stashDup++
							}
							seen[k] = true
						}
					}
				}
				c.trace = &p.trace
				p.path, p.stash, p.pathMap = c.populatePath(W, p.op, p.sig)
				c.trace = nil
			}(p)
		}
		wg.Wait()
		// Evict(全員、順番はランダム)
		for _, idx := range rand.Perm(len(prepared)) {
			p := prepared[idx]
			if err := p.client.Evict(p.path, p.pathMap, p.stash); err != nil {
				log.Fatal(err)
			}
		}
		for i, p := range prepared {
			t := p.trace
			pendingStash := t.PendingFromStashPrimary + t.PendingFromStashReplica
			retained := t.StashOutRetainedPrimary + t.StashOutRetainedReplica
			outflow := pendingStash - retained
			accessW.row(round, i, p.op.OP, boolInt(p.sig != 0),
				t.PathSlots, t.InSlotsPrimary, t.InSlotsReplica, t.InSlotsCollision,
				t.InPlace, t.Unused, t.UnusedWasReplica, t.UnusedWasEmpty, t.UnusedWasPrimary,
				t.PendingFromStashPrimary, t.PendingFromStashReplica, t.PendingCollisionPrimary, t.PendingCollisionReplica,
				p.stashIn, len(p.stash),
				t.StashOutRetainedPrimary, t.StashOutRetainedReplica, t.StashOutCollisionPrimary, t.StashOutCollisionReplica,
				outflow,
				t.DedupDeleted, t.DedupDeletedSameKey, t.DedupDeletedPrimary,
				t.CopiesCreated, t.EmptyAfterEvict, len(p.pathMap), p.stashDup)
		}
		if round%cfg.sampleEvery == 0 || round == rounds {
			st := observeCape(server.Requests, observer, cfg.addrCount)
			writeGlobalRow(globalW, round, round*cfg.clients, st)
			if round%(cfg.sampleEvery*100) == 0 {
				log.Printf("cape round=%d stash_valid=%d stash_raw=%d tree_primary=%d tree_replica=%d lost=%d", round, st.StashPrimary+st.StashReplica, st.StashRaw, st.TreePrimary, st.TreeReplica, st.LostAddrs)
				accessW.w.Flush()
				globalW.w.Flush()
			}
		}
	}
}

var baseAccessHeader = []string{"round", "client", "op", "path_slots", "swap_chosen", "swap_empty",
	"stash_in_size", "stash_out_size", "inflow_target", "inflow_swapped_out", "outflow_stash_to_path", "w_size", "path_map_len"}

type basePrepared struct {
	client      *BaseMvpClient
	op          OramOP
	leaf        BaseMvpPosition
	path        map[BaseMvpPosition]BaseMvpSlot
	stash       []BaseMvpDataBlock
	pathMap     []basePath
	stashIn     int
	targetPath  bool // アクセス対象がパス上にいた
	inflowOther int
	outflow     int
	wSize       int
}

func runBaseStashTrace(cfg stashTraceConfig) {
	server := NewBaseMvpServer(cfg.z, cfg.l)
	positionMap := server.InitializeRandomData(cfg.addrCount, cfg.seed)
	go server.Run()

	clients := make([]*BaseMvpClient, cfg.clients)
	ops := make([]AccessOperation, cfg.clients)
	for i := range clients {
		clients[i] = NewBaseMvpClient(cfg.l, cfg.z, i, cloneBaseMvpPositionMap(positionMap), server.Requests)
		ops[i] = cfg.newOperation(cfg.seed + int64(i))
	}
	observer := NewBaseMvpClient(cfg.l, cfg.z, stashTraceObserverID, cloneBaseMvpPositionMap(positionMap), server.Requests)

	accessW := newTraceWriter(filepath.Join(cfg.csvDir, cfg.tag()+"_access.csv"), baseAccessHeader)
	globalW := newTraceWriter(filepath.Join(cfg.csvDir, cfg.tag()+"_global.csv"), globalHeader)
	defer accessW.close()
	defer globalW.close()
	writeGlobalRow(globalW, 0, 0, observeBase(server.Requests, observer, cfg.addrCount))

	rounds := (cfg.accesses + cfg.clients - 1) / cfg.clients
	prepared := make([]*basePrepared, cfg.clients)
	for round := 1; round <= rounds; round++ {
		for i, c := range clients {
			op := ops[i].Next()
			version, pms, err := c.GetPM()
			if err != nil {
				log.Fatal(err)
			}
			c.seq = version
			c.consolidatePathMaps(pms)
			prepared[i] = &basePrepared{client: c, op: op, leaf: c.baseMvpSelectPath(c.PositionMap[op.target].Slot, c.L)}
		}
		var wg sync.WaitGroup
		for _, p := range prepared {
			wg.Add(1)
			go func(p *basePrepared) {
				defer wg.Done()
				c := p.client
				var err error
				c.basePath, c.Stash, err = c.GetPS(p.leaf)
				if err != nil {
					log.Fatal(err)
				}
				W := c.mergePathStashes()
				target, ok := W[p.op.target]
				if !ok {
					log.Fatalf("base client %d: target %d not in working set", c.ClientID, p.op.target)
				}
				if p.op.OP == Write {
					target.Data = p.op.param
					target.Version = Versions{c.seq, c.seq, c.seq}
				} else {
					target.Version.SetA(c.seq)
				}
				W[p.op.target] = target
				p.wSize = len(W)
				origin := make(map[int]bool, len(W)) // true = スタッシュ由来
				for addr := range W {
					origin[addr] = c.PositionMap[addr].Slot == baseMvpStashPosition
					if origin[addr] {
						p.stashIn++
					}
				}
				p.targetPath = !origin[p.op.target]
				p.path, p.stash, p.pathMap = c.populatePath(W, p.op)
				inStash := make(map[int]bool, len(p.stash))
				for _, b := range p.stash {
					inStash[b.Addr] = true
				}
				for addr, fromStash := range origin {
					if fromStash && !inStash[addr] {
						p.outflow++
					}
					if !fromStash && inStash[addr] && addr != p.op.target {
						p.inflowOther++
					}
				}
			}(p)
		}
		wg.Wait()
		for _, idx := range rand.Perm(len(prepared)) {
			p := prepared[idx]
			if err := p.client.Evict(p.path, p.pathMap, p.stash); err != nil {
				log.Fatal(err)
			}
		}
		for i, p := range prepared {
			c := p.client
			accessW.row(round, i, p.op.OP, (c.L+1)*c.Z, c.traceSwapChosen, c.traceSwapEmpty,
				p.stashIn, len(p.stash), boolInt(p.targetPath), p.inflowOther, p.outflow, p.wSize, len(p.pathMap))
		}
		if round%cfg.sampleEvery == 0 || round == rounds {
			st := observeBase(server.Requests, observer, cfg.addrCount)
			writeGlobalRow(globalW, round, round*cfg.clients, st)
			if round%(cfg.sampleEvery*100) == 0 {
				log.Printf("base round=%d stash_valid=%d stash_raw=%d tree_primary=%d lost=%d", round, st.StashPrimary, st.StashRaw, st.TreePrimary, st.LostAddrs)
				accessW.w.Flush()
				globalW.w.Flush()
			}
		}
	}
}

func boolInt(b bool) int {
	if b {
		return 1
	}
	return 0
}
