package main

import (
	"math"
	"math/rand"
	"testing"
)

func newTestSim(t *testing.T, cfg *Config, clients int, alpha, read float64, seed int64) *Sim {
	t.Helper()
	rng := rand.New(rand.NewSource(seed))
	wl := NewWorkload(cfg.N, alpha, read, rng)
	return NewSim(cfg, clients, wl, seed)
}

func allSchemes(L, Z, N int) map[string]*Config {
	return map[string]*Config{
		"mvp":          {L: L, Z: Z, N: N, NoSelfRep: true},
		"mvp-packup":   {L: L, Z: Z, N: N, PackUp: true, NoSelfRep: true},
		"cape":         {L: L, Z: Z, N: N, Replicas: ReplicaFewest, RMax: 4, NoSelfRep: true},
		"cape-hot":     {L: L, Z: Z, N: N, Replicas: ReplicaHot, RMax: 4, NoSelfRep: true},
		"cape-copy":    {L: L, Z: Z, N: N, Replicas: ReplicaFewest, RMax: 4, LeafRule: LeafCopyUniform, NoSelfRep: true},
		"cape-stash":   {L: L, Z: Z, N: N, Replicas: ReplicaStashHot, RMax: 4, NoSelfRep: true},
		"cape-shallow": {L: L, Z: Z, N: N, Replicas: ReplicaShallow, RMax: 8, MinDepth: 3, NoSelfRep: true},
	}
}

// 線形化可能性 (Round 内で読み値を検査) とブロックの保存 (Observe) を全方式で確認する。
func TestLinearizableAndNoLoss(t *testing.T) {
	for name, cfg := range allSchemes(6, 4, 127) {
		for _, c := range []int{1, 4, 15} {
			for _, read := range []float64{0.5, 0.95} {
				sim := newTestSim(t, cfg, c, 1.2, read, 7)
				for r := 0; r < 600; r++ {
					sim.Round()
					if r%20 == 0 {
						g := sim.Observe()
						if g.Lost != 0 || g.WrongData != 0 {
							t.Fatalf("%s c=%d read=%.2f round %d: lost=%d wrong=%d", name, c, read, r, g.Lost, g.WrongData)
						}
					}
				}
			}
		}
	}
}

// Algorithm 1/3: アクセスしたブロックは必ずスタッシュへ行く。
func TestAccessedBlockGoesToStash(t *testing.T) {
	for name, cfg := range allSchemes(6, 4, 127) {
		sim := newTestSim(t, cfg, 1, 0.8, 0.8, 3)
		for r := 0; r < 500; r++ {
			cl := sim.clients[0]
			sim.Round()
			sim.obs.Update(sim.srv.ReadHistory(observerID))
			_ = cl
			// 直前のアクセス対象を Ml から特定: 本体の最後の stash 行き
			addr := lastTarget(sim)
			if sim.obs.prim[addr].Loc != LocStash {
				t.Fatalf("%s round %d: accessed addr %d not in stash (loc=%d)", name, r, addr, sim.obs.prim[addr].Loc)
			}
		}
	}
}

func lastTarget(sim *Sim) int {
	// アクセス対象の ts は ⟨_, seq, seq⟩。最大の a を持つ本体がアクセス対象。
	best, bestA := -1, -1
	for a, e := range sim.obs.prim {
		if e.TS.A > bestA {
			best, bestA = a, e.TS.A
		}
	}
	return best
}

// 単一クライアントでは各スロットの版は常に1つ (並列でなければ衝突しない)。
func TestSingleClientNoMultiVersion(t *testing.T) {
	cfg := &Config{L: 6, Z: 4, N: 127, NoSelfRep: true}
	sim := newTestSim(t, cfg, 1, 1.0, 0.5, 11)
	for r := 0; r < 300; r++ {
		sim.Round()
	}
	nodes := 1 << (cfg.L + 1)
	for sl := cfg.Z; sl < nodes*cfg.Z; sl++ {
		if n := len(sim.srv.AliveSlot(sl)); n > 1 {
			t.Fatalf("slot %d has %d live versions with a single client", sl, n)
		}
	}
	if n := len(sim.srv.AliveStashes()); n != 1 {
		t.Fatalf("%d live stash versions with a single client", n)
	}
}

// 並列 evict では、他クライアントが同時に追加した版は消さない (Tc \ T)。
func TestConcurrentEvictKeepsOthersVersions(t *testing.T) {
	srv := NewServer(2, 1)
	srv.GetPM(1)
	srv.GetPM(2)
	leaf := 0
	sl := PathSlots(2, 1, leaf)[2]
	b1 := Block{Addr: 1, TS: TS{1, 1, 1}}
	b2 := Block{Addr: 2, TS: TS{2, 2, 2}}
	srv.Evict(1, leaf, nil, map[int]*Block{sl: &b1}, nil)
	srv.Evict(2, leaf, nil, map[int]*Block{sl: &b2}, nil)
	if got := len(srv.AliveSlot(sl)); got != 2 {
		t.Fatalf("expected 2 concurrent versions, got %d", got)
	}
	srv.GetPM(3)
	srv.Evict(3, leaf, nil, map[int]*Block{}, nil)
	if got := len(srv.AliveSlot(sl)); got != 0 {
		t.Fatalf("expected versions seen by client 3 to be replaced, got %d", got)
	}
}

// 全ブロックがスタッシュにあれば、どのパス選択も一様なので識別アドバンテージは 0。
func TestSecurityAllInStashIsZero(t *testing.T) {
	cfg := &Config{L: 5, Z: 4, N: 20, NoSelfRep: true}
	sim := newTestSim(t, cfg, 2, 1.0, 0.5, 1)
	for a := range sim.obs.prim {
		sim.obs.prim[a] = pmEntry{LocStash, TS{0, 0, 0}}
	}
	snap := sim.Security(sim.wl.Weights)
	for k := 0; k < 2; k++ {
		if snap.TV[k] > 1e-9 || snap.TVLeaf[k] > 1e-9 {
			t.Fatalf("expected zero advantage, got %v %v", snap.TV, snap.TVLeaf)
		}
	}
}

// 全ブロックがリーフにあれば H1 は必ず同一リーフ → 同一リーフ判定のアドバンテージは 1 - P0(同一リーフ)。
func TestSecurityAllAtLeaves(t *testing.T) {
	L, Z := 4, 4
	cfg := &Config{L: L, Z: Z, N: 16, NoSelfRep: true}
	sim := newTestSim(t, cfg, 2, 0, 0.5, 1)
	for a := range sim.obs.prim {
		node := (1 << L) + a
		sim.obs.prim[a] = pmEntry{node * Z, TS{0, 0, 0}}
		sim.obs.reps[a] = nil
	}
	snap := sim.Security(sim.wl.Weights)
	if math.Abs(snap.H1[0][L]-1) > 1e-9 {
		t.Fatalf("H1 same-leaf prob = %f, want 1", snap.H1[0][L])
	}
	if math.Abs(snap.TVLeaf[0]-1) > 1e-9 { // 別ブロックは別リーフ
		t.Fatalf("TVLeaf = %f, want 1", snap.TVLeaf[0])
	}
}

// Read と Write でログ長の分布に構造的な差がないこと (CAPE)。
func TestLogLengthReadWriteSimilar(t *testing.T) {
	cfg := &Config{L: 8, Z: 4, N: 511, Replicas: ReplicaFewest, RMax: 4, NoSelfRep: true}
	sim := newTestSim(t, cfg, 15, 1.0, 0.5, 5)
	var tot RoundStats
	for r := 0; r < 600; r++ {
		st := sim.Round()
		if r > 200 {
			tot.Add(st)
		}
	}
	mr := float64(tot.MlLenRead) / float64(tot.Reads)
	mw := float64(tot.MlLenWrite) / float64(tot.Writes)
	t.Logf("mean Ml length read=%.2f write=%.2f", mr, mw)
	if math.Abs(mr-mw) > 1.5 {
		t.Fatalf("read/write log length differ: %.2f vs %.2f", mr, mw)
	}
}
