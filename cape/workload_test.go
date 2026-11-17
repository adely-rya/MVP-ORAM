package main

import (
	"math/rand"
	"testing"
)

func TestYCSBWorkloads(t *testing.T) {
	rng := rand.New(rand.NewSource(1))
	N := 1023
	// hotspot: hot set (20%) に約 80% のアクセス
	wl, _ := NewYCSB("hotspot", N, rng)
	hot := 0
	for i := 0; i < 20000; i++ {
		a, _ := wl.NextFor(0, rng)
		if wl.isHot[a] {
			hot++
		}
	}
	if f := float64(hot) / 20000; f < 0.77 || f > 0.83 {
		t.Fatalf("hotspot hot fraction %.3f", f)
	}
	// ycsb-f: read の直後に同じクライアントが同じアドレスへ write
	wl, _ = NewYCSB("ycsb-f", N, rng)
	rmw := 0
	for i := 0; i < 5000; i++ {
		a, w := wl.NextFor(3, rng)
		if w {
			t.Fatalf("write without preceding read")
		}
		if _, ok := wl.pending[3]; ok {
			b, w2 := wl.NextFor(3, rng)
			if !w2 || b != a {
				t.Fatalf("rmw: read %d then (%d,%v)", a, b, w2)
			}
			rmw++
		}
	}
	if rmw < 2000 || rmw > 3000 {
		t.Fatalf("rmw count %d", rmw)
	}
	// ycsb-d: 最も人気のあるアドレスは直近の insert
	wl, _ = NewYCSB("ycsb-d", N, rng)
	for i := 0; i < 3000; i++ {
		wl.NextFor(0, rng)
	}
	w := wl.CurrentWeights()
	best := 0
	for a := range w {
		if w[a] > w[best] {
			best = a
		}
	}
	if best != (wl.nextKey-1)%N {
		t.Fatalf("latest: hottest %d, last insert %d", best, (wl.nextKey-1)%N)
	}
}

// 新しい複製戦略と YCSB ワークロードでも線形化可能でブロックが失われない
func TestStrategiesOnYCSB(t *testing.T) {
	for _, name := range []string{"ycsb-a", "ycsb-d", "ycsb-f", "hotspot"} {
		for _, v := range []func(*Config){
			func(c *Config) { c.Score = ScoreFreq },
			func(c *Config) { c.Place = PlaceLeaf },
			func(c *Config) { c.Place = PlaceRandom; c.Score = ScoreRandom },
			func(c *Config) { c.Score = ScoreFreq; c.RAdapt = true },
		} {
			cfg := &Config{L: 6, Z: 4, N: 127, Replicas: ReplicaStashHot, RMax: 4, NoSelfRep: true, HalfLife: 500, Clients: 8}
			v(cfg)
			rng := rand.New(rand.NewSource(5))
			wl, err := NewYCSB(name, cfg.N, rng)
			if err != nil {
				t.Fatal(err)
			}
			sim := NewSim(cfg, 8, wl, 5)
			for r := 0; r < 800; r++ {
				sim.Round()
				if r%100 == 0 {
					if g := sim.Observe(); g.Lost > 0 || g.WrongData > 0 {
						t.Fatalf("%s: lost=%d wrong=%d", name, g.Lost, g.WrongData)
					}
				}
			}
		}
	}
}
