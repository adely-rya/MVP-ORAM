package main

// 使い方:
//   go run . -scheme mvp -read 0.8 -accesses 105000
//   go run . -scheme cape -read 0.95 -rmax 4
// scheme: mvp (論文どおり) / mvp-packup (対照: レプリカなしで上に詰める) /
//         cape (fewest) / cape-hot / cape-shallow

import (
	"encoding/csv"
	"flag"
	"fmt"
	"log"
	"math/rand"
	"os"
	"path/filepath"
	"strconv"
	"time"
)

func main() {
	scheme := flag.String("scheme", "mvp", "mvp | mvp-packup | cape | cape-hot | cape-shallow")
	L := flag.Int("L", 10, "tree height (levels 0..L)")
	Z := flag.Int("Z", 4, "bucket size")
	N := flag.Int("N", 0, "number of blocks (default: number of tree nodes 2^(L+1)-1, as in the paper)")
	clients := flag.Int("c", 15, "concurrent clients")
	accesses := flag.Int("accesses", 105000, "total accesses")
	readRatio := flag.Float64("read", 0.8, "read ratio")
	alpha := flag.Float64("alpha", 1.0, "zipf exponent (0 = uniform)")
	rmax := flag.Int("rmax", 4, "max replicas per block (cape)")
	minDepth := flag.Int("mindepth", 4, "cape-shallow: create replicas only at depth <= this")
	leafRule := flag.String("leafrule", "union", "union | copy")
	sample := flag.Int("sample", 10, "rounds between state samples")
	secEvery := flag.Int("secevery", 200, "rounds between security snapshots")
	warmup := flag.Int("warmup", 20000, "accesses before security snapshots are aggregated")
	seed := flag.Int64("seed", 542, "seed")
	sigma := flag.Int("sigma", 0, "Strong MVP-ORAM: dummy accesses per real access")
	official := flag.Bool("official", false, "match the public Java implementation: empty start, a-ascending in-place reorder, fixed evict order")
	evictCold := flag.Bool("evictcold", false, "tweak: evict least recently accessed stash blocks first")
	outDir := flag.String("out", "results", "output directory")
	flag.Parse()

	if *N == 0 {
		*N = (1 << (*L + 1)) - 1
	}
	cfg := &Config{L: *L, Z: *Z, N: *N, RMax: *rmax, MinDepth: *minDepth, NoSelfRep: true}
	switch *scheme {
	case "mvp":
	case "mvp-packup":
		cfg.PackUp = true
	case "cape":
		cfg.Replicas = ReplicaFewest
	case "cape-hot":
		cfg.Replicas = ReplicaHot
	case "cape-shallow":
		cfg.Replicas = ReplicaShallow
	case "cape-stash":
		cfg.Replicas = ReplicaStashHot
	default:
		log.Fatalf("unknown scheme %q", *scheme)
	}
	cfg.Sigma = *sigma
	cfg.EvictCold = *evictCold
	if *official {
		cfg.ReorderOfficial, cfg.EmptyStart, cfg.FixedEvictOrder = true, true, true
	}
	if *leafRule == "copy" {
		cfg.LeafRule = LeafCopyUniform
	}

	rng := rand.New(rand.NewSource(*seed))
	wl := NewWorkload(cfg.N, *alpha, *readRatio, rng)
	sim := NewSim(cfg, *clients, wl, *seed)

	tag := fmt.Sprintf("%s_r%03d_a%.1f_c%d_L%d_N%d", *scheme, int(*readRatio*100+0.5), *alpha, *clients, *L, cfg.N)
	if cfg.Replicas != ReplicaNone {
		tag += fmt.Sprintf("_rmax%d", *rmax)
	}
	if cfg.LeafRule == LeafCopyUniform {
		tag += "_copyrule"
	}
	if cfg.Sigma > 0 {
		tag += fmt.Sprintf("_sigma%d", cfg.Sigma)
	}
	if cfg.EvictCold {
		tag += "_evictcold"
	}
	if *official {
		tag += "_official"
	}
	if err := os.MkdirAll(*outDir, 0o755); err != nil {
		log.Fatal(err)
	}
	ts := newCSV(filepath.Join(*outDir, tag+"_timeseries.csv"), []string{
		"round", "accesses", "stash_valid", "stash_raw", "stash_versions", "tree_primary", "tree_replica", "fill",
		"lost", "wrong_replica_data",
		"sz_empty_per_access", "sz_empty_had_replica_per_access", "in_swapped", "in_collision", "in_target", "out_to_path",
		"rep_created", "rep_dropped", "rep_kept", "via_replica_frac", "cand_leaves_at_access",
		"ml_len_read", "ml_len_write", "bw_getpm_entries", "bw_getps_path_blocks", "bw_getps_stash_blocks", "bw_evict_blocks", "client0_new_stash"})
	sec := newCSV(filepath.Join(*outDir, tag+"_security.csv"), []string{
		"round", "accesses", "stash", "tv_lca_uniform", "tv_lca_workload", "tv_leaf_uniform", "tv_leaf_workload",
		"cand_p10", "cand_p50", "cand_p90", "cand_nostash_p10", "cand_nostash_p50", "cand_nostash_p90",
		"k_mean_nostash", "k1_frac", "k2_frac", "k3plus_frac"})
	defer ts.close()
	defer sec.close()

	rounds := (*accesses + *clients - 1) / *clients * (cfg.Sigma + 1)
	warmRounds := (*warmup + *clients - 1) / *clients * (cfg.Sigma + 1)
	var bwTot RoundStats
	var win RoundStats
	var aggH1, aggH0 [2][]float64
	var aggTV, aggTVLeaf [2]float64
	nSec := 0
	candHist := map[int]int{}
	candHistNoStash := map[int]int{}
	kHist := map[int]int{}
	started := time.Now()
	for r := 1; r <= rounds; r++ {
		rs := sim.Round()
		win.Add(rs)
		if r == warmRounds {
			sim.KHist = nil
		}
		if r > warmRounds {
			bwTot.Add(rs)
		}
		if r%*sample == 0 || r == rounds {
			g := sim.Observe()
			if g.Lost > 0 || g.WrongData > 0 {
				log.Fatalf("round %d: lost=%d wrong=%d", r, g.Lost, g.WrongData)
			}
			a := float64(max(win.Accesses, 1))
			ts.row(r, r**clients, g.StashValid, g.StashRaw, g.StashVersions, g.TreePrimary, g.TreeReplica,
				float64(g.TreePrimary+g.TreeReplica)/float64(g.TotalSlots), g.Lost, g.WrongData,
				float64(win.SZEmpty)/a, float64(win.SZHadReplica)/a, float64(win.InSwapped)/a, float64(win.InCollision)/a,
				float64(win.InTarget)/a, float64(win.Out)/a, float64(win.RepCreated)/a, float64(win.RepDropped)/a,
				float64(win.RepKept)/a, float64(win.ViaReplica)/a, win.CandLeaves/a,
				float64(win.MlLenRead)/float64(max(win.Reads, 1)), float64(win.MlLenWrite)/float64(max(win.Writes, 1)),
				float64(win.PMEntries)/a, float64(win.PSBlocks)/a, float64(win.PSStash)/a,
				float64(win.EvictSlot+win.EvictStash)/a, float64(win.Client0Stash)/float64(*sample))
			win = RoundStats{}
		}
		if r%(*secEvery*(cfg.Sigma+1)) == 0 && r > warmRounds {
			snap := sim.Security(wl.Weights)
			var nostash, kvals []int
			k1, k2, k3, kn := 0, 0, 0, 0
			ksum := 0
			for a := 0; a < cfg.N; a++ {
				candHist[snap.Cand[a]]++
				if !snap.InStash[a] {
					nostash = append(nostash, snap.Cand[a])
					candHistNoStash[snap.Cand[a]]++
					kvals = append(kvals, snap.K[a])
					kHist[snap.K[a]]++
					ksum += snap.K[a]
					kn++
					switch {
					case snap.K[a] == 1:
						k1++
					case snap.K[a] == 2:
						k2++
					default:
						k3++
					}
				}
			}
			kf := float64(max(kn, 1))
			sec.row(r, r**clients, snap.StashSize, snap.TV[0], snap.TV[1], snap.TVLeaf[0], snap.TVLeaf[1],
				percentile(snap.Cand, 0.1), percentile(snap.Cand, 0.5), percentile(snap.Cand, 0.9),
				percentile(nostash, 0.1), percentile(nostash, 0.5), percentile(nostash, 0.9),
				float64(ksum)/kf, float64(k1)/kf, float64(k2)/kf, float64(k3)/kf)
			for t := 0; t < 2; t++ {
				if aggH1[t] == nil {
					aggH1[t] = make([]float64, cfg.L+1)
					aggH0[t] = make([]float64, cfg.L+1)
				}
				for d := range snap.H1[t] {
					aggH1[t][d] += snap.H1[t][d]
					aggH0[t][d] += snap.H0[t][d]
				}
				aggTV[t] += snap.TV[t]
				aggTVLeaf[t] += snap.TVLeaf[t]
			}
			nSec++
		}
		if r%1000 == 0 {
			ts.w.Flush()
			sec.w.Flush()
			log.Printf("%s round %d/%d elapsed %s", tag, r, rounds, time.Since(started).Round(time.Second))
		}
	}
	// 集計: 深さヒストグラムと分布
	hist := newCSV(filepath.Join(*outDir, tag+"_lca_hist.csv"), []string{"selection", "depth", "h1", "h0"})
	for t, name := range []string{"uniform", "workload"} {
		for d := 0; d <= cfg.L && nSec > 0; d++ {
			hist.row(name, d, aggH1[t][d]/float64(nSec), aggH0[t][d]/float64(nSec))
		}
	}
	hist.close()
	dist := newCSV(filepath.Join(*outDir, tag+"_dist.csv"), []string{"kind", "value", "count"})
	for _, kv := range sortedKeys(candHist) {
		dist.row("cand_all", kv, candHist[kv])
	}
	for _, kv := range sortedKeys(candHistNoStash) {
		dist.row("cand_nostash", kv, candHistNoStash[kv])
	}
	for _, kv := range sortedKeys(kHist) {
		dist.row("k_nonnested", kv, kHist[kv])
	}
	dist.close()
	tvK := KDistanceTV(sim.KHist, IdealKDist(cfg.L, *clients))
	a := float64(max(bwTot.Accesses, 1))
	log.Printf("COST %s tv_K=%.4f stash_blocks_per_real=%.1f path_blocks_per_real=%.1f evict_blocks_per_real=%.1f log_entries_per_real=%.1f total_blocks_per_real=%.1f timesteps_per_real=%d",
		tag, tvK, float64(bwTot.PSStash)/a, float64(bwTot.PSBlocks)/a, float64(bwTot.EvictSlot+bwTot.EvictStash)/a,
		float64(bwTot.PMEntries+bwTot.MlLen)/a, float64(bwTot.PSStash+bwTot.PSBlocks+bwTot.EvictSlot+bwTot.EvictStash)/a, cfg.Sigma+1)
	if nSec > 0 {
		log.Printf("SUMMARY %s tv_lca_uniform=%.4f tv_lca_workload=%.4f tv_leaf_uniform=%.4f tv_leaf_workload=%.4f snapshots=%d",
			tag, aggTV[0]/float64(nSec), aggTV[1]/float64(nSec), aggTVLeaf[0]/float64(nSec), aggTVLeaf[1]/float64(nSec), nSec)
	}
	log.Printf("done %s in %s", tag, time.Since(started).Round(time.Second))
}

func sortedKeys(m map[int]int) []int {
	ks := make([]int, 0, len(m))
	for k := range m {
		ks = append(ks, k)
	}
	for i := 1; i < len(ks); i++ {
		for j := i; j > 0 && ks[j] < ks[j-1]; j-- {
			ks[j], ks[j-1] = ks[j-1], ks[j]
		}
	}
	return ks
}

type csvOut struct {
	f *os.File
	w *csv.Writer
}

func newCSV(path string, header []string) *csvOut {
	f, err := os.Create(path)
	if err != nil {
		log.Fatal(err)
	}
	w := csv.NewWriter(f)
	_ = w.Write(header)
	return &csvOut{f, w}
}

func (c *csvOut) row(vals ...any) {
	rec := make([]string, len(vals))
	for i, v := range vals {
		switch x := v.(type) {
		case float64:
			rec[i] = strconv.FormatFloat(x, 'f', 6, 64)
		default:
			rec[i] = fmt.Sprint(x)
		}
	}
	_ = c.w.Write(rec)
}

func (c *csvOut) close() {
	c.w.Flush()
	_ = c.f.Close()
}
