// ============================================================================
// tctl/benchmark.hpp — Benchmarking suite for CAV-style scalability curves
// ============================================================================
//
// Provides parameterized benchmark families (depth, M, obligations,
// until/release) that generate TCTL formulas, run the tableau engine,
// and write CSV results plus a reproducibility manifest.
//
// ============================================================================

#ifndef CTL_BENCHMARK_HPP
#define CTL_BENCHMARK_HPP

#include <cstdint>
#include <string>
#include <vector>

namespace tctl {

// ── BenchmarkOptions ────────────────────────────────────────────────────────

struct BenchmarkOptions {
    int         timeout_s          = 30;          // per-instance timeout (CAV default)
    int         warmup_runs        = 2;           // warmup iterations (not recorded)
    int         num_threads        = 1;           // reproducibility
    uint64_t    seed               = 1337;        // fixed seed
    std::string out_dir_override;                 // optional output dir
    bool        run_ablation       = true;        // if feasible
    bool        abstraction_M_default = true;     // default abstraction mode

    // ── Per-family parameters ────────────────────────────────────────
    // Family A — depth curves
    int         max_depth          = 14;          // A: depth 1..max_depth
    int         M_fixed_A          = 10;          // A2-A4, D/E/Mixed: fixed M

    // Family B — max-constant M sweep
    std::vector<int> M_values      = {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024};
    int         b4_k               = 5;           // B4: chain-of-windows conjuncts
    int         b5_depth           = 6;           // B5: nested-chain nesting depth

    // Family C — obligations / clock pressure
    int         max_k              = 14;          // C: k = 1..max_k

    // Families D/E — until / release nesting
    int         max_until_depth    = 10;          // D/E/Mixed: depth 1..max_until_depth
    int         max_conj_untils    = 6;           // D conjunctive: u ≤ max_conj_untils

    // Family F — Zeno rejection
    int         max_zeno_M         = 16;          // F: M = 2..max_zeno_M

    // Family G — clock dimensionality
    int         max_clocks_k       = 10;          // G: k = 1..max_clocks_k
    int         clocks_M           = 5;           // G: fixed M

    // Family H — chained eventualities
    int         max_chain_n        = 14;          // H: n = 1..max_chain_n
    int         chain_M            = 2;           // H: fixed M

    // Family I — modality alternation
    int         max_alt_n          = 14;          // I: n = 1..max_alt_n
    int         alt_M              = 1;           // I: fixed M
};

/// Run all benchmark families and write CSVs + reproducibility.txt.
/// Returns 0 on success, non-zero on error.
int run_benchmarks(const BenchmarkOptions& opt);

}  // namespace tctl

#endif  // CTL_BENCHMARK_HPP
