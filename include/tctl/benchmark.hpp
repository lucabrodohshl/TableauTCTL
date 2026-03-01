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
    int         max_depth          = 14;          // family A upper bound
    int         max_k              = 14;          // family C upper bound
    int         max_until_depth    = 10;          // family D/E upper bound
    std::vector<int> M_values      = {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024}; // family B M values
    std::string out_dir_override;                 // optional output dir
    bool        run_ablation       = true;        // if feasible
    bool        abstraction_M_default = true;     // default abstraction mode
};

/// Run all benchmark families and write CSVs + reproducibility.txt.
/// Returns 0 on success, non-zero on error.
int run_benchmarks(const BenchmarkOptions& opt);

}  // namespace tctl

#endif  // CTL_BENCHMARK_HPP
