// ============================================================================
// benchmark.cpp — CAV-style benchmarking suite for TCTL satisfiability
// ============================================================================
//
// Parameterized formula generators, scalability curves, and CSV output.
// Called via `--benchmark` from the CLI.
//
// ============================================================================

#include "tctl/benchmark.hpp"
#include "tctl/ast.hpp"
#include "tctl/lexer.hpp"
#include "tctl/normalization.hpp"
#include "tctl/parser.hpp"
#include "tctl/tableau.hpp"
#include "tctl/utils.hpp"

#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

namespace tctl {

// ── Helpers ─────────────────────────────────────────────────────────────────

/// Escape a CSV field value (double-quote wrapping + escaping).
static std::string csv_esc(const std::string& s) {
    std::string out = "\"";
    for (char c : s) {
        if (c == '"') out += "\"\"";
        else          out += c;
    }
    out += '"';
    return out;
}

/// Format a verdict enum to string.
static const char* verdict_str(Result::Value v) {
    switch (v) {
        case Result::Value::Satisfiable:   return "SAT";
        case Result::Value::Unsatisfiable: return "UNSAT";
        case Result::Value::Timeout:       return "TIMEOUT";
    }
    return "UNKNOWN";
}

/// Get current timestamp as a formatted string.
static std::string timestamp_string() {
    std::time_t t  = std::time(nullptr);
    std::tm     tm = *std::localtime(&t);
    std::ostringstream oss;
    oss << std::put_time(&tm, "%Y%m%d_%H%M%S");
    return oss.str();
}

static std::string timestamp_readable() {
    std::time_t t  = std::time(nullptr);
    std::tm     tm = *std::localtime(&t);
    std::ostringstream oss;
    oss << std::put_time(&tm, "%Y-%m-%d %H:%M:%S");
    return oss.str();
}

/// Run a shell command and capture its stdout (best effort).
static std::string shell_capture(const char* cmd) {
    std::string result;
    FILE* pipe = popen(cmd, "r");
    if (!pipe) return "(not available)";
    char buf[256];
    while (fgets(buf, sizeof(buf), pipe)) {
        result += buf;
    }
    pclose(pipe);
    // Trim trailing newline(s).
    while (!result.empty() && (result.back() == '\n' || result.back() == '\r'))
        result.pop_back();
    return result.empty() ? "(not available)" : result;
}

// ── Formula generators ──────────────────────────────────────────────────────

// Family A1: untimed alternation AG(EF(AG(EF(... p0 ...))))
static std::string gen_depth_untimed(int depth) {
    // depth d layers alternating AG / EF around p0
    std::string core = "p0";
    for (int i = 0; i < depth; ++i) {
        if (i % 2 == 0) core = "EF(" + core + ")";
        else             core = "AG(" + core + ")";
    }
    return core;
}

// Family A2: overlapping timed obligations — d conjuncts, fresh atoms.
// EF[0,M] p1 & EF[1,M+1] p2 & ... & EF[d-1,M+d-1] pd
// Each EF introduces a fresh clock; overlapping windows force zone
// interaction.  SAT: each obligation can be met on a separate path.
static std::string gen_a2_overlap_sat(int depth, int M) {
    std::string result;
    for (int i = 0; i < depth; ++i) {
        if (i > 0) result += " & ";
        int lo = i;
        int hi = i + M;
        result += "EF[" + std::to_string(lo) + "," +
                  std::to_string(hi) + "] p" + std::to_string(i + 1);
    }
    return result;
}

// Family A3: nested EU with fresh atoms per layer.
// E(true U[1,M] (p1 & E(true U[1,M] (p2 & ... E(true U[1,M] pd)...))))
// Each nesting level adds a clock AND forces eventuality checking.
// Fresh atoms per layer prevent zone collapse.  SAT.
static std::string gen_a3_nested_eu(int depth, int M) {
    std::string interval = "[1," + std::to_string(M) + "]";
    // Build inside-out: core is pd, then wrap.
    std::string core = "p" + std::to_string(depth);
    for (int i = depth - 1; i >= 1; --i) {
        core = "p" + std::to_string(i) + " & E(true U" + interval + " " + core + ")";
    }
    // Outermost EU wraps the whole chain.
    core = "E(true U" + interval + " " + core + ")";
    return core;
}

// Family A4: killed obligations (UNSAT).
// Same d overlapping EF as A2, plus AG[0,M+d] (!p1 & !p2 & ... & !pd).
// The AG universally prevents any pi from ever holding within the combined
// window, making every EF obligation unsatisfiable.  Forces d+1 clocks
// and the solver must refute each obligation individually.
static std::string gen_a4_killed_unsat(int depth, int M) {
    // EF obligations (same as A2)
    std::string result;
    for (int i = 0; i < depth; ++i) {
        if (i > 0) result += " & ";
        int lo = i;
        int hi = i + M;
        result += "EF[" + std::to_string(lo) + "," +
                  std::to_string(hi) + "] p" + std::to_string(i + 1);
    }
    // Killer constraint: AG[0, M+d] (!p1 & !p2 & ... & !pd)
    result += " & AG[0," + std::to_string(M + depth) + "] (";
    for (int i = 0; i < depth; ++i) {
        if (i > 0) result += " & ";
        result += "!p" + std::to_string(i + 1);
    }
    result += ")";
    return result;
}

// Family B1 — EU delay: forces time progression (cannot discharge at t=0)
// E((!p0) U[0,M] p0)  — SAT, must find a path where !p0 holds until p0
static std::string gen_b1_eu_delay(int M) {
    return "E((!p0) U[0," + std::to_string(M) + "] p0)";
}

// Family B2 — Deadline conflict (UNSAT): globally !p0 within [0,M]
// but must eventually reach p0 within [1,M].
// AG[0,M] !p0 & EF[1,M] p0
// For M=1 uses [0,M] for EF to avoid point interval.
static std::string gen_b2_deadline_unsat(int M) {
    if (M <= 1) {
        return "AG[0," + std::to_string(M) + "] !p0 & EF[0," +
               std::to_string(M) + "] p0";
    }
    return "AG[0," + std::to_string(M) + "] !p0 & EF[1," +
           std::to_string(M) + "] p0";
}

// Family B3 — Negated window (UNSAT): requires p0 to hold and not hold
// in the same timed window, forcing negated timed modality handling.
// EF[0,M] p0 & !EF[0,M] p0
static std::string gen_b3_negated_window(int M) {
    return "EF[0," + std::to_string(M) + "] p0 & !EF[0," +
           std::to_string(M) + "] p0";
}

// Family B4 — Chain-of-windows SAT, fixed k=5.
// step = max(1, M / k), windows: EF[0,step] p1 & EF[step,2*step] p2 & ...
// max_const_in_formula = k * step ≈ M.  Structure is constant (5 conjuncts,
// 5 clocks); only the interval endpoints grow with M, tightening
// extrapolation and forcing finer zone distinctions.
static constexpr int kB4_k = 5;

struct B4Result { std::string formula; int k; int max_const; };

static B4Result gen_b4_chain_windows(int M) {
    int k    = kB4_k;
    int step = std::max(1, M / k);
    std::string result;
    for (int i = 0; i < k; ++i) {
        if (i > 0) result += " & ";
        int lo = i * step;
        int hi = (i + 1) * step;
        result += "EF[" + std::to_string(lo) + "," +
                  std::to_string(hi) + "] p" + std::to_string(i + 1);
    }
    return {result, k, k * step};
}

// Family B5 — Nested timed chain SAT, fixed depth=6.
// E(true U[0,M] E(true U[0,M] ... p0)) — 6 levels.
// Structure is constant (6 nested EU, 6 clocks); only M varies,
// which raises max_constants_ per clock and tightens extrapolation.
static constexpr int kB5_depth = 6;

struct B5Result { std::string formula; int depth; int max_const; };

static B5Result gen_b5_nested_timed_chain(int M) {
    int depth = kB5_depth;
    std::string interval = "[0," + std::to_string(M) + "]";
    std::string core = "p0";
    for (int i = 0; i < depth; ++i) {
        core = "E(true U" + interval + " " + core + ")";
    }
    return {core, depth, M};
}

// Family B6 — Forced delay (SAT): EF[M-1, M] p0.
// Forces the engine to advance time symbolically to at least M-1 before
// satisfying p0.  For M=1, falls back to EF[0, 1] p0.
static std::string gen_b6_forced_delay(int M) {
    int lo = (M >= 2) ? M - 1 : 0;
    return "EF[" + std::to_string(lo) + "," + std::to_string(M) + "] p0";
}

// Family C1: staggered windows — conjunction of EF[i, i+2] p_i
static std::string gen_obligations_staggered(int k) {
    std::string result;
    for (int i = 1; i <= k; ++i) {
        if (i > 1) result += " & ";
        result += "EF[" + std::to_string(i) + "," +
                  std::to_string(i + 2) + "] p" + std::to_string(i);
    }
    return result;
}

// Family C2: overlapping windows — conjunction of EF[1,3] p_i
static std::string gen_obligations_overlapping(int k) {
    std::string result;
    for (int i = 1; i <= k; ++i) {
        if (i > 1) result += " & ";
        result += "EF[1,3] p" + std::to_string(i);
    }
    return result;
}

// Family D: nested timed until — E(true U[1,M] E(true U[1,M] ... p0 ...))
static std::string gen_until_nested(int depth, int M) {
    std::string core = "p0";
    std::string interval = "[1," + std::to_string(M) + "]";
    for (int i = 0; i < depth; ++i) {
        core = "E(true U" + interval + " " + core + ")";
    }
    return core;
}

// Family E: nested timed release — E(false R[1,M] E(false R[1,M] ... p0 ...))
static std::string gen_release_nested(int depth, int M) {
    std::string core = "p0";
    std::string interval = "[1," + std::to_string(M) + "]";
    for (int i = 0; i < depth; ++i) {
        core = "E(false R" + interval + " " + core + ")";
    }
    return core;
}

// Mixed: conjunction of until_nested(n) and release_nested(n)
static std::string gen_mixed(int depth, int M) {
    return "(" + gen_until_nested(depth, M) + ") & (" +
           gen_release_nested(depth, M) + ")";
}

// ── Family F — Zeno rejection (anti-Zeno boundary tests) ───────────────────
//
// These formulas are SAT under Zeno semantics (infinite discrete steps,
// convergent time) but UNSAT under correct non-Zeno / time-divergence
// acceptance.  They stress the anti-Zeno loop check.
//
// Key mechanism: AG[1,M] forces a timed safety obligation with lower
// bound 1 > 0.  The only "satisfying" loops keep time < 1 (Zeno),
// which the engine must reject.
//
// Requires M >= 2 to avoid point-interval [1,1].

// F1: AG[1,M] false — pure Zeno base.
// The only way to avoid falsifying is to never let time reach [1,M].
// Under Zeno: time stays < 1, interval never entered → vacuously SAT.
// Under non-Zeno: time diverges, reaches [1,M], false must hold → UNSAT.
static std::string gen_f1_ag_false(int M) {
    return "AG[1," + std::to_string(M) + "] false";
}

// F2: EG p0 & AG[1,M] !p0 — Zeno EG path.
// EG p0 requires an infinite path with p0 at every state.
// AG[1,M] !p0 requires all paths (including the EG path) to have !p0
// within [1,M].  Under Zeno, the EG path keeps time < 1, so AG is
// vacuously satisfied.  Under non-Zeno, time reaches [1,M], forcing
// both p0 (EG) and !p0 (AG) simultaneously → contradiction → UNSAT.
static std::string gen_f2_eg_conflict(int M) {
    return "EG p0 & AG[1," + std::to_string(M) + "] !p0";
}

// F3: k stacked Zeno traps with existential guard (k = M - 1).
// AG[1,M] !p1 & AG[1,M] !p2 & ... & AG[1,M] !p_k & EG(p1 & ... & p_k)
// Structural growth: as M increases, k grows, adding more clocks and
// atoms.  Each AG obligation allocates a clock; the EG path must keep
// all p_i true, but all AG obligations forbid each p_i within [1,M].
// Under Zeno: loop with all p_i, time < 1 → vacuously SAT.
// Under non-Zeno: reach [1,M], k contradictions → UNSAT.
static std::string gen_f3_stacked_zeno(int M) {
    int k = M - 1;
    if (k < 1) k = 1;
    std::string result;
    for (int i = 1; i <= k; ++i) {
        result += "AG[1," + std::to_string(M) + "] !p" + std::to_string(i);
        result += " & ";
    }
    result += "EG (";
    for (int i = 1; i <= k; ++i) {
        if (i > 1) result += " & ";
        result += "p" + std::to_string(i);
    }
    result += ")";
    return result;
}

// ── Family G — Clock dimensionality (k concurrent clocks) ──────────────────
//
// These formulas force k clocks to be simultaneously active, stressing
// zone operations (DBM dimension = k+1, each operation O(k²)).
// M is kept small (e.g. 5) so the parameter that drives complexity is
// purely the number of concurrent clocks k.

// G1: conjunctive — k staggered EF obligations with fresh atoms.
// EF[1,M] p1 & EF[2,M+1] p2 & ... & EF[k, M+k-1] pk
// Each EF allocates a clock; staggered intervals prevent zone collapse.
// SAT: each obligation can be scheduled independently.
static std::string gen_g1_conjunctive(int k, int M) {
    std::string result;
    for (int i = 1; i <= k; ++i) {
        if (i > 1) result += " & ";
        int lo = i;
        int hi = M + i - 1;
        result += "EF[" + std::to_string(lo) + "," +
                  std::to_string(hi) + "] p" + std::to_string(i);
    }
    return result;
}

// G2: nested — k-deep nested EU preventing early clock deallocation.
// E(true U[1,M] (p1 & E(true U[1,M] (p2 & ... & E(true U[1,M] pk)))))
// All clocks from outer levels remain active while inner levels open
// new clocks.  Fresh atoms per layer prevent zone collapse.  SAT.
static std::string gen_g2_nested(int k, int M) {
    std::string interval = "[1," + std::to_string(M) + "]";
    std::string core = "p" + std::to_string(k);
    for (int i = k - 1; i >= 1; --i) {
        core = "p" + std::to_string(i) + " & E(true U" + interval + " " + core + ")";
    }
    core = "E(true U" + interval + " " + core + ")";
    return core;
}

// G3: killed conjunctive — same as G1 but all atoms are forbidden by AG.
// EF[1,M] p1 & ... & EF[k,M+k-1] pk & AG[0, M+k] (!p1 & ... & !pk)
// Forces k+1 clocks and the engine must refute each individually.  UNSAT.
static std::string gen_g3_killed(int k, int M) {
    std::string result;
    for (int i = 1; i <= k; ++i) {
        if (i > 1) result += " & ";
        int lo = i;
        int hi = M + i - 1;
        result += "EF[" + std::to_string(lo) + "," +
                  std::to_string(hi) + "] p" + std::to_string(i);
    }
    // Killer
    result += " & AG[0," + std::to_string(M + k) + "] (";
    for (int i = 1; i <= k; ++i) {
        if (i > 1) result += " & ";
        result += "!p" + std::to_string(i);
    }
    result += ")";
    return result;
}

// ── Family H — Chained eventualities (formula length n, fixed M) ────────────
//
// Isolates the effect of formula length on tableau cost.  M is held at 2
// (small, fixed), so all growth comes from the number of nested Until
// operators, not from numeric constants.
//
// Each nesting level allocates a fresh clock and a fresh atom;
// the engine must track n independent eventualities simultaneously.

// H1: existential chain (SAT).
// E(p1 U[0,2] E(p2 U[0,2] ... E(pn U[0,2] q)...))
static std::string gen_h1_chain_eu(int n) {
    std::string core = "q";
    for (int i = n; i >= 1; --i) {
        core = "E(p" + std::to_string(i) + " U[0,2] " + core + ")";
    }
    return core;
}

// H2: existential chain + AG killer (UNSAT stress test).
// Same chain as H1, conjoined with AG !q.
// The AG globally prevents q from ever holding, so no EU obligation
// can be fulfilled.  Forces the engine to exhaust the full search
// space (or hit timeout), rather than finding a shallow witness.
static std::string gen_h2_chain_killed(int n) {
    return gen_h1_chain_eu(n) + " & AG !q";
}

// ── Family I — Modality alternation (fixed M=1, fixed clocks) ──────────────
//
// Compares formulas of identical structure depth but with different
// modality nesting.  All use universal (A) quantification and the same
// fixed interval [0,1], so the only variable is whether each layer is
// an Until (least fixpoint, requires eventuality fulfillment) or a
// Release (greatest fixpoint, requires continuous preservation).
//
// I1: pure safety  — n nested AR, no eventualities to track.
// I2: pure liveness — n nested AU, n eventualities must be fulfilled.
// I3: alternating   — Until/Release interleaved, worst-case for loop
//     acceptance because eventualities compete with safety constraints.

// I1: A(p1 R[0,1] A(p2 R[0,1] ... A(pn R[0,1] q)))
static std::string gen_i1_pure_safety(int n) {
    std::string core = "q";
    for (int i = n; i >= 1; --i) {
        core = "A(p" + std::to_string(i) + " R[0,1] " + core + ")";
    }
    return core;
}

// I2: A(p1 U[0,1] A(p2 U[0,1] ... A(pn U[0,1] q)))
static std::string gen_i2_pure_liveness(int n) {
    std::string core = "q";
    for (int i = n; i >= 1; --i) {
        core = "A(p" + std::to_string(i) + " U[0,1] " + core + ")";
    }
    return core;
}

// I3: A(p1 U[0,1] A(p2 R[0,1] A(p3 U[0,1] ... q)))
// Odd layers (1,3,5,...) are Until; even layers (2,4,6,...) are Release.
static std::string gen_i3_alternating(int n) {
    std::string core = "q";
    for (int i = n; i >= 1; --i) {
        const char* op = ((n - i) % 2 == 0) ? "U" : "R";
        core = "A(p" + std::to_string(i) + " " + op + "[0,1] " + core + ")";
    }
    return core;
}

// ── Single-instance runner ──────────────────────────────────────────────────

struct BenchRow {
    std::string family;
    std::string variant;
    std::string param_name;
    int         param_value;
    std::string formula;
    std::string verdict;
    double      elapsed_s;
    int         timeout_s;
    uint32_t    nodes_generated;
    uint32_t    distinct_zones;
    uint32_t    loop_checks;
    uint64_t    seed;
    int         num_threads;
    int         M;
    int         max_const;  // actual max constant in the formula intervals
    int         k;          // -1 = not applicable
    int         depth;      // -1 = not applicable
    std::string abstraction;
};

static void write_csv_header(std::ofstream& f) {
    f << "family,variant,param_name,param_value,formula,verdict,elapsed_s,"
         "timeout_s,nodes_generated,distinct_zones,loop_checks,seed,"
         "num_threads,M,max_const_in_formula,k,depth,abstraction\n";
}

static void write_csv_row(std::ofstream& f, const BenchRow& r) {
    f << csv_esc(r.family) << ","
      << csv_esc(r.variant) << ","
      << csv_esc(r.param_name) << ","
      << r.param_value << ","
      << csv_esc(r.formula) << ","
      << r.verdict << ","
      << std::fixed << std::setprecision(6) << r.elapsed_s << ","
      << r.timeout_s << ","
      << r.nodes_generated << ","
      << r.distinct_zones << ","
      << r.loop_checks << ","
      << r.seed << ","
      << r.num_threads << ","
      << r.M << ","
      << r.max_const << ","
      << r.k << ","
      << r.depth << ","
      << csv_esc(r.abstraction) << "\n";
}

/// Run a single benchmark instance: parse → normalize → check.
/// Performs warmup_runs first (results discarded), then one measured run.
/// @param extrapolation  If false, disables zone extrapolation in the engine.
static BenchRow run_instance(const std::string& family,
                             const std::string& variant,
                             const std::string& param_name,
                             int param_value,
                             const std::string& formula_str,
                             int M_value,
                             const BenchmarkOptions& opt,
                             bool extrapolation = true) {
    BenchRow row;
    row.family      = family;
    row.variant     = variant;
    row.param_name  = param_name;
    row.param_value = param_value;
    row.formula     = formula_str;
    row.timeout_s   = opt.timeout_s;
    row.seed        = opt.seed;
    row.num_threads = opt.num_threads;
    row.M           = M_value;
    row.max_const   = M_value;  // default: caller-provided M
    row.k           = -1;
    row.depth       = -1;
    row.abstraction = extrapolation ? "M" : "none";

    // ── Warmup (not measured) ───────────────────────────────────────────
    for (int w = 0; w < opt.warmup_runs; ++w) {
        try {
            FormulaFactory wf;
            FormulaId parsed = parse_formula(formula_str, wf, 1);
            FormulaId normed = normalize(parsed, wf);
            TableauEngine eng(wf);
            eng.set_timeout(std::chrono::seconds(opt.timeout_s));
            eng.set_extrapolation(extrapolation);
            if (opt.num_threads > 0) eng.set_num_threads(opt.num_threads);
            eng.check(normed);
        } catch (...) {
            // Warmup failure is OK — the measured run will catch it.
        }
    }

    // ── Measured run ────────────────────────────────────────────────────
    try {
        FormulaFactory factory;
        FormulaId parsed = parse_formula(formula_str, factory, 1);
        FormulaId normed = normalize(parsed, factory);

        TableauEngine engine(factory);
        engine.set_timeout(std::chrono::seconds(opt.timeout_s));
        engine.set_extrapolation(extrapolation);
        if (opt.num_threads > 0) engine.set_num_threads(opt.num_threads);

        Result result = engine.check(normed);

        row.verdict         = verdict_str(result.verdict);
        row.elapsed_s       = result.elapsed_s;

        const auto& st      = engine.get_stats();
        row.nodes_generated = st.nodes_created.load();
        row.distinct_zones  = st.distinct_zones.load();
        row.loop_checks     = st.loop_checks.load();

    } catch (const std::exception& e) {
        row.verdict         = "ERROR";
        row.elapsed_s       = 0.0;
        row.nodes_generated = 0;
        row.distinct_zones  = 0;
        row.loop_checks     = 0;
        std::cerr << "  [bench] ERROR on " << family << "/" << variant
                  << " param=" << param_value << ": " << e.what() << "\n";
    }

    return row;
}

// ── Reproducibility file ────────────────────────────────────────────────────

static void write_reproducibility(const std::string& dir,
                                  const BenchmarkOptions& opt,
                                  [[maybe_unused]] int argc_saved,
                                  const std::string& cmdline) {
    std::ofstream f(dir + "/reproducibility.txt");
    if (!f) {
        std::cerr << "[bench] WARNING: could not write reproducibility.txt\n";
        return;
    }

    f << "=== TCTL Benchmark Reproducibility Record ===\n\n";
    f << "timestamp: " << timestamp_readable() << "\n";
    f << "command_line: " << cmdline << "\n\n";

    // Git commit hash
    f << "git_commit: " << shell_capture("git rev-parse --short HEAD 2>/dev/null") << "\n";
    f << "git_dirty: "  << shell_capture("git diff --quiet 2>/dev/null && echo clean || echo dirty") << "\n\n";

    // Compiler
    f << "compiler: " << shell_capture("c++ --version 2>&1 | head -n1") << "\n";
#ifdef __clang_version__
    f << "clang_version: " << __clang_version__ << "\n";
#elif defined(__GNUC__)
    f << "gcc_version: " << __GNUC__ << "." << __GNUC_MINOR__ << "." << __GNUC_PATCHLEVEL__ << "\n";
#endif
    f << "cpp_standard: " << __cplusplus << "\n";

    // Build flags (best effort)
#ifndef NDEBUG
    f << "build_type: Debug (assertions enabled)\n";
#else
    f << "build_type: Release (NDEBUG defined)\n";
#endif
#ifdef TCTL_USE_OPENMP
    f << "openmp: enabled\n";
#else
    f << "openmp: disabled\n";
#endif
    f << "\n";

    // OS info
    f << "uname: " << shell_capture("uname -a") << "\n";

    // CPU info (macOS vs Linux)
#ifdef __APPLE__
    f << "cpu_model: " << shell_capture("sysctl -n machdep.cpu.brand_string 2>/dev/null") << "\n";
    f << "cpu_cores: " << shell_capture("sysctl -n hw.ncpu 2>/dev/null") << "\n";
    f << "ram_total: " << shell_capture("sysctl -n hw.memsize 2>/dev/null | awk '{printf \"%.1f GB\", $1/1073741824}'") << "\n";
#else
    f << "cpu_model: " << shell_capture("grep -m1 'model name' /proc/cpuinfo 2>/dev/null | cut -d: -f2 | xargs") << "\n";
    f << "cpu_cores: " << shell_capture("nproc 2>/dev/null") << "\n";
    f << "ram_total: " << shell_capture("grep MemTotal /proc/meminfo 2>/dev/null | awk '{printf \"%.1f GB\", $2/1048576}'") << "\n";
#endif
    f << "\n";

    // Benchmark configuration
    f << "=== Benchmark Configuration ===\n";
    f << "seed: " << opt.seed << "\n";
    f << "threads: " << opt.num_threads << "\n";
    f << "timeout_per_instance_s: " << opt.timeout_s << "\n";
    f << "warmup_runs: " << opt.warmup_runs << "\n";
    f << "abstraction_mode: " << (opt.abstraction_M_default ? "M" : "none") << "\n";
    f << "run_ablation: " << (opt.run_ablation ? "yes" : "no") << "\n";
    f << "memory_limit: not supported\n";
    f << "\n";

    // Parameter ranges
    f << "=== Parameter Ranges ===\n";
    f << "family_A_depth: 1.." << opt.max_depth << "\n";
    f << "family_B_M_values:";
    for (int v : opt.M_values) f << " " << v;
    f << "\n";
    f << "family_C_k: 1.." << opt.max_k << "\n";
    f << "family_D_until_depth: 1.." << opt.max_until_depth << "\n";
    f << "family_E_release_depth: 1.." << opt.max_until_depth << "\n";
    f << "family_F_zeno_M: 2..16\n";
    f << "family_G_clocks_k: 1..10 (M=5 fixed)\n";
    f << "family_H_chain_n: 1..14 (M=2 fixed)\n";
    f << "family_I_alternation_n: 1..14 (M=1 fixed)\n";
    f << "\n";

    if (!opt.out_dir_override.empty()) {
        f << "output_dir_override: " << opt.out_dir_override << "\n";
    }

    f.close();
}

// ── Main entry point ────────────────────────────────────────────────────────

int run_benchmarks(const BenchmarkOptions& opt) {
    // ── Create output directory ─────────────────────────────────────────
    std::string out_dir;
    if (!opt.out_dir_override.empty()) {
        out_dir = opt.out_dir_override;
    } else {
        out_dir = "benchmark_result_" + timestamp_string();
    }
    std::filesystem::create_directories(out_dir);
    std::cout << "[benchmark] Writing results to: " << out_dir << "/\n";

    // ── Reconstruct command line (best effort) ──────────────────────────
    std::ostringstream cmdline;
    cmdline << "--benchmark";
    if (opt.timeout_s != 30)   cmdline << " --bench-timeout " << opt.timeout_s;
    if (opt.seed != 1337)      cmdline << " --bench-seed " << opt.seed;
    if (opt.num_threads != 1)  cmdline << " --bench-threads " << opt.num_threads;
    if (opt.max_depth != 14)   cmdline << " --bench-max-depth " << opt.max_depth;
    if (opt.max_k != 16)       cmdline << " --bench-max-k " << opt.max_k;
    if (!opt.run_ablation)     cmdline << " --bench-no-ablation";
    if (!opt.out_dir_override.empty()) cmdline << " --bench-out " << opt.out_dir_override;

    // ── Write reproducibility ───────────────────────────────────────────
    write_reproducibility(out_dir, opt, 0, cmdline.str());
    std::cout << "[benchmark] Wrote reproducibility.txt\n";

    int total_instances = 0;
    int timeouts = 0;
    int errors = 0;

    // ================================================================
    // Family A — Depth / formula-size curves
    // ================================================================
    {
        std::ofstream csv(out_dir + "/curves_depth.csv");
        write_csv_header(csv);

        std::cout << "[benchmark] Family A: depth curves (1.." << opt.max_depth << ")\n";

        for (int d = 1; d <= opt.max_depth; ++d) {
            // A1: untimed alternation (baseline, no clocks)
            {
                std::string formula = gen_depth_untimed(d);
                std::cout << "  A1 depth=" << d << " ... " << std::flush;
                BenchRow row = run_instance("A_depth", "A1_untimed",
                                            "depth", d, formula, 0, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // A2: overlapping timed obligations (SAT, d clocks, M=10)
            {
                std::string formula = gen_a2_overlap_sat(d, 10);
                std::cout << "  A2 depth=" << d << " ... " << std::flush;
                BenchRow row = run_instance("A_depth", "A2_overlap_sat",
                                            "depth", d, formula, 10, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // A3: nested EU with fresh atoms per layer (SAT, d clocks)
            {
                std::string formula = gen_a3_nested_eu(d, 10);
                std::cout << "  A3 depth=" << d << " ... " << std::flush;
                BenchRow row = run_instance("A_depth", "A3_nested_eu",
                                            "depth", d, formula, 10, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // A4: killed obligations (UNSAT, d+1 clocks)
            {
                std::string formula = gen_a4_killed_unsat(d, 10);
                std::cout << "  A4 depth=" << d << " ... " << std::flush;
                BenchRow row = run_instance("A_depth", "A4_killed_unsat",
                                            "depth", d, formula, 10, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }
        }
        csv.close();
        std::cout << "[benchmark] Wrote curves_depth.csv\n";
    }

    // ================================================================
    // Family B — Max constant M curves (hard variants)
    // ================================================================
    {
        std::ofstream csv(out_dir + "/curves_bounds_M.csv");
        write_csv_header(csv);

        std::cout << "[benchmark] Family B: M curves (" << opt.M_values.size()
                  << " values, 7 variants)\n";

        // Track scaling variant metrics for validation guard.
        std::vector<uint32_t> b4_nodes, b5_nodes, b6_noextr_nodes;

        for (int M : opt.M_values) {
            // B1: EU delay — E((!p0) U[0,M] p0)  (SAT, forces time progress)
            {
                std::string formula = gen_b1_eu_delay(M);
                std::cout << "  B1_EU_delay M=" << M << " ... " << std::flush;
                BenchRow row = run_instance("B_bounds_M", "B1_EU_delay",
                                            "M", M, formula, M, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // B2: Deadline UNSAT — AG[0,M] !p0 & EF[1,M] p0
            {
                std::string formula = gen_b2_deadline_unsat(M);
                std::cout << "  B2_deadline M=" << M << " ... " << std::flush;
                BenchRow row = run_instance("B_bounds_M", "B2_deadline_unsat",
                                            "M", M, formula, M, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // B3: Negated window UNSAT — EF[0,M] p0 & !EF[0,M] p0
            {
                std::string formula = gen_b3_negated_window(M);
                std::cout << "  B3_negated M=" << M << " ... " << std::flush;
                BenchRow row = run_instance("B_bounds_M", "B3_negated_window",
                                            "M", M, formula, M, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // B4: chain-of-windows — fixed k=5, step=M/5, max_const≈M
            {
                auto [formula, k, max_const] = gen_b4_chain_windows(M);
                std::cout << "  B4_chain_windows M=" << M << " k=" << k
                          << " max_const=" << max_const
                          << " ... " << std::flush;
                BenchRow row = run_instance("B_bounds_M", "B4_chain_windows",
                                            "M", M, formula, max_const, opt);
                row.k         = k;
                row.max_const = max_const;
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes, "
                          << row.distinct_zones << " zones)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
                b4_nodes.push_back(row.nodes_generated);
            }

            // B5: nested timed chain — fixed depth=6, interval [0,M]
            {
                auto [formula, depth, max_const] = gen_b5_nested_timed_chain(M);
                std::cout << "  B5_nested_chain M=" << M << " depth=" << depth
                          << " max_const=" << max_const
                          << " ... " << std::flush;
                BenchRow row = run_instance("B_bounds_M", "B5_nested_chain",
                                            "M", M, formula, max_const, opt);
                row.depth     = depth;
                row.max_const = max_const;
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes, "
                          << row.distinct_zones << " zones)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
                b5_nodes.push_back(row.nodes_generated);
            }

            // B6: forced delay — EF[M-1, M] p0 (with extrapolation ON)
            {
                std::string formula = gen_b6_forced_delay(M);
                std::cout << "  B6_forced_delay M=" << M
                          << " (extrap=ON) ... " << std::flush;
                BenchRow row = run_instance("B_bounds_M", "B6_forced_delay",
                                            "M", M, formula, M, opt,
                                            /*extrapolation=*/true);
                row.max_const = M;
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes, "
                          << row.distinct_zones << " zones)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // B6_noextr: forced delay — same formula, extrapolation OFF
            {
                std::string formula = gen_b6_forced_delay(M);
                std::cout << "  B6_forced_delay M=" << M
                          << " (extrap=OFF) ... " << std::flush;
                BenchRow row = run_instance("B_bounds_M",
                                            "B6_forced_delay_noextr",
                                            "M", M, formula, M, opt,
                                            /*extrapolation=*/false);
                row.max_const = M;
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes, "
                          << row.distinct_zones << " zones)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
                b6_noextr_nodes.push_back(row.nodes_generated);
            }
        }
        csv.close();

        // ── Validation guard: warn if scaling variants produced flat metrics ──
        auto all_identical = [](const std::vector<uint32_t>& v) -> bool {
            return v.size() > 1 &&
                   std::all_of(v.begin() + 1, v.end(),
                               [&](uint32_t x) { return x == v[0]; });
        };
        if (all_identical(b4_nodes)) {
            std::cerr << "[bench] WARNING: B4_chain_windows has FLAT "
                         "nodes_generated across all M values.\n"
                         "  Zone abstraction may be neutralising the M "
                         "parameter. Consider reducing \u0394_B4.\n";
        }
        if (all_identical(b5_nodes)) {
            std::cerr << "[bench] WARNING: B5_nested_chain has FLAT "
                         "nodes_generated across all M values.\n"
                         "  Zone abstraction may be neutralising the M "
                         "parameter. Consider reducing \u0394_B5.\n";
        }
        if (all_identical(b6_noextr_nodes)) {
            std::cerr << "[bench] WARNING: B6_forced_delay_noextr has FLAT "
                         "nodes_generated across all M values.\n"
                         "  The forced-delay formula may not be exercising "
                         "the zone engine as expected.\n";
        }

        std::cout << "[benchmark] Wrote curves_bounds_M.csv\n";
    }

    // ================================================================
    // Family C — Timed obligations / clock pressure
    // ================================================================
    {
        std::ofstream csv(out_dir + "/curves_obligations.csv");
        write_csv_header(csv);

        std::cout << "[benchmark] Family C: obligations (k=1.." << opt.max_k
                  << ")\n";

        for (int k = 1; k <= opt.max_k; ++k) {
            // C1: staggered windows
            {
                std::string formula = gen_obligations_staggered(k);
                std::cout << "  C1 k=" << k << " ... " << std::flush;
                // M is max upper bound = k+2
                BenchRow row = run_instance("C_obligations", "C1_staggered",
                                            "k", k, formula, k + 2, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // C2: overlapping windows
            {
                std::string formula = gen_obligations_overlapping(k);
                std::cout << "  C2 k=" << k << " ... " << std::flush;
                BenchRow row = run_instance("C_obligations", "C2_overlapping",
                                            "k", k, formula, 3, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }
        }
        csv.close();
        std::cout << "[benchmark] Wrote curves_obligations.csv\n";
    }

    // ================================================================
    // Families D + E — Until / Release / Mixed
    // ================================================================
    {
        std::ofstream csv(out_dir + "/curves_until_release_mixed.csv");
        write_csv_header(csv);

        std::cout << "[benchmark] Family D: nested until (u=1.."
                  << opt.max_until_depth << ")\n";

        for (int u = 1; u <= opt.max_until_depth; ++u) {
            // D: nested timed until
            {
                std::string formula = gen_until_nested(u, 10);
                std::cout << "  D u=" << u << " ... " << std::flush;
                BenchRow row = run_instance("D_until", "until_nested",
                                            "until_depth", u, formula, 10, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // D optional: conjunctive untils
            if (u <= 6) {
                std::string formula;
                for (int i = 1; i <= u; ++i) {
                    if (i > 1) formula += " & ";
                    formula += "E(true U[1,10] p" + std::to_string(i) + ")";
                }
                std::cout << "  D_conj u=" << u << " ... " << std::flush;
                BenchRow row = run_instance("D_until", "until_conjunctive",
                                            "until_depth", u, formula, 10, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }
        }

        std::cout << "[benchmark] Family E: nested release (r=1.."
                  << opt.max_until_depth << ")\n";

        for (int r = 1; r <= opt.max_until_depth; ++r) {
            // E: nested timed release
            {
                std::string formula = gen_release_nested(r, 10);
                std::cout << "  E r=" << r << " ... " << std::flush;
                BenchRow row = run_instance("E_release", "release_nested",
                                            "release_depth", r, formula, 10, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }
        }

        // Mixed variant
        std::cout << "[benchmark] Mixed: until+release (n=1.."
                  << opt.max_until_depth << ")\n";

        for (int n = 1; n <= opt.max_until_depth; ++n) {
            std::string formula = gen_mixed(n, 10);
            std::cout << "  Mixed n=" << n << " ... " << std::flush;
            BenchRow row = run_instance("DE_mixed", "mixed",
                                        "depth", n, formula, 10, opt);
            write_csv_row(csv, row);
            std::cout << row.verdict << " (" << std::fixed
                      << std::setprecision(3) << row.elapsed_s << "s)\n";
            ++total_instances;
            if (row.verdict == "TIMEOUT") ++timeouts;
            if (row.verdict == "ERROR")   ++errors;
        }

        csv.close();
        std::cout << "[benchmark] Wrote curves_until_release_mixed.csv\n";
    }

    // ================================================================
    // Family F — Zeno rejection (anti-Zeno boundary tests)
    // ================================================================
    {
        std::ofstream csv(out_dir + "/curves_zeno.csv");
        write_csv_header(csv);

        // M ranges from 2..16 (M=1 would create point interval [1,1]).
        constexpr int kZenoM_lo = 2;
        constexpr int kZenoM_hi = 16;

        std::cout << "[benchmark] Family F: Zeno rejection (M="
                  << kZenoM_lo << ".." << kZenoM_hi << ", 3 variants)\n";

        for (int M = kZenoM_lo; M <= kZenoM_hi; ++M) {
            // F1: AG[1,M] false — pure Zeno base
            {
                std::string formula = gen_f1_ag_false(M);
                std::cout << "  F1_ag_false M=" << M << " ... " << std::flush;
                BenchRow row = run_instance("F_zeno", "F1_ag_false",
                                            "M", M, formula, M, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // F2: EG p0 & AG[1,M] !p0 — Zeno EG conflict
            {
                std::string formula = gen_f2_eg_conflict(M);
                std::cout << "  F2_eg_conflict M=" << M << " ... " << std::flush;
                BenchRow row = run_instance("F_zeno", "F2_eg_conflict",
                                            "M", M, formula, M, opt);
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // F3: stacked Zeno traps (k=M-1 obligations)
            {
                int k = M - 1;
                std::string formula = gen_f3_stacked_zeno(M);
                std::cout << "  F3_stacked M=" << M << " k=" << k
                          << " ... " << std::flush;
                BenchRow row = run_instance("F_zeno", "F3_stacked_zeno",
                                            "M", M, formula, M, opt);
                row.k = k;
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes, "
                          << row.distinct_zones << " zones)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }
        }
        csv.close();
        std::cout << "[benchmark] Wrote curves_zeno.csv\n";
    }

    // ================================================================
    // Family G — Clock dimensionality (k concurrent clocks)
    // ================================================================
    {
        std::ofstream csv(out_dir + "/curves_clocks.csv");
        write_csv_header(csv);

        constexpr int kClockM   = 5;   // small fixed M
        constexpr int kClockMax = 10;   // k = 1..10

        std::cout << "[benchmark] Family G: clock dimensionality (k=1.."
                  << kClockMax << ", M=" << kClockM << ", 3 variants)\n";

        for (int k = 1; k <= kClockMax; ++k) {
            // G1: conjunctive — k staggered EF, SAT
            {
                std::string formula = gen_g1_conjunctive(k, kClockM);
                int max_const = kClockM + k - 1;
                std::cout << "  G1_conjunctive k=" << k
                          << " ... " << std::flush;
                BenchRow row = run_instance("G_clocks", "G1_conjunctive",
                                            "k", k, formula, max_const, opt);
                row.k         = k;
                row.max_const = max_const;
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes, "
                          << row.distinct_zones << " zones)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // G2: nested — k-deep nested EU, SAT
            {
                std::string formula = gen_g2_nested(k, kClockM);
                std::cout << "  G2_nested k=" << k
                          << " ... " << std::flush;
                BenchRow row = run_instance("G_clocks", "G2_nested",
                                            "k", k, formula, kClockM, opt);
                row.k     = k;
                row.depth = k;
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes, "
                          << row.distinct_zones << " zones)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // G3: killed conjunctive — same as G1 + AG killer, UNSAT
            {
                std::string formula = gen_g3_killed(k, kClockM);
                int max_const = kClockM + k;
                std::cout << "  G3_killed k=" << k
                          << " ... " << std::flush;
                BenchRow row = run_instance("G_clocks", "G3_killed",
                                            "k", k, formula, max_const, opt);
                row.k         = k;
                row.max_const = max_const;
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes, "
                          << row.distinct_zones << " zones)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }
        }
        csv.close();
        std::cout << "[benchmark] Wrote curves_clocks.csv\n";
    }

    // ================================================================
    // Family H — Chained eventualities (formula length n, fixed M=2)
    // ================================================================
    {
        std::ofstream csv(out_dir + "/curves_chain.csv");
        write_csv_header(csv);

        constexpr int kChainMax = 14;  // n = 1..14

        std::cout << "[benchmark] Family H: chained eventualities (n=1.."
                  << kChainMax << ", M=2, 2 variants)\n";

        for (int n = 1; n <= kChainMax; ++n) {
            // H1: existential chain (SAT)
            {
                std::string formula = gen_h1_chain_eu(n);
                std::cout << "  H1_chain_eu n=" << n << " ... " << std::flush;
                BenchRow row = run_instance("H_chain", "H1_chain_eu",
                                            "n", n, formula, 2, opt);
                row.depth = n;
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes, "
                          << row.distinct_zones << " zones)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // H2: chain + AG killer (UNSAT)
            {
                std::string formula = gen_h2_chain_killed(n);
                std::cout << "  H2_chain_killed n=" << n << " ... " << std::flush;
                BenchRow row = run_instance("H_chain", "H2_chain_killed",
                                            "n", n, formula, 2, opt);
                row.depth = n;
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes, "
                          << row.distinct_zones << " zones)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }
        }
        csv.close();
        std::cout << "[benchmark] Wrote curves_chain.csv\n";
    }

    // ================================================================
    // Family I — Modality alternation (fixed M=1, depth n)
    // ================================================================
    {
        std::ofstream csv(out_dir + "/curves_alternation.csv");
        write_csv_header(csv);

        constexpr int kAltMax = 14;  // n = 1..14

        std::cout << "[benchmark] Family I: modality alternation (n=1.."
                  << kAltMax << ", M=1, 3 variants)\n";

        for (int n = 1; n <= kAltMax; ++n) {
            // I1: pure safety — nested AR
            {
                std::string formula = gen_i1_pure_safety(n);
                std::cout << "  I1_safety n=" << n << " ... " << std::flush;
                BenchRow row = run_instance("I_alternation", "I1_pure_safety",
                                            "n", n, formula, 1, opt);
                row.depth = n;
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes, "
                          << row.distinct_zones << " zones)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // I2: pure liveness — nested AU
            {
                std::string formula = gen_i2_pure_liveness(n);
                std::cout << "  I2_liveness n=" << n << " ... " << std::flush;
                BenchRow row = run_instance("I_alternation", "I2_pure_liveness",
                                            "n", n, formula, 1, opt);
                row.depth = n;
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes, "
                          << row.distinct_zones << " zones)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }

            // I3: alternating fixpoint — Until/Release interleaved
            {
                std::string formula = gen_i3_alternating(n);
                std::cout << "  I3_alternating n=" << n << " ... " << std::flush;
                BenchRow row = run_instance("I_alternation", "I3_alternating",
                                            "n", n, formula, 1, opt);
                row.depth = n;
                write_csv_row(csv, row);
                std::cout << row.verdict << " (" << std::fixed
                          << std::setprecision(3) << row.elapsed_s << "s, "
                          << row.nodes_generated << " nodes, "
                          << row.distinct_zones << " zones)\n";
                ++total_instances;
                if (row.verdict == "TIMEOUT") ++timeouts;
                if (row.verdict == "ERROR")   ++errors;
            }
        }
        csv.close();
        std::cout << "[benchmark] Wrote curves_alternation.csv\n";
    }

    // ── Summary ─────────────────────────────────────────────────────────
    std::cout << "\n[benchmark] Done. " << total_instances << " instances, "
              << timeouts << " timeouts, " << errors << " errors.\n";
    std::cout << "[benchmark] Results in: " << out_dir << "/\n";

    return errors > 0 ? 1 : 0;
}

}  // namespace tctl
