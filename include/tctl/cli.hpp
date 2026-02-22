// ============================================================================
// tctl/cli.hpp — Command-line interface handling
// ============================================================================
//
// Parses argv into a structured Options object and provides the main
// driver loop: read input file → parse → normalise → run tableau stub.
//
// ============================================================================

#ifndef CTL_CLI_HPP
#define CTL_CLI_HPP

#include <string>
#include <vector>

namespace tctl {

// ── Options ─────────────────────────────────────────────────────────────────

struct Options {
    std::string input;   // path to the input (empty if --selftest)
    bool        selftest = false;
    bool        show_model = false;
    bool        show_stats = false;
    bool        help = false;
    bool        tot = false; // conjoin all formulas in the input with AND and check as one formula
    int         num_threads = 0; // OpenMP threads (0 = default)
};

/// Parse command-line arguments.  Throws std::runtime_error on bad usage.
Options parse_args(int argc, char* argv[]);

/// Print usage information to stderr.
void print_usage(const char* program_name);

/// Main driver: read file, process formulas, print results.
/// Returns the process exit code (0 = ok, 1 = errors encountered).
int run(const Options& opts);

}  // namespace tctl

#endif  // CTL_CLI_HPP
