// ============================================================================
// cli.cpp — Command-line interface and main driver
// ============================================================================

#include "tctl/cli.hpp"
#include "tctl/ast.hpp"
#include "tctl/benchmark.hpp"
#include "tctl/lexer.hpp"
#include "tctl/normalization.hpp"
#include "tctl/paper_tableau.hpp"
#include "tctl/parser.hpp"
#include "tctl/test.hpp"
#include "tctl/utils.hpp"
#include "tctl/z3_solver.hpp"

#include <ctime>
#include <filesystem>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace tctl {

// ── parse_args ──────────────────────────────────────────────────────────────

Options parse_args(int argc, char* argv[]) {
    Options opts;

    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];

        if (arg == "--selftest") {
            opts.selftest = true;
        } else if (arg == "--benchmark") {
            opts.benchmark = true;
        } else if (arg == "--bench-timeout") {
            if (i + 1 >= argc) throw std::runtime_error("--bench-timeout requires a number");
            opts.bench_opts.timeout_s = std::stoi(argv[++i]);
        } else if (arg == "--bench-seed") {
            if (i + 1 >= argc) throw std::runtime_error("--bench-seed requires a number");
            opts.bench_opts.seed = std::stoull(argv[++i]);
        } else if (arg == "--bench-threads") {
            if (i + 1 >= argc) throw std::runtime_error("--bench-threads requires a number");
            opts.bench_opts.num_threads = std::stoi(argv[++i]);
        } else if (arg == "--bench-max-depth") {
            if (i + 1 >= argc) throw std::runtime_error("--bench-max-depth requires a number");
            opts.bench_opts.max_depth = std::stoi(argv[++i]);
        } else if (arg == "--bench-max-k") {
            if (i + 1 >= argc) throw std::runtime_error("--bench-max-k requires a number");
            opts.bench_opts.max_k = std::stoi(argv[++i]);
        } else if (arg == "--bench-out") {
            if (i + 1 >= argc) throw std::runtime_error("--bench-out requires a directory");
            opts.bench_opts.out_dir_override = argv[++i];
        } else if (arg == "--bench-no-ablation") {
            opts.bench_opts.run_ablation = false;
        } else if (arg == "--bench-abstraction") {
            if (i + 1 >= argc) throw std::runtime_error("--bench-abstraction requires M|none|both");
            std::string mode = argv[++i];
            if (mode == "none") opts.bench_opts.abstraction_M_default = false;
            else if (mode == "M" || mode == "both") opts.bench_opts.abstraction_M_default = true;
            else throw std::runtime_error("--bench-abstraction must be M, none, or both");
        } else if (arg == "--model" || arg == "--show-model") {
            opts.show_model = true;
        } else if (arg == "--stats" || arg == "--show-stats") {
            opts.show_stats = true;
        } else if (arg == "--real-vars") {
            if (i + 1 >= argc) {
                throw std::runtime_error("--real-vars requires a comma-separated list");
            }
            std::string list = argv[++i];
            std::vector<std::string> names;
            std::string cur;
            for (char c : list) {
                if (c == ',') { if (!cur.empty()) names.push_back(cur); cur.clear(); }
                else if (c != ' ') cur.push_back(c);
            }
            if (!cur.empty()) names.push_back(cur);
            set_real_vars(names);
        } else if (arg == "--help" || arg == "-h") {
            opts.help = true;
        } else if (arg == "--output") {
            if (i + 1 >= argc) {
                throw std::runtime_error("--output requires a directory argument");
            }
            std::string dir = argv[++i];
            if (!std::filesystem::exists(dir)) {
                std::filesystem::create_directories(dir);
            } else {
                std::string timestamp = std::to_string(std::time(nullptr));
                dir += "_" + timestamp;
                std::filesystem::create_directories(dir);
            }
            if (!std::filesystem::is_directory(dir)) {
                throw std::runtime_error("output path is not a directory: " + dir);
            }
            std::filesystem::current_path(dir);
        } else if (arg == "--tot" || arg == "all_formula" || arg == "all") {
            opts.tot = true;
        } else if (arg.starts_with("-")) {
            throw std::runtime_error("unknown option: " + arg);
        } else {
            if (!opts.input.empty()) {
                throw std::runtime_error("multiple input files not supported");
            }
            opts.input = arg;
        }
    }

    // Validate: need either --selftest, --benchmark, or an input file.
    if (!opts.selftest && !opts.benchmark && !opts.help && opts.input.empty()) {
        throw std::runtime_error("no input file specified (use --help for usage)");
    }

    return opts;
}

// ── print_usage ─────────────────────────────────────────────────────────────

void print_usage(const char* program_name) {
    std::cerr
        << "Usage: " << program_name << " [OPTIONS] <input.txt>\n"
        << "       " << program_name << " --selftest\n"
        << "       " << program_name << " --benchmark [bench-options]\n"
        << "\n"
        << "TCTL satisfiability checker (ETAPS2026 tableau).\n"
        << "\n"
        << "Options:\n"
        << "  <Formula> | <input.txt>  A TCTL formula, or a file with one per line\n"
        << "  --selftest    Run the built-in semantic self-test suite\n"
        << "  --benchmark   Run benchmark suites (writes CSVs + reproducibility)\n"
        << "  --stats, --show-stats   Show engine statistics\n"
        << "  --model, --show-model   Extract witness Timed Automaton (pending)\n"
        << "  --output <dir>  Directory to write extracted models (default: current)\n"
        << "  --real-vars a,b Declare variable names as Real-sorted (else Int)\n"
        << "  --tot, --all, --all_formula  Conjoin all input formulas and check as one\n"
        << "  --help, -h    Show this message\n"
        << "\n"
        << "Benchmark options (use with --benchmark):\n"
        << "  --bench-timeout <sec>     Per-instance timeout (default: 30)\n"
        << "  --bench-seed <int>        Random seed (default: 1337)\n"
        << "  --bench-threads <n>       Number of threads (default: 1)\n"
        << "  --bench-max-depth <n>     Family A max depth (default: 14)\n"
        << "  --bench-max-k <n>         Family C max k (default: 16)\n"
        << "  --bench-out <dir>         Output directory (default: auto-timestamped)\n"
        << "  --bench-no-ablation       Disable ablation runs\n"
        << "  --bench-abstraction <M|none|both>  Abstraction mode (default: M)\n"
        << "\n"
        << "Input format:\n"
        << "  - One formula per line\n"
        << "  - Empty lines and lines starting with # are ignored\n"
        << "  - Inline comments: everything after # is ignored\n";
}

// ── run ─────────────────────────────────────────────────────────────────────
// Main driver loop.  Reads the input file, processes each formula line,
// prints results.

int run(const Options& opts) {
    if (opts.selftest) {
        return run_selftests();
    }
    if (opts.benchmark) {
        return run_benchmarks(opts.bench_opts);
    }

    if (opts.input.empty()) {
        std::cerr << "ERROR: no input specified (use --help for usage)\n";
        return 1;
    }

    std::vector<std::string> formulas;
    bool is_file = opts.input.ends_with(".txt");
    // If it ends with .txt assume a file; otherwise treat as a single formula.
    if (is_file) {
        std::vector<std::string> temp;
        try {
            temp = read_lines(opts.input);
        } catch (const std::exception& e) {
            std::cerr << "ERROR: " << e.what() << "\n";
            return 1;
        }
        if (opts.tot) {
            std::string combined;
            for (const auto& line : temp) {
                std::string content = strip_comment(line);
                if (!content.empty()) {
                    if (!combined.empty()) combined += " & ";
                    combined += "(" + content + ")";
                }
            }
            formulas.clear();
            formulas.push_back(combined);
        } else {
            formulas = std::move(temp);
        }
    } else {
        formulas.push_back(opts.input);
    }

    FormulaFactory factory;
    PaperTableau engine(factory);
    bool had_errors = false;

    for (std::size_t i = 0; i < formulas.size(); ++i) {
        std::uint32_t line_num = static_cast<std::uint32_t>(i + 1);
        std::string content = strip_comment(formulas[i]);
        if (content.empty()) continue;  // blank / comment-only

        try {
            // Parse → normalise (desugar → eliminate implications → NNF).
            FormulaId parsed = parse_formula(content, factory, line_num);
            FormulaId normalised = normalize(parsed, factory);

            // Warn when the input leaves the fragment the procedure is complete
            // for: a punctual interval nested inside another timed modality
            // (timed-nesting depth > 1) is sound and terminating but may be
            // incomplete.
            PunctualityReport pr = analyze_punctuality(normalised, factory);
            if (pr.punctual_nested) {
                std::cerr << line_num << ": warning: punctual interval [a,a] nested "
                             "inside another timed modality (timed-nesting depth > 1). "
                             "The procedure stays SOUND and TERMINATING but is not "
                             "guaranteed COMPLETE here: a SATISFIABLE verdict is "
                             "reliable (a witness exists), an UNSATISFIABLE verdict "
                             "may be a false negative.\n";
            }

            Result result = engine.check(normalised);
            std::cout << line_num << ": " << result_to_string(result) << "\n";

            if (opts.show_stats) {
                std::cout << "  Stats: " << engine.stats() << "\n";
            }
            if (opts.show_model && result == Result::Satisfiable) {
                std::cerr << "  note: witness Timed Automaton extraction is not yet "
                             "implemented (verdict-first build).\n";
            }
        } catch (const std::exception& e) {
            // Parser error messages already include line/column.
            std::cerr << e.what() << "\n";
            had_errors = true;
        }
    }

    return had_errors ? 1 : 0;
}

}  // namespace tctl
