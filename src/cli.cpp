// ============================================================================
// cli.cpp — Command-line interface and main driver
// ============================================================================

#include "tctl/cli.hpp"
#include "tctl/ast.hpp"
#include "tctl/benchmark.hpp"
#include "tctl/lexer.hpp"
#include "tctl/normalization.hpp"
#include "tctl/parser.hpp"
#include "tctl/tableau.hpp"
#include "tctl/test.hpp"
#include "tctl/timed_automaton.hpp"
#include "tctl/utils.hpp"

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>

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
        } else if (arg == "--model") {
            opts.show_model = true;
        } else if (arg == "--stats") {
            opts.show_stats = true;
        } else if (arg == "--help" || arg == "-h") {
            opts.help = true;
        } else if (arg == "--output") {
            if (i + 1 >= argc) {
                throw std::runtime_error("--output requires a directory argument");
            }
            std::string dir = argv[++i];
            if (!std::filesystem::exists(dir)) {
                //throw std::runtime_error("output directory does not exist: " + dir);
                std::filesystem::create_directories(dir);
            }else {
                // create directory by appending timestamp if it already exists
                std::string timestamp = std::to_string(std::time(nullptr));
                dir += "_" + timestamp;
                std::filesystem::create_directories(dir);
            }
            if (!std::filesystem::is_directory(dir)) {
                throw std::runtime_error("output path is not a directory: " + dir);
            }
            std::filesystem::current_path(dir);
        } else if (arg == "--tot" || arg== "all_formula" || arg == "all"){
            opts.tot = true;

        } else if (arg == "--threads" || arg == "-j") {
            if (i + 1 >= argc) {
                throw std::runtime_error("--threads requires a number argument");
            }
            opts.num_threads = std::stoi(argv[++i]);
            if (opts.num_threads < 0) {
                throw std::runtime_error("--threads must be >= 0");
            }

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
        << "tctl satisfiability checker.\n"
        << "\n"
        << "Options:\n"
        << "  <Formula> | <input.txt>  Formula or  File with one tctl formula per line\n"
        << "  --selftest    Run built-in tests\n"
        << "  --benchmark   Run benchmark suites (writes CSVs + reproducibility)\n"
        << "  --model       Extract Timed Automaton (UPPAAL style)\n"
        << "  --output <dir>  Directory to write extracted models (default: current)\n"
        << "  --stats       Show engine statistics\n"
        << "  --help, -h    Show this message\n"
        << "  --tot, --all, --all_formula  Conjoin all formulas in the input with AND and check as one formula\n"
        << "  --threads N, -j N  Set number of OpenMP threads (0 = auto, default)\n"
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
    // ── Handle --selftest ───────────────────────────────────────────────
    if (opts.selftest) {
        return run_selftests();
    }

    // ── Handle --benchmark ──────────────────────────────────────────────
    if (opts.benchmark) {
        return run_benchmarks(opts.bench_opts);
    }

    // ── Read input file ─────────────────────────────────────────────────

    
    if (opts.input.empty()) {
        std::cerr << "ERROR: no input specified (use --help for usage)\n";
        return 1;
    }

    std::vector<std::string> formulas;
    std::string stem;
    bool is_file = opts.input.ends_with(".txt");
    //if it ends with .txt assume text file input, otherwise treat it as a single formula
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
                    if (!combined.empty()) {
                        combined += " & ";
                    }
                    combined += "(" + content + ")";
                }
            }
            formulas.clear();
            formulas.push_back(combined);
        }else{
            formulas = std::move(temp);
        }

        stem =std::filesystem::path(opts.input).stem().string();
    }
    else {
        formulas.push_back(opts.input);
        // name is formula + timestamp to avoid collisions when using --output with multiple formulas
        stem = "formula_" + std::to_string(std::time(nullptr));
    }

    

        

    

    // ── Process each line ───────────────────────────────────────────────
    FormulaFactory factory;
    TableauEngine engine(factory);
    engine.set_extract_model(opts.show_model);
    if (opts.num_threads > 0) engine.set_num_threads(opts.num_threads);
    bool had_errors = false;

    

    for (std::size_t i = 0; i < formulas.size(); ++i) {
        std::uint32_t line_num = static_cast<std::uint32_t>(i + 1);
        std::string content = strip_comment(formulas[i]);

        // Skip blank / comment-only lines.
        if (content.empty()) {
            continue;
        }

        try {
            // Parse the formula.
            FormulaId parsed = parse_formula(content, factory, line_num);

            // Normalise: desugar → eliminate implications → NNF.
            FormulaId normalised = normalize(parsed, factory);

            // Run the tableau stub.
            Result result = engine.check(normalised);

            // Print result.
            std::cout << line_num << ": " << result_to_string(result) << "\n";

            // Optional: show stats.
            if (opts.show_stats) {
                std::cout << "  Stats: " << engine.stats() << "\n";
            }

            // Optional: extract Timed Automaton (--model).
            if (opts.show_model && result == Result::Satisfiable) {
                TimedAutomaton ta = build_from_tableau(engine);
                std::cout << "\n" << ta.to_string() << "\n";

                
                std::string base;
                if (is_file && !opts.tot) {
                    //create one folder per line
                    std::filesystem::create_directories("line_" + std::to_string(line_num));
                    base= "line_" + std::to_string(line_num) + "/" + stem;
                } else {
                    base = stem + "_ta";
                }

                // JSON
                {
                    std::string path = base + ".json";
                    std::ofstream f(path);
                    f << ta.to_json();
                    std::cout << "  TA JSON : " << path << "\n";
                }
                // UPPAAL XML
                {
                    std::string path = base + ".xml";
                    std::ofstream f(path);
                    f << ta.to_uppaal_xml();
                    std::cout << "  TA XML  : " << path << "\n";
                }
                // DOT → PNG
                {
                    std::string dot_path = base + ".dot";
                    std::string png_path = base + ".png";
                    {
                        std::ofstream f(dot_path);
                        f << ta.to_dot();
                    }
                    std::string cmd =
                        "dot -Tpng \"" + dot_path + "\" -o \"" + png_path + "\" 2>/dev/null";
                    int rc = std::system(cmd.c_str());
                    if (rc == 0) {
                        std::filesystem::remove(dot_path);
                        std::cout << "  TA PNG  : " << png_path << "\n";
                    } else {
                        std::cout << "  TA DOT  : " << dot_path << "\n";
                    }
                }
            }

        } catch (const std::exception& e) {
            // Error messages from the parser already include line/column.
            std::cerr << e.what() << "\n";
            had_errors = true;
        }
    }

    return had_errors ? 1 : 0;
}

}  // namespace tctl
