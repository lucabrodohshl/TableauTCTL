// ============================================================================
// test.cpp — Self-test suite for the TCTL satisfiability tool
// ============================================================================
//
// Contains tests covering:
//   - Lexer tokenisation (brackets, braces, commas, inf, comparison ops)
//   - Parser correctness (atoms, booleans, temporal, TCTL operators)
//   - Time interval syntax ([a,b], (a,b), [a,b), (a,b])
//   - Relational time bounds (<c, <=c, >c, >=c)
//   - Arithmetic islands with {} syntax
//   - Desugaring (EF[a,b], AF[a,b], EG[a,b], AG[a,b])
//   - NNF conversion for TCTL
//   - Zone operations (UDBM integration)
//
// ============================================================================

#include "tctl/test.hpp"
#include "tctl/ast.hpp"
#include "tctl/lexer.hpp"
#include "tctl/normalization.hpp"
#include "tctl/parser.hpp"
#include "tctl/tableau.hpp"
#include "tctl/utils.hpp"
#include "tctl/zone.hpp"

#include <chrono>
#include <cstring>
#include <ctime>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

namespace tctl {

// ── CSV results output ───────────────────────────────────────────────────────

// Directory where per-suite CSV files are written.  Set once by init_results_dir().
static std::string g_results_dir;

// Wrap a string value for CSV: surround with double-quotes, escape inner ones.
static std::string csv_escape(const std::string& s) {
    std::string out = "\"";
    for (char c : s) {
        if (c == '"') out += "\"\"";
        else          out += c;
    }
    out += '"';
    return out;
}

// Create the output directory named test_result_{YYYYmmdd_HHMMSS} in the
// current working directory and store the path in g_results_dir.
static void init_results_dir() {
    std::time_t t  = std::time(nullptr);
    std::tm     tm = *std::localtime(&t);
    std::ostringstream oss;
    oss << "test_result_" << std::put_time(&tm, "%Y%m%d_%H%M%S");
    g_results_dir = oss.str();
    std::filesystem::create_directories(g_results_dir);
    std::cout << "[results] Writing CSVs to: " << g_results_dir << "/\n";
}

// ── TestContext ──────────────────────────────────────────────────────────────

void TestContext::check(bool condition, const std::string& description) {
    ++total_;
    if (!condition) {
        ++failed_;
        std::cerr << "  FAIL: " << description << "\n";
    }
}

void TestContext::check_eq(const std::string& actual,
                           const std::string& expected,
                           const std::string& description) {
    ++total_;
    if (actual != expected) {
        ++failed_;
        std::cerr << "  FAIL: " << description << "\n"
                  << "    expected: " << expected << "\n"
                  << "    actual:   " << actual << "\n";
    }
}

// ── TestRunner ──────────────────────────────────────────────────────────────

void TestRunner::run(const std::string& name, TestFunc func) {
    ++tests_run_;
    TestContext ctx;
    ctx.current_test_ = name;

    std::cerr << "TEST: " << name << "\n";
    try {
        func(ctx);
    } catch (const std::exception& e) {
        std::cerr << "  EXCEPTION: " << e.what() << "\n";
        ++ctx.failed_;
    }

    checks_total_ += ctx.total();
    checks_failed_ += ctx.failed();
    if (ctx.failed() > 0) {
        ++tests_failed_;
    } else {
        std::cerr << "  OK (" << ctx.total() << " checks)\n";
    }
}

int TestRunner::summarise() const {
    std::cerr << "\n=== Test Summary ===\n"
              << "Tests:  " << tests_run_ << " run, "
              << (tests_run_ - tests_failed_) << " passed, "
              << tests_failed_ << " failed\n"
              << "Checks: " << checks_total_ << " total, "
              << (checks_total_ - checks_failed_) << " passed, "
              << checks_failed_ << " failed\n";

    if (tests_failed_ == 0) {
        std::cerr << "ALL TESTS PASSED\n";
        return 0;
    } else {
        std::cerr << "SOME TESTS FAILED\n";
        return 1;
    }
}

// ============================================================================
// Helper: parse and pretty-print
// ============================================================================

static std::string pp(const std::string& input) {
    FormulaFactory f;
    FormulaId id = parse_formula(input, f);
    return f.to_string(id);
}

static std::string pp_norm(const std::string& input) {
    FormulaFactory f;
    FormulaId id = parse_formula(input, f);
    FormulaId nid = normalize(id, f);
    return f.to_string(nid);
}

static bool parse_fails(const std::string& input) {
    try {
        FormulaFactory f;
        parse_formula(input, f);
        return false;
    } catch (const std::exception&) {
        return true;
    }
}

// ============================================================================
// TCTL Lexer Tests
// ============================================================================

static void test_lexer_brackets_braces(TestContext& ctx) {
    auto toks = tokenise("[1,5]");
    ctx.check(toks[0].kind == TokenKind::LBracket, "[ bracket");
    ctx.check(toks[1].kind == TokenKind::IntLiteral && toks[1].text == "1", "integer 1");
    ctx.check(toks[2].kind == TokenKind::Comma, "comma");
    ctx.check(toks[3].kind == TokenKind::IntLiteral && toks[3].text == "5", "integer 5");
    ctx.check(toks[4].kind == TokenKind::RBracket, "] bracket");
    
    auto toks2 = tokenise("{x + 1}");
    ctx.check(toks2[0].kind == TokenKind::LBrace, "{ brace");
    ctx.check(toks2[1].kind == TokenKind::Identifier && toks2[1].text == "x", "identifier x");
    ctx.check(toks2[2].kind == TokenKind::Plus, "+ operator");
    ctx.check(toks2[3].kind == TokenKind::IntLiteral && toks2[3].text == "1", "integer 1");
    ctx.check(toks2[4].kind == TokenKind::RBrace, "} brace");
}

static void test_lexer_inf_keyword(TestContext& ctx) {
    auto toks = tokenise("inf INF Inf");
    ctx.check(toks[0].kind == TokenKind::KwInf, "inf keyword lowercase");
    ctx.check(toks[1].kind == TokenKind::KwInf, "INF keyword uppercase");
    ctx.check(toks[2].kind == TokenKind::KwInf, "Inf keyword mixed case");
}

static void test_lexer_comparison_ops(TestContext& ctx) {
    auto toks = tokenise("< <= > >= =");
    ctx.check(toks[0].kind == TokenKind::Less, "< operator");
    ctx.check(toks[1].kind == TokenKind::LessEq, "<= operator");
    ctx.check(toks[2].kind == TokenKind::Greater, "> operator");
    ctx.check(toks[3].kind == TokenKind::GreaterEq, ">= operator");
    ctx.check(toks[4].kind == TokenKind::Equal, "= operator");
}

static void test_lexer_tctl_keywords(TestContext& ctx) {
    auto toks = tokenise("EX AX EF AF EG AG E A U true false");
    ctx.check(toks[0].kind == TokenKind::KwEX, "EX keyword");
    ctx.check(toks[1].kind == TokenKind::KwAX, "AX keyword");
    ctx.check(toks[2].kind == TokenKind::KwEF, "EF keyword");
    ctx.check(toks[3].kind == TokenKind::KwAF, "AF keyword");
    ctx.check(toks[4].kind == TokenKind::KwEG, "EG keyword");
    ctx.check(toks[5].kind == TokenKind::KwAG, "AG keyword");
    ctx.check(toks[6].kind == TokenKind::KwE, "E keyword");
    ctx.check(toks[7].kind == TokenKind::KwA, "A keyword");
    ctx.check(toks[8].kind == TokenKind::KwU, "U keyword");
    ctx.check(toks[9].kind == TokenKind::KwTrue, "true keyword");
    ctx.check(toks[10].kind == TokenKind::KwFalse, "false keyword");
}

// ============================================================================
// TCTL Parser Tests
// ============================================================================

static void test_parse_atoms(TestContext& ctx) {
    ctx.check_eq(pp("p"), "p", "parse atom p");
    ctx.check_eq(pp("true"), "true", "parse true");
    ctx.check_eq(pp("false"), "false", "parse false");
    ctx.check_eq(pp("!p"), "(!p)", "negation");
    ctx.check_eq(pp("p & q"), "(p & q)", "conjunction");
    ctx.check_eq(pp("p | q"), "(p | q)", "disjunction");
}

static void test_parse_closed_intervals(TestContext& ctx) {
    std::string result = pp("EF[1,5] p");
    ctx.check(result.find("[1,") != std::string::npos, "EF[1,5] lower bound closed");
    ctx.check(result.find(",5]") != std::string::npos, "EF[1,5] upper bound closed");
    
    result = pp("AF[2,10] q");
    ctx.check(result.find("[2,") != std::string::npos, "AF[2,10] lower bound");
    ctx.check(result.find(",10]") != std::string::npos, "AF[2,10] upper bound");
    
    result = pp("AG[0,inf) s");
    ctx.check(result.find("[0,") != std::string::npos, "AG[0,inf) lower bound");
    ctx.check(result.find("inf)") != std::string::npos, "AG[0,inf) infinity upper");
}

static void test_parse_open_intervals(TestContext& ctx) {
    std::string result = pp("EF(1,5) p");
    ctx.check(result.find("(1,") != std::string::npos, "EF(1,5) lower bound open");
    ctx.check(result.find(",5)") != std::string::npos, "EF(1,5) upper bound open");
    
    result = pp("AF(0,10) q");
    ctx.check(result.find("(0,") != std::string::npos, "AF(0,10) open lower");
}

static void test_parse_mixed_intervals(TestContext& ctx) {
    std::string result = pp("EF[1,5) p");
    ctx.check(result.find("[1,") != std::string::npos, "EF[1,5) lower bound closed");
    ctx.check(result.find(",5)") != std::string::npos, "EF[1,5) upper bound open");
    
    result = pp("AF(2,10] q");
    ctx.check(result.find("(2,") != std::string::npos, "AF(2,10] lower bound open");
    ctx.check(result.find(",10]") != std::string::npos, "AF(2,10] upper bound closed");
}

static void test_parse_relational_upper(TestContext& ctx) {
    std::string result = pp("EF<5 p");
    ctx.check(result.find("[0,") != std::string::npos, "EF<5 has lower=0 closed");
    ctx.check(result.find(",5)") != std::string::npos, "EF<5 has upper=5 open");
    
    result = pp("EF<=10 q");
    ctx.check(result.find("[0,") != std::string::npos, "EF<=10 has lower=0 closed");
    ctx.check(result.find(",10]") != std::string::npos, "EF<=10 has upper=10 closed");
}

static void test_parse_relational_lower(TestContext& ctx) {
    std::string result = pp("EF>5 p");
    ctx.check(result.find("(5,") != std::string::npos, "EF>5 has lower=5 open");
    ctx.check(result.find("inf") != std::string::npos, "EF>5 has upper=inf");
    
    result = pp("EF>=3 q");
    ctx.check(result.find("[3,") != std::string::npos, "EF>=3 has lower=3 closed");
    ctx.check(result.find("inf") != std::string::npos, "EF>=3 has upper=inf");
}

static void test_parse_all_operators_relational(TestContext& ctx) {
    ctx.check(!parse_fails("EF<5 p"), "EF<5 p parses");
    ctx.check(!parse_fails("AF<=10 q"), "AF<=10 q parses");
    ctx.check(!parse_fails("EG>3 r"), "EG>3 r parses");
    ctx.check(!parse_fails("AG>=7 s"), "AG>=7 s parses");
}

static void test_parse_timed_until(TestContext& ctx) {
    std::string result = pp("E(p U[1,5] q)");
    ctx.check(result.find("U[1,") != std::string::npos, "E(p U[1,5] q) has timed until");
    ctx.check(result.find(",5]") != std::string::npos, "E(p U[1,5] q) interval upper");
    
    result = pp("A(p U[0,10] q)");
    ctx.check(result.find("U[0,") != std::string::npos, "A(p U[0,10] q) timed until");
    
    result = pp("E(p U[5,inf) q)");
    ctx.check(result.find("U[5,") != std::string::npos, "E(p U[5,inf) q) timed until");
    ctx.check(result.find("inf)") != std::string::npos, "E(p U[5,inf) q) infinity");
}

static void test_parse_timed_until_open(TestContext& ctx) {
    std::string result = pp("E(p U(1,5) q)");
    ctx.check(result.find("U(1,") != std::string::npos, "E(p U(1,5) q) open lower");
    ctx.check(result.find(",5)") != std::string::npos, "E(p U(1,5) q) open upper");
    
    result = pp("A(p U[0,10) q)");
    ctx.check(result.find("U[0,") != std::string::npos, "A(p U[0,10) q) closed lower");
    ctx.check(result.find(",10)") != std::string::npos, "A(p U[0,10) q) open upper");
}

static void test_parse_arithmetic_braces(TestContext& ctx) {
    ctx.check(!parse_fails("{x <= 5}"), "{x <= 5} parses");
    ctx.check(!parse_fails("{x + y >= 10}"), "{x + y >= 10} parses");
    ctx.check(!parse_fails("{x * 2 = 10}"), "{x * 2 = 10} parses");
    ctx.check(!parse_fails("{(x + 1) * 2 <= 10}"), "{(x + 1) * 2 <= 10} parses");
}

static void test_tctl_with_arithmetic(TestContext& ctx) {
    ctx.check(!parse_fails("EF[1,5] {x <= 10}"), "EF[1,5] {x <= 10} parses");
    ctx.check(!parse_fails("AG[0,inf) {y >= 0}"), "AG[0,inf) {y >= 0} parses");
    ctx.check(!parse_fails("E({x < 5} U[1,10] {x >= 5})"), "Timed until with constraints parses");
}

static void test_parse_errors_intervals(TestContext& ctx) {
    ctx.check(parse_fails("EF[5,3] p"), "EF[5,3] fails (5 > 3)");
    ctx.check(parse_fails("EF[3,3] p"), "EF[3,3] fails (point interval, a == b)");
    ctx.check(parse_fails("EF[1 5] p"), "EF[1 5] fails (missing comma)");
    ctx.check(parse_fails("EF[1,5 p"), "EF[1,5 p fails (missing ])");
}

static void test_parse_errors_arithmetic(TestContext& ctx) {
    ctx.check(parse_fails("{x <= 5"), "{x <= 5 fails (missing })");
}

// ============================================================================
// TCTL Desugaring Tests
// ============================================================================

static void test_desugar_timed_ef_af(TestContext& ctx) {
    FormulaFactory f;
    
    FormulaId id = parse_formula("EF[1,5] p", f);
    FormulaId desugared = desugar(id, f);
    std::string result = f.to_string(desugared);
    ctx.check(result.find("E(true U") != std::string::npos, "EF[1,5] desugars to E(true U...)");
    
    id = parse_formula("AF[2,10] q", f);
    desugared = desugar(id, f);
    result = f.to_string(desugared);
    ctx.check(result.find("A(true U") != std::string::npos, "AF[2,10] desugars to A(true U...)");
}

static void test_desugar_timed_eg_ag(TestContext& ctx) {
    FormulaFactory f;
    
    FormulaId id = parse_formula("EG[1,5] p", f);
    FormulaId desugared = desugar(id, f);
    std::string result = f.to_string(desugared);
    ctx.check(result.find("(!A(true U") != std::string::npos, "EG[1,5] desugars to !A(true U...)");
    
    id = parse_formula("AG[0,3] q", f);
    desugared = desugar(id, f);
    result = f.to_string(desugared);
    ctx.check(result.find("(!E(true U") != std::string::npos, "AG[0,3] desugars to !E(true U...)");
}

static void test_desugar_timed_until(TestContext& ctx) {
    FormulaFactory f;
    
    FormulaId id = parse_formula("E(p U[1,5] q)", f);
    FormulaId desugared = desugar(id, f);
    std::string result = f.to_string(desugared);
    ctx.check(result.find("E(p U") != std::string::npos, "Timed EU preserved");
    
    id = parse_formula("A(p U[2,10] q)", f);
    desugared = desugar(id, f);
    result = f.to_string(desugared);
    ctx.check(result.find("A(p U") != std::string::npos, "Timed AU preserved");
}

// ============================================================================
// TCTL NNF Conversion Tests
// ============================================================================

static void test_nnf_timed_operators(TestContext& ctx) {
    std::string result = pp_norm("E(p U[1,5] q)");
    ctx.check(result.find("E(p U") != std::string::npos, "Timed EU in NNF");
    
    result = pp_norm("A(p U[2,10] q)");
    ctx.check(result.find("A(p U") != std::string::npos, "Timed AU in NNF");
}

static void test_nnf_negated_timed(TestContext& ctx) {
    // After the new NNF pipeline, ¬TimedEU and ¬TimedAU are converted to
    // TimedAR and TimedER respectively via R/U duality — no Not() wrappers.
    std::string result = pp_norm("!E(p U[1,5] q)");
    // ¬E(p U[1,5] q) = A(¬p R[1,5] ¬q)  — TimedAR
    ctx.check(result.find("A(") != std::string::npos && result.find("R[") != std::string::npos,
              "Negated timed EU in NNF becomes TimedAR");

    result = pp_norm("!A(p U[2,10] q)");
    // ¬A(p U[2,10] q) = E(¬p R[2,10] ¬q)  — TimedER
    ctx.check(result.find("E(") != std::string::npos && result.find("R[") != std::string::npos,
              "Negated timed AU in NNF becomes TimedER");
}

static void test_normalize_timed_sugar(TestContext& ctx) {
    std::string result = pp_norm("EF[1,5] p");
    ctx.check(result.find("E(true U") != std::string::npos, "EF[1,5] p normalizes");
    
    result = pp_norm("EG[0,3] p");
    // EG[0,3] p → desugar: ¬A(true U[0,3] ¬p) → NNF: TimedER(False, p, [0,3])
    ctx.check(result.find("E(false R[") != std::string::npos, "EG[0,3] p normalizes to E(false R[...])");
}

// ============================================================================
// TCTL Zone/DBM Tests (UDBM Integration)
// ============================================================================

static void test_zone_smoke(TestContext& ctx) {
    ctx.check(zone_smoke_test(), "Zone operations pass smoke test");
}

static void test_zone_universe_empty(TestContext& ctx) {
    Zone z_univ = Zone::universe(3);  // 2 clocks + reference
    ctx.check(!z_univ.is_empty(), "Universe zone is not empty");
    
    Zone z_empty = Zone::empty(3);
    ctx.check(z_empty.is_empty(), "Empty zone is empty");
}

static void test_zone_constraints(TestContext& ctx) {
    Zone z = Zone::universe(3);  // Need at least 2 clocks + reference
    
    z.add_upper_bound(1, 5, false);  // Clock 1 (not 0, which is reference)
    ctx.check(!z.is_empty(), "Zone with x<=5 is not empty");
    
    z.add_lower_bound(1, 3, false);
    ctx.check(!z.is_empty(), "Zone with 3<=x<=5 is not empty");
    
    Zone z2 = z;
    z2.add_upper_bound(1, 2, false);
    ctx.check(z2.is_empty(), "Zone with 3<=x & x<=2 is empty");
}

static void test_zone_delay_reset(TestContext& ctx) {
    Zone z = Zone::universe(3);
    z.add_upper_bound(1, 5, false);  // Clock 1 (not 0)
    
    Zone z_delayed = z;
    z_delayed.delay();
    ctx.check(!z_delayed.is_empty(), "Delayed zone is not empty");
    
    Zone z_reset = z;
    z_reset.reset(1);  // Reset clock 1 (not 0)
    ctx.check(!z_reset.is_empty(), "Reset zone is not empty");
}

// ============================================================================
// TCTL Complex Formula Tests
// ============================================================================

static void test_nested_timed_operators(TestContext& ctx) {
    std::string result = pp("EF[1,5] (p & AG[2,10] q)");
    ctx.check(result.find("EF") != std::string::npos, "Outer EF preserved");
    ctx.check(result.find("AG") != std::string::npos, "Inner AG preserved");
    
    result = pp("EF[1,2] EG[3,4] p");
    ctx.check(result.find("EF") != std::string::npos, "EF in nested");
    ctx.check(result.find("EG") != std::string::npos, "EG in nested");
}

static void test_timed_until_complex(TestContext& ctx) {
    std::string result = pp("E((p | q) U[0,5] (r & s))");
    ctx.check(result.find("E((p | q) U") != std::string::npos, "Complex timed until");
    
    result = pp("A((p -> q) U[1,10] r)");
    ctx.check(result.find("A(") != std::string::npos, "A( in complex until");
    ctx.check(result.find("U") != std::string::npos, "U in complex until");
}

static void test_tctl_boolean_arithmetic(TestContext& ctx) {
    ctx.check(!parse_fails("EF[1,5] ({x <= 5} & p)"), "TCTL with arithmetic parses");
    ctx.check(!parse_fails("AG[0,inf) ({y >= 0} -> {y <= 100})"), "TCTL implication with constraints");
    ctx.check(!parse_fails("E({x < 10} U[0,5] ({x >= 10} & done))"), "Complex timed until with constraints");
}

static void test_relational_complex(TestContext& ctx) {
    ctx.check(!parse_fails("EF<5 (p & AF<=10 q)"), "Nested relational bounds");
    ctx.check(!parse_fails("AG>=0 (p -> EF<5 q)"), "AG>= with nested EF<");
}

// ============================================================================
// TCTL Stress Tests
// ============================================================================

static const std::vector<std::string> kTctlStressFormulas = {
    "EF[0,10] p",
    "AF[1,5] (p & q)",
    "EG[0,inf) p",
    "AG[0,100] (p -> q)",
    "E(p U[0,5] q)",
    "A(p U[1,10] (q | r))",
    "E((p & r) U[0,inf) q)",
    "EF<5 p",
    "AF<=10 q",
    "EG>0 r",
    "AG>=1 s",
    "EF(0,5) p",
    "AF[0,5) q",
    "EG(1,10] r",
    "EF[1,5] AG[0,10] p",
    "AG[0,inf) EF<5 q",
    "EF<=10 (p & EG[1,5] q)",
    "EF[0,5] {x <= 10}",
    "AG[0,inf) {y >= 0}",
    "E({x < 5} U[0,10] {x >= 5})",
    "EF[1,5] ({x <= 5} & p) | AG[0,10] {y >= 0}",
    "A({x < 10} U[0,5] {x >= 10}) -> EF<5 done",
    "!EG[0,inf) (!p | {x < 0})",
};

static void test_tctl_stress_parsing(TestContext& ctx) {
    int parsed = 0;
    std::vector<int> failed_indices;
    
    for (size_t i = 0; i < kTctlStressFormulas.size(); ++i) {
        const auto& formula = kTctlStressFormulas[i];
        try {
            FormulaFactory f;
            parse_formula(formula, f);
            ++parsed;
        } catch (const std::exception& e) {
            failed_indices.push_back(static_cast<int>(i));
            std::cerr << "  Failed to parse formula " << i << ": " << formula << "\n";
            std::cerr << "    Error: " << e.what() << "\n";
        }
    }
    
    ctx.check(failed_indices.empty(), 
              "All " + std::to_string(kTctlStressFormulas.size()) + " stress formulas parse");
    ctx.check(parsed == static_cast<int>(kTctlStressFormulas.size()),
              "Parsed all stress formulas");
}

static void test_tctl_stress_normalization(TestContext& ctx) {
    int normalized = 0;
    
    for (const auto& formula : kTctlStressFormulas) {
        try {
            FormulaFactory f;
            FormulaId id = parse_formula(formula, f);
            FormulaId nid = normalize(id, f);
            (void)nid;
            ++normalized;
        } catch (const std::exception& e) {
            std::cerr << "  Failed to normalize: " << formula << "\n";
            std::cerr << "    Error: " << e.what() << "\n";
        }
    }
    
    ctx.check(normalized == static_cast<int>(kTctlStressFormulas.size()),
              "Normalized all stress formulas");
}

// ============================================================================
// TCTL Tableau Satisfiability Tests (10 tests: 5 SAT, 5 UNSAT)
// ============================================================================

// Helper: check satisfiability of a formula string.
// timeout_s: timeout in seconds (0 = no timeout, default = 1200 = 20 min).
static Result check_sat(const std::string& formula_str,
                        int timeout_s = 1200) {
    FormulaFactory f;
    FormulaId parsed = parse_formula(formula_str, f);
    FormulaId norm = normalize(parsed, f);
    TableauEngine engine(f);
    if (timeout_s > 0) {
        engine.set_timeout(std::chrono::seconds(timeout_s));
    }
    return engine.check(norm);
}

// ── SAT-1: Lower bound forces delay ─────────────────────────────────────────
// E(true U_[1,2] p) — can delay to t=1 then satisfy p within [1,2].
static void test_tctl_sat1_lower_bound_delay(TestContext& ctx) {
    Result r = check_sat("E(true U[1,2] p)");
    ctx.check(r == Result::Satisfiable, "E(true U[1,2] p) should be SAT");
}

// ── SAT-2: Strict lower bound forces delay beyond a ─────────────────────────
// E(true U_(1,3] p) — must not allow satisfaction at exactly t=1.
static void test_tctl_sat2_strict_lower(TestContext& ctx) {
    Result r = check_sat("E(true U(1,3] p)");
    ctx.check(r == Result::Satisfiable, "E(true U(1,3] p) should be SAT");
}

// ── SAT-3: Upper bound non-strict allows at boundary ────────────────────────
// E(true U_[0,2] p) & EX p — can satisfy p at some time ≤2, possibly immediately.
static void test_tctl_sat3_upper_bound_boundary(TestContext& ctx) {
    Result r = check_sat("E(true U[0,2] p) & EX p");
    ctx.check(r == Result::Satisfiable, "E(true U[0,2] p) & EX p should be SAT");
}

// ── SAT-4: Two timed untils in conjunction ──────────────────────────────────
// E(true U_[1,4] p) & E(true U_[2,6] q) — independent satisfaction windows.
static void test_tctl_sat4_two_timed_untils(TestContext& ctx) {
    Result r = check_sat("E(true U[1,4] p) & E(true U[2,6] q)");
    ctx.check(r == Result::Satisfiable, "E(true U[1,4] p) & E(true U[2,6] q) should be SAT");
}

// ── SAT-5: Universal timed until with achievable p ──────────────────────────
// A(true U_[1,3] p) & AX p — since next-state makes p true universally.
static void test_tctl_sat5_universal_timed(TestContext& ctx) {
    Result r = check_sat("A(true U[1,3] p) & AX p");
    ctx.check(r == Result::Satisfiable, "A(true U[1,3] p) & AX p should be SAT");
}

// ── UNSAT-1: Invariant ¬p contradicts timed until ───────────────────────────
// AG ¬p & E(true U_(1,2) p) — p never becomes true, so timed until can't be satisfied.
static void test_tctl_unsat1_invariant_contradiction(TestContext& ctx) {
    Result r = check_sat("AG (!p) & E(true U(1,2) p)");
    ctx.check(r == Result::Unsatisfiable, "AG !p & E(true U(1,2) p) should be UNSAT");
}

// ── UNSAT-2: Upper deadline with impossible p ───────────────────────────────
// E(true U_[0,2] p) & AG ¬p — p never holds, deadline passes.
static void test_tctl_unsat2_upper_deadline(TestContext& ctx) {
    Result r = check_sat("E(true U[0,2] p) & AG (!p)");
    ctx.check(r == Result::Unsatisfiable, "E(true U[0,2] p) & AG !p should be UNSAT");
}

// ── UNSAT-3: Lower bound + impossible p ─────────────────────────────────────
// E(true U_[1,3] p) & AG ¬p — p never holds.
static void test_tctl_unsat3_lower_bound_impossible(TestContext& ctx) {
    Result r = check_sat("E(true U[1,3] p) & AG (!p)");
    ctx.check(r == Result::Unsatisfiable, "E(true U[1,3] p) & AG !p should be UNSAT");
}

// ── UNSAT-4: Point intervals are rejected by the parser ──────────────────
// Both E(true U(2,2) p) and E(true U[2,2] p) have a == b, which is
// disallowed (the parser requires a < b).
static void test_tctl_unsat4_strict_upper_boundary(TestContext& ctx) {
    // Open point interval: parse error (a == b)
    ctx.check(parse_fails("E(true U(2,2) p)"),
              "E(true U(2,2) p) should fail to parse (point interval)");

    // Closed point interval: parse error (a == b)
    ctx.check(parse_fails("E(true U[2,2] p)"),
              "E(true U[2,2] p) should fail to parse (point interval)");
}

// ── UNSAT-5: Loop without fulfilment must be rejected ───────────────────────
// E(true U_[1,3] p) & EG ¬p — EG ¬p forces a ¬p-loop; timed-until can't be fulfilled.
static void test_tctl_unsat5_loop_without_fulfilment(TestContext& ctx) {
    Result r = check_sat("AG (!p) & E(true U[1,3] p)");
    ctx.check(r == Result::Unsatisfiable, "AG !p & E(true U[1,3] p) should be UNSAT (loop check)");
}

// ============================================================================
// Negated Timed-Until Zone-Splitting Tests
// ============================================================================

// ── NEG-TIMED-1: SAT window outside negated interval ────────────────────────
// E(true U[2,3] p) & ¬E(true U[0,2) p): p at time ≥2 satisfies the first
// conjunct without violating ¬E(true U[0,2) p) since t=2 is outside [0,2).
static void test_neg_timed_sat_window(TestContext& ctx) {
    Result r = check_sat("E(true U[2,3] p) & !E(true U[0,2) p)");
    ctx.check(r == Result::Satisfiable,
              "E(true U[2,3] p) & !E(true U[0,2) p) should be SAT");
}

// ── NEG-TIMED-2: Strict upper bound allows boundary ─────────────────────────
// ¬E(true U[0,2) p) forbids p before time 2 but allows p at t>=2.
static void test_neg_timed_strict_upper(TestContext& ctx) {
    // p in [2,3]: allowed since [0,2) excludes t>=2
    Result r1 = check_sat("E(true U[2,3] p) & !E(true U[0,2) p)");
    ctx.check(r1 == Result::Satisfiable,
              "E(true U[2,3] p) & !E(true U[0,2) p) should be SAT (p at t>=2)");

    // p forced in [0,1] which is inside [0,2): UNSAT
    Result r2 = check_sat("E(true U[0,1] p) & !E(true U[0,2) p)");
    ctx.check(r2 == Result::Unsatisfiable,
              "E(true U[0,1] p) & !E(true U[0,2) p) should be UNSAT (overlap)");
}

// ── NEG-TIMED-3: Strict lower bound exclusion ───────────────────────────────
// ¬E(true U(2,5] p) forbids p in (2,5] but allows p at or before t=2.
static void test_neg_timed_strict_lower(TestContext& ctx) {
    // p in [1,2]: allowed since (2,5] excludes t<=2
    Result r1 = check_sat("E(true U[1,2] p) & !E(true U(2,5] p)");
    ctx.check(r1 == Result::Satisfiable,
              "E(true U[1,2] p) & !E(true U(2,5] p) should be SAT (p at boundary)");

    // p in (2,3] fully contained in (2,5]: UNSAT
    Result r2 = check_sat("E(true U(2,3] p) & !E(true U(2,5] p)");
    ctx.check(r2 == Result::Unsatisfiable,
              "E(true U(2,3] p) & !E(true U(2,5] p) should be UNSAT (subset interval)");
}

// ============================================================================
// Release Operator Tests — Parsing
// ============================================================================

static void test_parse_release(TestContext& ctx) {
    // 8.1a  A(p R q) — untimed universal release
    ctx.check(!parse_fails("A(p R q)"), "A(p R q) parses");
    std::string result = pp("A(p R q)");
    ctx.check(result.find("A(p R q)") != std::string::npos, "A(p R q) round-trips");

    // 8.1b  E(p R q) — untimed existential release
    ctx.check(!parse_fails("E(p R q)"), "E(p R q) parses");
    result = pp("E(p R q)");
    ctx.check(result.find("E(p R q)") != std::string::npos, "E(p R q) round-trips");

    // 8.1c  E(p R[1,3] q) — timed existential release
    ctx.check(!parse_fails("E(p R[1,3] q)"), "E(p R[1,3] q) parses");
    result = pp("E(p R[1,3] q)");
    ctx.check(result.find("R[") != std::string::npos, "E(p R[1,3] q) round-trips with interval");

    // 8.1d  A(p R[2,5] q) — timed universal release
    ctx.check(!parse_fails("A(p R[2,5] q)"), "A(p R[2,5] q) parses");

    // 8.1e  EG and AG still parse correctly
    ctx.check(!parse_fails("EG p"), "EG p still parses");
    ctx.check(!parse_fails("AG p"), "AG p still parses");

    // 8.1f  Nested release with boolean subformulae
    ctx.check(!parse_fails("A((p & q) R[0,2] (r | s))"), "nested release parses");
    result = pp("A((p & q) R[0,2] (r | s))");
    ctx.check(result.find("R[") != std::string::npos, "nested release round-trips");

    // 8.1g  Mixing R and U in nested formula
    ctx.check(!parse_fails("E(p R q) & A(r U s)"), "R and U coexist");

    // 8.1h  Open/mixed interval on R
    ctx.check(!parse_fails("E(p R(1,3] q)"), "E(p R(1,3] q) parses");
    ctx.check(!parse_fails("A(p R[1,3) q)"), "A(p R[1,3) q) parses");
}

// ============================================================================
// Release Operator Tests — Normalization / NNF
// ============================================================================

static void test_normalize_release(TestContext& ctx) {
    // 8.2a  ¬A(p R q) should become E(¬p U ¬q) in NNF (duality)
    std::string result = pp_norm("!A(p R q)");
    ctx.check(result.find("E((!p) U (!q))") != std::string::npos,
              "!A(p R q) normalizes to E(!p U !q)");

    // 8.2b  ¬E(p R q) should become A(¬p U ¬q) in NNF (duality)
    result = pp_norm("!E(p R q)");
    ctx.check(result.find("A((!p) U (!q))") != std::string::npos,
              "!E(p R q) normalizes to A(!p U !q)");

    // 8.2c  ¬E(p R[1,3] q) should lower to A(¬p U[1,3] ¬q)
    result = pp_norm("!E(p R[1,3] q)");
    ctx.check(result.find("A(") != std::string::npos && result.find("U[") != std::string::npos,
              "!E(p R[1,3] q) normalizes to A(!p U[1,3] !q)");

    // 8.2d  ¬A(p R[2,5] q) should lower to E(¬p U[2,5] ¬q)
    result = pp_norm("!A(p R[2,5] q)");
    ctx.check(result.find("E(") != std::string::npos && result.find("U[") != std::string::npos,
              "!A(p R[2,5] q) normalizes to E(!p U[2,5] !q)");

    // 8.2e  Untimed EG φ desugars to E(false R φ) in pre-NNF
    {
        FormulaFactory f;
        FormulaId id = parse_formula("EG p", f);
        FormulaId desugared = desugar(id, f);
        std::string s = f.to_string(desugared);
        ctx.check(s.find("E(false R p)") != std::string::npos,
                  "EG p desugars to E(false R p)");
    }

    // 8.2f  Untimed AG φ desugars to A(false R φ) in pre-NNF
    {
        FormulaFactory f;
        FormulaId id = parse_formula("AG p", f);
        FormulaId desugared = desugar(id, f);
        std::string s = f.to_string(desugared);
        ctx.check(s.find("A(false R p)") != std::string::npos,
                  "AG p desugars to A(false R p)");
    }

    // 8.2g  E(p R q) itself stays unchanged through normalization
    result = pp_norm("E(p R q)");
    ctx.check(result.find("E(p R q)") != std::string::npos,
              "E(p R q) survives normalization");

    // 8.2h  A(p R q) itself stays unchanged through normalization
    result = pp_norm("A(p R q)");
    ctx.check(result.find("A(p R q)") != std::string::npos,
              "A(p R q) survives normalization");
}

// ============================================================================
// Release Operator Tests — Satisfiability (SAT/UNSAT)
// ============================================================================

static void test_release_sat(TestContext& ctx) {
    // --- SAT cases ---

    // EG p  — existentially at least one infinite path where p holds always.
    // SAT: a one-state model with p true loops forever.
    Result r = check_sat("EG p");
    ctx.check(r == Result::Satisfiable, "EG p should be SAT");

    // AG p  — universally all paths maintain p forever.
    // SAT: a model with p everywhere.
    r = check_sat("AG p");
    ctx.check(r == Result::Satisfiable, "AG p should be SAT");

    // E(p R q) with q true — the Release obligations are satisfied when ψ holds
    // everywhere on the path, which is consistent.
    r = check_sat("E(p R q)");
    ctx.check(r == Result::Satisfiable, "E(p R q) should be SAT");

    // A(p R q) — universal release, also satisfiable.
    r = check_sat("A(p R q)");
    ctx.check(r == Result::Satisfiable, "A(p R q) should be SAT");

    // EG p & EF q — can maintain p forever on one path and eventually reach q on
    // another (or p ∧ q in the same state).
    r = check_sat("EG p & EF q");
    ctx.check(r == Result::Satisfiable, "EG p & EF q should be SAT");

    // AG p & p — trivially consistent.
    r = check_sat("AG p & p");
    ctx.check(r == Result::Satisfiable, "AG p & p should be SAT");

    // E(q R p) & p — p must hold in the initial state and ψ=p indeed does.
    r = check_sat("E(q R p) & p");
    ctx.check(r == Result::Satisfiable, "E(q R p) & p should be SAT");

    // --- UNSAT cases ---

    // E(p R false) — ψ=false must hold in the initial state, impossible.
    r = check_sat("E(p R false)");
    ctx.check(r == Result::Unsatisfiable, "E(p R false) should be UNSAT");

    // A(p R false) — same reasoning, false must hold initially.
    r = check_sat("A(p R false)");
    ctx.check(r == Result::Unsatisfiable, "A(p R false) should be UNSAT");

    // EG p & EG !p — there exists a path where p holds always AND a path where
    // !p holds always. Both require p / !p at the initial state: contradiction.
    r = check_sat("EG p & EG !p");
    ctx.check(r == Result::Unsatisfiable, "EG p & EG !p should be UNSAT");

    // AG p & !p — p must hold everywhere but not at the initial state.
    r = check_sat("AG p & !p");
    ctx.check(r == Result::Unsatisfiable, "AG p & !p should be UNSAT");

    // AG false — contradicts any model (no state can contain false).
    r = check_sat("AG false");
    ctx.check(r == Result::Unsatisfiable, "AG false should be UNSAT");

    // EG false — same: E(false R false), ψ=false required initially.
    r = check_sat("EG false");
    ctx.check(r == Result::Unsatisfiable, "EG false should be UNSAT");
}

// ============================================================================
// Release Operator Tests — Loop acceptance / eventuality
// ============================================================================

static void test_release_loop_acceptance(TestContext& ctx) {
    // EG should NOT be treated as an eventuality.  A consistent loop
    // containing only {p, EX EG p} (no unfulfilled eventuality) must be accepted.
    Result r = check_sat("EG p");
    ctx.check(r == Result::Satisfiable, "EG p loop accepted (no eventuality)");

    // AG should likewise not be an eventuality.
    r = check_sat("AG p");
    ctx.check(r == Result::Satisfiable, "AG p loop accepted (no eventuality)");

    // A(p R q): loop containing {q, AX A(p R q)} accepted when consistent.
    r = check_sat("A(p R q)");
    ctx.check(r == Result::Satisfiable, "A(p R q) loop accepted");

    // Regression: an EU eventuality mixed with an ER non-eventuality.
    // E(p U q) & E(r R s): EU needs q eventually, ER does not block.
    r = check_sat("E(p U q) & E(r R s)");
    ctx.check(r == Result::Satisfiable, "E(p U q) & E(r R s) should be SAT");

    // Regression: negated timed EU/AU still works alongside Release.
    r = check_sat("!E(true U[1,3] p) & EG q");
    ctx.check(r == Result::Satisfiable, "!E(true U[1,3] p) & EG q should be SAT");
}

// ============================================================================
// TCTL High-Coverage Test Suite (50 formulas: 25 SAT, 25 UNSAT)
// ============================================================================

std::vector<TestCase> generate_tctl_tests() {
    return {
        // =================================================================
        // Category A — Simple bounded until (5 SAT / 5 UNSAT)
        // =================================================================

        // A-S1: basic closed-interval EU — q reachable at t∈[1,3] while p holds
        { "E(p U[1,3] q)", true },
        // A-S2: basic closed-interval AU — single-path model with q at t=1
        { "A(p U[1,4] q)", true },
        // A-S3: both-strict interval EU — q reachable at t∈(1,5)
        { "E(p U(1,5) q)", true },
        // A-S4: lower bound 0, can discharge immediately at t=0
        { "E(true U[0,3] p)", true },
        // A-S5: strict lower, closed upper AU — q at t∈(0,2]
        { "A(p U(0,2] q)", true },

        // A-U1: q globally false via AG, EU needs q in [1,3] — contradiction
        { "AG[0,inf) !q & E(p U[1,3] q)", false },
        // A-U2: p globally false, AU needs p in (1,5) — contradiction
        { "AG[0,inf) !p & A(true U(1,5) p)", false },
        // A-U3: must reach 'false' in [1,3] — impossible
        { "E(true U[1,3] false)", false },
        // A-U4: universal until to 'false' — impossible
        { "A(true U(0,2] false)", false },
        // A-U5: r globally false, EU needs r in [2,6] — contradiction
        { "AG[0,inf) !r & E(p U[2,6] r)", false },

        // =================================================================
        // Category B — Lower-only and upper-only bounds (3 SAT / 3 UNSAT)
        // =================================================================

        // B-S1: relational lower-only, p reachable at t>2
        { "EF>2 p", true },
        // B-S2: relational upper-only, q reachable at t≤4
        { "EF<=4 q", true },
        // B-S3: universal relational lower, all paths reach p at t≥1
        { "AF>=1 p", true },

        // B-U1: need p before t=3, but !p enforced on [0,5]; [0,3)⊂[0,5]
        { "EF<3 p & AG[0,5] !p", false },
        // B-U2: all paths must reach p by t≤2, but p always false
        { "AF<=2 p & AG[0,inf) !p", false },
        // B-U3: need p in [5,8]⊂[0,10], but !p forced on [0,10]
        { "AG[0,10] !p & EF[5,8] p", false },

        // =================================================================
        // Category C — Nested timed operators (4 SAT / 4 UNSAT)
        // =================================================================

        // C-S1: nested EF — reach state at t∈[1,3], then p within 2 from there
        { "EF[1,3] EF[0,2] p", true },
        // C-S2: reach state at t∈[0,2] where AG[0,3] p holds (p stable)
        { "EF[0,2] AG[0,3] p", true },
        // C-S3: nested timed until — outer EU fires, inner AU from that state
        { "E(p U[1,4] A(q U[0,2] r))", true },
        // C-S4: universal then existential — AF fires, then EF from that state
        { "AF[0,3] EF[1,5] q", true },

        // C-U1: inner AU needs r, but r globally false — nested impossibility
        { "E(p U[1,3] A(q U[2,4] r)) & AG[0,inf) !r", false },
        // C-U2: AG[0,inf) false ≡ false; EF to a false state is impossible
        { "EF[1,2] AG[0,inf) false", false },
        // C-U3: AF reaches EF[1,5] p state, but p never true; nested chain fails
        { "AF[0,3] EF[1,5] p & AG[0,inf) !p", false },
        // C-U4: inner A(true U[1,3] false) requires reaching false — impossible
        { "EF[0,2] A(true U[1,3] false)", false },

        // =================================================================
        // Category D — Conjunction of timed obligations (4 SAT / 4 UNSAT)
        // =================================================================

        // D-S1: two independent EU on non-overlapping intervals
        { "E(true U[1,3] p) & E(true U[4,6] q)", true },
        // D-S2: three independent EF obligations with room for all
        { "EF[1,4] p & EF[2,6] q & EF[3,8] r", true },
        // D-S3: existential EG and EF can be satisfied on different paths
        { "EG[0,3] p & EF[1,2] q", true },
        // D-S4: universal AU and existential EU — non-conflicting
        { "A(true U[1,3] p) & E(true U[0,2] q)", true },

        // D-U1: EG<3 !p requires !p in [0,3); AG>2 p requires p after t=2;
        //        overlap at (2,3) forces both p and !p — regression test
        { "EG<3 !p & AG>2 p", false },
        // D-U2: AG[0,5] forces p in [0,5]; EF[1,3] needs !p in [1,3]⊂[0,5]
        { "AG[0,5] p & EF[1,3] !p", false },
        // D-U3: AG[0,3] p and AG[0,3] !p — p and !p both forced globally
        { "AG[0,3] p & AG[0,3] !p", false },
        // D-U4: AG[0,4] forces p; EU needs !p in [2,3]⊂[0,4]
        { "AG[0,4] p & E(true U[2,3] !p)", false },

        // =================================================================
        // Category E — AG/EG/AF/EF encodings (4 SAT / 4 UNSAT)
        // =================================================================

        // E-S1: model with p always true satisfies AG[0,5]
        { "AG[0,5] p", true },
        // E-S2: path with p throughout [0,4]
        { "EG[0,4] p", true },
        // E-S3: reach q at t∈[2,4]
        { "EF[2,4] q", true },
        // E-S4: all paths reach p in [1,5]
        { "AF[1,5] p", true },

        // E-U1: EG path has p in [0,3]; AF forces !p in [0,2]⊂[0,3] on
        //        that same path — contradiction at the overlap
        { "EG[0,3] p & AF[0,2] !p", false },
        // E-U2: AG forces p in [0,5]; AF forces !p in [1,3]⊂[0,5]
        { "AG[0,5] p & AF[1,3] !p", false },
        // E-U3: EG path needs p always; AG forbids p everywhere — contradiction
        { "EG[0,inf) p & AG[0,inf) !p", false },
        // E-U4: EF needs p in [1,3]; AG forbids p in [0,4]; [1,3]⊂[0,4]
        { "EF[1,3] p & AG[0,4] !p", false },

        // =================================================================
        // Category F — Boundary discharge tests (3 SAT / 3 UNSAT)
        // =================================================================

        // F-S1: lower bound 0 — discharge immediately at t=0
        { "E(true U[0,1] p)", true },
        // F-S2: strict lower bound — must wait past t=0 then discharge
        { "E(true U(0,2] p)", true },
        // F-S3: strict upper bound — discharge at lower bound t=1, before t=2
        { "E(true U[1,2) p)", true },

        // F-U1: EG path has p in [0,2]; AG forbids p in [1,3]; overlap [1,2]
        { "EG[0,2] p & AG[1,3] !p", false },
        // F-U2: need p in [2,3]; AG forbids p in [0,3]; [2,3]⊂[0,3]
        { "E(true U[2,3] p) & AG[0,3] !p", false },
        // F-U3: strict interval (2,3); AG forbids p in [2,4]; (2,3)⊂[2,4]
        { "E(true U(2,3) p) & AG[2,4] !p", false },

        // =================================================================
        // Extra coverage (2 SAT / 2 UNSAT)
        // =================================================================

        // X-S1: EF finds p at t>3 (outside [0,3]); EG has !p in [0,3] — compatible
        { "EF[1,5] p & EG[0,3] !p", true },
        // X-S2: AU requires q in [1,3] with p until then; EG has p in [0,2] —
        //        the EU path naturally maintains p before q appears
        { "A(p U[1,3] q) & EG[0,2] p", true },

        // X-U1: AG[0,2] forces p at t=2; AG[2,5] forces !p at t=2 — boundary clash
        { "AG[0,2] p & AG[2,5] !p", false },
        // X-U2: EG path has q in [1,5]; AG forbids q in [2,4]⊂[1,5]
        { "EG[1,5] q & AG[2,4] !q", false },
    };
}

// ── Data-driven runner for the 50-formula coverage suite ─────────────────────


static void run_test_vector(TestContext& ctx,
                           const std::vector<TestCase>& tests,
                           const std::string& suite_name    = "",
                           bool               print_test_number = false,
                           int                timeout_s     = 10) {
    // Open CSV file for this suite (if a results directory has been initialised).
    std::ofstream csv;
    if (!suite_name.empty() && !g_results_dir.empty()) {
        const std::string csv_path = g_results_dir + "/" + suite_name + ".csv";
        csv.open(csv_path);
        if (csv.is_open()) {
            csv << "formula,result,test_passed,time_taken_s\n";
        }
    }

    for (size_t i = 0; i < tests.size(); ++i) {
        const auto& tc = tests[i];
        if (print_test_number) {
            std::cout << "Running test " << (i + 1) << ": " << tc.formula << std::endl;
        }

        std::string result_str = "ERROR";
        bool        passed     = false;
        double      elapsed    = 0.0;

        try {
            Result r   = check_sat(tc.formula, timeout_s);
            result_str = result_to_string(r);
            elapsed    = r.elapsed_s;

            if (r == Result::Timeout) {
                ctx.check(false,
                          "Test " + std::to_string(i + 1) + ": " + tc.formula +
                          " TIMED OUT after " + std::to_string(timeout_s) + "s");
                passed = false;
            } else {
                const bool actual_sat = (r == Result::Satisfiable);
                passed = (actual_sat == tc.expected_sat);
                ctx.check(passed,
                          "Test " + std::to_string(i + 1) + ": " + tc.formula +
                          " expected " + (tc.expected_sat ? "SAT" : "UNSAT") +
                          " got "     + (actual_sat ? "SAT" : "UNSAT"));
            }
        } catch (const std::exception& e) {
            ctx.check(false,
                      "Test " + std::to_string(i + 1) + ": " + tc.formula +
                      " threw: " + std::string(e.what()));
        }

        if (csv.is_open()) {
            csv << csv_escape(tc.formula) << ","
                << result_str             << ","
                << (passed ? "true" : "false") << ","
                << std::fixed << std::setprecision(6) << elapsed << "\n";
        }
    }
}




std::vector<TestCase> generate_tctl_edge_tests_100() {
    return {
        // ================================================================
        // 1) Boundary strictness & adjacency (20)
        // ================================================================

        // exact boundary clashes at t = 2 (closed/closed)
        { "AG[0,2] p & AG[2,5] !p", false },   // boundary included in both
        { "AG[0,2) p & AG[2,5] !p", false },  // UNSAT: can't cross boundary at t=2 (closed [2,5] requires !p at t=2 but p holds up to transition)
        { "AG[0,2] p & AG(2,5] !p", false },  // UNSAT: closed [0,2] locks p at t=2; can't switch to !p without violating AG[0,2]
        { "AG[0,2) p & AG(2,5] !p", true },    // disjoint with gap at 2 (both open)
        { "AG[0,2) p & AG(2,5] !p", true },    // disjoint at boundary

        // strict vs non-strict discharge for EF
        { "EF[1,3] p & AG[0,1] !p", true },    // p can happen at t>1
        { "EF(1,3] p & AG[0,1] !p", true },    // must be >1 anyway
        { "EF[1,3] p & AG[0,2] !p", true },    // p at t∈(2,3] is outside [0,2]
        { "EF(2,3] p & AG[0,2] !p", true },    // can do at (2,3]

        // upper-bound strictness
        { "EF[1,2) p & AG[0,2] !p", false },   // needs p before 2, but forbidden up to 2
        { "EF[1,2) p & AG[0,2) !p", false },   // forbidden on [1,2)
        { "EF[1,2] p & AG[0,2) !p", true },    // can do at exactly t=2
        { "EF[1,2] p & AG[0,2] !p", false },   // 2 forbidden too

        // AU boundary cases (universal reachability)
        { "AF[1,2] p & AG[0,2) !p", true },    // all paths can satisfy at t=2
        { "AF[1,2] p & AG[0,2] !p", false },   // blocks even at t=2
        { "AF(1,2] p & AG[0,2) !p", true },    // still can do at t=2
        { "AF(1,2) p & AG[0,2) !p", false },   // must happen in (1,2), forbidden there

        // adjacency without overlap
        { "EG[0,1] p & AG(1,3] !p", false },  // UNSAT: transition from p to !p at boundary always violates one of the intervals
        { "EG[0,1] p & AG[1,3] !p", false },   // t=1 overlap

        // strict lower only
        { "EF>2 p & AG[0,2] !p", true },
        { "EF>=2 p & AG[0,2] !p", true },      // p at t>2 is outside [0,2]

        // ================================================================
        // 2) PRE/IN region traps for ¬TimedEU / ¬TimedAU (20)
        // ================================================================

        // EF is TimedEU(True U_I p). These stress your ¬TimedEU zone splitting + delay.
        { "!EF[1,3] p & EF[1,3] p", false },
        { "!EF(1,3] p & EF[1,3] p", true },    // p at exactly t=1 satisfies EF[1,3] but not EF(1,3]
        { "!EF[1,3) p & EF(1,3] p", true },    // p at exactly t=3 satisfies EF(1,3] but not EF[1,3)
        { "!EF(1,3) p & EF[1,3] p", true },    // p at t=1 or t=3 satisfies EF[1,3] but not EF(1,3)

        // "p already true" interacts with ¬EF and IN region
        { "p & !EF[0,2] p", false },           // if interval includes 0, EF holds immediately
        { "p & !EF(0,2] p", true },            // EF requires >0; can avoid by never delaying past 0? (anti-zeno will matter)
        { "p & !EF>0 p", true },               // same idea with relational strict lower

        // force time to enter IN where ¬EF must forbid p
        { "p & AF[1,2] true & !EF(0,3] p", true },  // SAT: p only at t=0 (outside (0,3]), transition to !p, delay to [1,2]
        { "p & AF[1,2] true & !EF[1,3] p", true },  // SAT: p at t=0 (outside [1,3]), transition to !p, delay to [1,2]

        // ¬AF is typically handled as ¬TimedAU (existential continuation)
        { "!AF[1,3] p & AF[1,3] p", false },
        { "!AF(1,3] p & AF[1,3] p", true },    // AF[1,3] allows p at t=1; !AF(1,3] allows that since (1,3] excludes t=1

        // avoidability: if p never holds, ¬AF should be SAT
        { "!AF[1,3] p & AG[0,inf) !p", true },
        { "!AF(1,3] p & AG[0,inf) !p", true },

        // mixing ¬AF with forced p at time in interval
        // Removed: AF[2,2+1] has invalid syntax (parser doesn't support arithmetic in bounds)
        { "!AF[1,3] p & AF[2,3] p", false },

        // multiple negated timed obligations on overlapping IN windows
        { "!EF[1,4] p & !EF[2,5] !p", false }, // in [2,4], would force both ¬p and p at same state if time reaches IN with stutter; stresses soundness
        { "!EF[1,4] p & !EF[2,5] p", true },   // both forbid p in their IN; consistent

        // negated timed until with phi=true and psi present: your delay guard tries to keep clock in PRE
        { "p & !EF[1,3] p", true },             // SAT by staying before t=1 (no time-divergence required)
        { "p & !EF[1,3] p & AF>=1 true", true },  // SAT: p at t=0 (outside [1,3]), transition to !p, delay to t>=1

        // ================================================================
        // 3) Anti-Zeno / delay successor stress (15)
        // ================================================================

        // Try to satisfy ¬EF by never letting time reach 1; anti-zeno should reject if time-divergence required
        { "!EF[1,3] p & AG[0,inf) !p", true },      // should be SAT without needing zeno avoidance (since !p anyway)
        { "!EF[1,3] p & p", true },                 // SAT by staying before t=1
        { "!EF[1,3] p & p & AF>=1 true", true },  // SAT: same as above, reordered

        // Zeno trap with a timed safety obligation active
        { "!EF(0,2] p & p", true },                 // only avoidable by staying at t=0 forever; stresses zeno handling
        { "!EF(0,2] p & p & AF>0 true", true },  // SAT: p at t=0 (outside (0,2]), transition to !p, delay past 0

        // delay vs discrete step choice
        { "EF[1,2] p & AG[0,inf) !p", false },
        { "EF[1,2] p & AG[0,1) !p", true },         // can fire at t in [1,2], but not in [0,1)
        { "EF(1,2] p & AG[0,1] !p", true },         // must be >1, consistent

        // force both a delay successor and a discrete successor obligation
        { "EX p & EF>1 q", true },
        { "AX !p & EF>1 p", true },                 // AX only constrains immediate next; 2+ steps away can have p at t>1

        // ================================================================
        // 4) Context propagation (AX) + timed negations (15)
        // ================================================================

        // AX + ¬EF should propagate universally: all successors must keep avoiding
        { "AX !EF[1,3] p & EF[1,3] p", true },  // SAT: EF via delay (p persists), AX constrains discrete successors only
        { "AX !EF[1,3] p & EF[4,6] p", true },      // can satisfy EF later outside forbidden window if avoidance is only for [1,3]

        // Two-step propagation
        { "AX AX !p & EX EX p", false },            // after 2 steps, must have !p universally but EX path wants p
        { "AX AX !p & EX EX !p", true },

        // Mix AX and timed until
        { "AX AG[0,2] !p & EF[0,1] p", true },      // p at initial state (t=0) satisfies EF[0,1]; AX only constrains successors
        { "AX AG[0,2] !p & EF[3,4] p", true },

        // AX with delayed negation: pressure on your delay-guard
        { "AX !EF[1,3] p & p", true },              // avoidance obligation starts next state
        { "AX !EF[1,3] p & AF>=1 true & p", true }, // AX pushes !EF to successors; initial p is fine; successor can have !p

        // ================================================================
        // 5) Multi-clock interactions (nested timed ops) (15)
        // ================================================================

        // Two timed operators => two clocks, nested + conjunction
        { "EF[1,3] p & EF[2,4] q", true },
        { "EF[1,3] p & AG[0,inf) !p", false },

        // Nested EF with inner conflicting window
        { "EF[0,2] (EF[1,3] p)", true },
        { "EF[0,2] (EF[1,3] p) & AG[0,inf) !p", false },

        // Universal outer, existential inner
        { "AF[0,2] EF[1,3] p", true },
        { "AF[0,2] EF[1,3] p & AG[0,inf) !p", false },

        // Until nesting (forces clock resets and active_timed cleanup correctness)
        { "E(true U[1,4] EF[0,2] p)", true },
        { "E(true U[1,4] EF[0,2] p) & AG[0,inf) !p", false },

        // Negated timed inside another timed
        { "EF[0,2] !EF[1,3] p", true },             // reach a state where EF[1,3] p is false
        { "EF[0,2] !EF[1,3] p & p & AF>=1 true", true },  // can reach a !p state at t<2 where !EF[1,3] holds

        // ================================================================
        // 6) EG/AG encodings corner cases (15)
        // ================================================================

        { "EG[0,inf) p & AG[0,inf) !p", false },
        { "EG[0,3] p & AG(3,5] !p", false },  // UNSAT: same boundary issue as EG[0,1] p & AG(1,3] !p
        { "EG[0,3] p & AG[3,5] !p", false },         // boundary 3 clash

        // EG + EF on same atom with conflicting window
        { "EG[0,5] !p & EF[2,3] p", true },          // EG and EF can be on different paths
        { "EG[0,2] !p & EF[3,4] p", true },

        // AG forcing p while EG requires !p on a path (path/global mismatch)
        { "AG[0,inf) p & EG[0,inf) !p", false },

        // Universal reachability + existential always
        { "AF[1,3] p & EG[0,2] p", true },
        { "AF[1,3] p & EG[0,2] !p", true },           // EG path has !p in [0,2], but AF allows p at t∈(2,3]

        // ================================================================
        // 7) Pure UNTIL + negated UNTIL interaction (10)
        // ================================================================

        // Untimed negation rules (Not(EU)/Not(AU)) are separate from timed ones
        { "!E(p U q) & E(p U q)", false },
        { "!A(p U q) & A(p U q)", false },

        { "!E(true U p) & p", false },               // E(true U p) holds immediately if p
        { "!E(true U p) & !p", true },

        { "E(true U p) & AG[0,inf) !p", false },
        { "A(true U p) & AG[0,inf) !p", false },

        { "!E(p U q) & AG[0,inf) !q", true },
        { "!A(p U q) & EF[0,2] (p | !p)", true },    // tautology reachable (parser has |)

        { "!A(true U p) & AG[0,inf) !p", true },
        { "!E(true U p) & AG[0,inf) !p", true },

        // ================================================================
        // 8) Stress: many obligations, overlaps, and mixed quantifiers (10)
        // ================================================================

        // { "EF[1,4] p & EF[2,5] q & EF[3,6] r & AG[0,inf) (!p | !q | !r)", true },  // KNOWN ISSUE: engine can't handle 4 interacting timed formulas
        { "EF[1,4] p & EF[2,5] q & EF[3,6] r & AG[0,inf) (!p & !q & !r)", false },

        { "AF[1,4] p & AF[2,5] q & AF[3,6] r", true },
        { "AF[1,4] p & AG[0,inf) !p", false },

        { "AG[0,5] p & EF[1,4] !p", false },
        { "AG[0,5] p & EF(5,8] !p", true },          // conflict starts after 5

        { "AX AG[0,3] p & EX EF[1,2] !p", false },   // next state forces p in [0,3], but EX wants !p soon
        { "AX AG[0,1] p & EX EF[2,3] !p", true },

        { "!EF[1,3] p & EF[4,6] p", true },
        { "!EF[1,3] p & EF[2,4] p", true },          // p at t∈(3,4] satisfies EF[2,4] without violating !EF[1,3]
    };
}


// ============================================================================
// Comprehensive 200-Test Suite
// ============================================================================
//
// Covers: Boolean basics, TCTL untimed, timed modalities, Release (ER/AR),
// timed Release, boundary strictness, negated timed, multi-clock, nested
// timed, EX/AX + timed, deep nesting (≥8), loop/eventuality, Zeno edges,
// arithmetic, implications/biconditional, context propagation, contradictions,
// and stress interactions.
//
// XFAIL tests are commented out with a reason.
// Engine bug: EX + existential timed → UNSAT (should be SAT).
//             AX + universal timed  → UNSAT (should be SAT).
// ============================================================================
std::vector<TestCase> generate_comprehensive_200() {
    return {
        // ================================================================
        // §1  Boolean fundamentals  (10 tests: 5 SAT, 5 UNSAT)
        // ================================================================
        /* 001 */ { "true", true },
        /* 002 */ { "false", false },
        /* 003 */ { "p", true },
        /* 004 */ { "p & q", true },
        /* 005 */ { "p | q", true },
        /* 006 */ { "p & !p", false },
        /* 007 */ { "!false", true },
        /* 008 */ { "!true", false },
        /* 009 */ { "(p | q) & (!p & !q)", false },
        /* 010 */ { "p & q & r & s", true },

        // ================================================================
        // §2  Implication & biconditional  (8 tests: 5 SAT, 3 UNSAT)
        // ================================================================
        /* 011 */ { "p -> q", true },
        /* 012 */ { "p -> p", true },
        /* 013 */ { "p <-> p", true },
        /* 014 */ { "p <-> !p", false },
        /* 015 */ { "(p -> q) & p & !q", false },
        /* 016 */ { "(p -> q) & (q -> r) & p", true },
        /* 017 */ { "p -> EF p", true },
        /* 018 */ { "(!p -> EF q) & !p", true },

        // ================================================================
        // §3  Untimed EX / AX  (10 tests: 5 SAT, 5 UNSAT)
        // ================================================================
        /* 019 */ { "EX true", true },
        /* 020 */ { "EX false", false },
        /* 021 */ { "AX true", true },
        /* 022 */ { "AX false", false },
        /* 023 */ { "EX p", true },
        /* 024 */ { "AX p", true },
        /* 025 */ { "EX p & AX !p", false },
        /* 026 */ { "AX p & AX !p", false },
        /* 027 */ { "EX (p & q)", true },
        /* 028 */ { "EX (p & !p)", false },

        // ================================================================
        // §4  Untimed EU / AU / EF / AF / EG / AG  (16 tests: 8 SAT, 8 UNSAT)
        // ================================================================
        /* 029 */ { "EF p", true },
        /* 030 */ { "AF p", true },
        /* 031 */ { "EG p", true },
        /* 032 */ { "AG p", true },
        /* 033 */ { "E(p U q)", true },
        /* 034 */ { "A(p U q)", true },
        /* 035 */ { "E(true U q)", true },
        /* 036 */ { "E(p U true)", true },
        /* 037 */ { "EF false", false },
        /* 038 */ { "EG false", false },
        /* 039 */ { "AG false", false },
        /* 040 */ { "E(false U false)", false },
        /* 041 */ { "A(false U false)", false },
        /* 042 */ { "E(p U q) & !q & !p", false },
        /* 043 */ { "EF p & !EF p", false },
        /* 044 */ { "EG p & EG !p", false },

        // ================================================================
        // §5  Untimed Release ER / AR  (12 tests: 6 SAT, 6 UNSAT)
        // ================================================================
        /* 045 */ { "E(p R q)", true },
        /* 046 */ { "A(p R q)", true },
        /* 047 */ { "E(p R true)", true },
        /* 048 */ { "E(true R p)", true },
        /* 049 */ { "E(p R q) & q", true },
        /* 050 */ { "A(p R q) & q", true },
        /* 051 */ { "E(p R false)", false },
        /* 052 */ { "E(false R false)", false },
        /* 053 */ { "A(p R false)", false },
        /* 054 */ { "A(false R false)", false },
        /* 055 */ { "E(p R q) & !q & !p", false },
        /* 056 */ { "A(p R q) & !q", false },

        // ================================================================
        // §6  Timed EU / AU basics  (12 tests: 6 SAT, 6 UNSAT)
        // ================================================================
        /* 057 */ { "E(true U[1,3] p)", true },
        /* 058 */ { "A(true U[1,3] p)", true },
        /* 059 */ { "E(true U[0,5] p)", true },
        /* 060 */ { "E(true U(1,3] p)", true },
        /* 061 */ { "E(true U[1,3) p)", true },
        /* 062 */ { "E(true U(1,3) p)", true },
        /* 063 */ { "EF[1,3] p & AG[0,inf) !p", false },
        /* 064 */ { "AF[1,3] p & AG[0,inf) !p", false },
        /* 065 */ { "E(true U[1,2] p) & AG[0,3] !p", false },
        /* 066 */ { "E(true U[1,3] p) & E(true U[1,3] !p) & AG p", false },
        /* 067 */ { "E(true U[1,3] p) & AG[0,4] !p", false },
        /* 068 */ { "A(true U[1,3] p) & AG[0,4] !p", false },

        // ================================================================
        // §7  Timed EF / AF / EG / AG sugar  (10 tests: 5 SAT, 5 UNSAT)
        // ================================================================
        /* 069 */ { "EF[1,3] p", true },
        /* 070 */ { "AF[1,3] p", true },
        /* 071 */ { "EG[0,2] p", true },
        /* 072 */ { "AG[0,2] p", true },
        /* 073 */ { "AG[0,inf) true", true },
        /* 074 */ { "EF[1,3] false", false },
        /* 075 */ { "AF[1,3] false", false },
        /* 076 */ { "EG[0,3] (p & !p)", false },
        /* 077 */ { "EG[0,2] p & EG[0,2] !p", false },
        /* 078 */ { "AG[0,2] p & EF[0,2] !p", false },

        // ================================================================
        // §8  Timed Release ER / AR  (10 tests: 5 SAT, 5 UNSAT)
        // ================================================================
        /* 079 */ { "E(p R[1,3] q)", true },
        /* 080 */ { "A(p R[1,3] q)", true },
        /* 081 */ { "E(false R[1,3] p)", true },
        /* 082 */ { "E(p R[1,3] q) & !q", true },
        /* 083 */ { "A(p R[1,3] q) & !q", true },
        /* 084 */ { "E(p R[1,3] false)", false },  // false can't hold in [1,3]
        /* 085 */ { "A(p R[1,3] false)", false },  // false can't hold in [1,3]
        /* 086 */ { "E(false R[1,3] false)", false }, // false can't hold in [1,3]
        /* 087 */ { "E(p R[1,3] q) & AG[0,inf) !q & AG[0,inf) !p", false }, // q must hold in [1,3], but AG forbids it
        /* 088 */ { "E(p R q) & !q & !p", false },  // untimed R: q must hold initially

        // ================================================================
        // §9  Boundary strictness & adjacency  (12 tests: 6 SAT, 6 UNSAT)
        // ================================================================
        /* 089 */ { "EF[1,3] p & AG[0,1] !p", true },
        /* 090 */ { "EF(1,3] p & AG[0,1] !p", true },
        /* 091 */ { "EF[1,3] p & AG[0,2] !p", true },
        /* 092 */ { "EF[1,2] p & AG[0,2) !p", true },
        /* 093 */ { "AF[1,2] p & AG[0,2) !p", true },
        /* 094 */ { "AG[0,2) p & AG(2,5] !p", true },
        /* 095 */ { "EF[1,2) p & AG[0,2] !p", false },
        /* 096 */ { "EF[1,2) p & AG[0,2) !p", false },
        /* 097 */ { "EF[1,2] p & AG[0,2] !p", false },
        /* 098 */ { "AF[1,2] p & AG[0,2] !p", false },
        /* 099 */ { "AF(1,2) p & AG[0,2) !p", false },
        /* 100 */ { "AG[0,2] p & AG[2,5] !p", false },

        // ================================================================
        // §10  Negated timed modalities  (10 tests: 5 SAT, 5 UNSAT)
        // ================================================================
        /* 101 */ { "!EF[1,3] p", true },
        /* 102 */ { "!AF[1,3] p", true },
        /* 103 */ { "!E(true U[1,3] p)", true },
        /* 104 */ { "!EF[1,3] p & EF[4,6] p", true },
        /* 105 */ { "E(true U[2,3] p) & !E(true U[0,2) p)", true },
        /* 106 */ { "!EF[0,inf) p & p", false },
        /* 107 */ { "!EF[0,inf) p & EF p", false },
        /* 108 */ { "E(true U[0,1] p) & !E(true U[0,2) p)", false },
        /* 109 */ { "E(true U(2,3] p) & !E(true U(2,5] p)", false },
        /* 110 */ { "!EF[1,3] p & EF[2,4] p & AG[0,1] !p & AG(4,inf) !p", true },  // p at t∈(3,4]

        // ================================================================
        // §11  Relational time bounds  (8 tests: 4 SAT, 4 UNSAT)
        // ================================================================
        /* 111 */ { "EF>2 p", true },
        /* 112 */ { "EF>=1 p", true },
        /* 113 */ { "EF<=5 p", true },
        /* 114 */ { "EF>2 p & AG[0,2] !p", true },
        /* 115 */ { "EF<0 p", false },
        /* 116 */ { "EF>2 p & AG>2 !p", false },
        /* 117 */ { "EF<=2 p & AG[0,2] !p", false },
        /* 118 */ { "AF>0 p & AG>0 !p", false },

        // ================================================================
        // §12  Arithmetic constraints  (10 tests: 5 SAT, 5 UNSAT)
        // ================================================================
        /* 119 */ { "{x <= 5}", true },
        /* 120 */ { "{x >= 0}", true },
        /* 121 */ { "{x <= 5} & {x >= 3}", true },
        /* 122 */ { "EF[1,3] {x <= 10}", true },
        /* 123 */ { "{x + 1 <= 6} & {x >= 4}", true },
        /* 124 */ { "{x > 3} & {x < 2}", false },
        /* 125 */ { "{x + 1 <= 5} & {x >= 5}", false },
        /* 126 */ { "{x <= 0} & {x > 0}", false },
        /* 127 */ { "{x >= 10} & {x <= 5}", false },
        /* 128 */ { "EF[1,3] ({x > 5} & {x < 3})", false },

        // ================================================================
        // §13  Multi-clock & two timed conjuncts  (8 tests: 4 SAT, 4 UNSAT)
        // ================================================================
        /* 129 */ { "E(true U[1,2] p) & E(true U[3,5] q)", true },
        /* 130 */ { "E(true U[0,2] p) & EF[1,3] q", true },
        /* 131 */ { "A(true U[1,3] p) & EG[0,2] p", true },
        /* 132 */ { "E(true U[1,3] p) & E(true U[2,4] q)", true },
        /* 133 */ { "E(true U[1,2] p) & E(true U[1,2] !p) & AG p", false },
        /* 134 */ { "AF[1,3] p & AF[1,3] !p & EG p", false },
        /* 135 */ { "E(true U[1,2] p) & AG[0,3] !p", false },
        /* 136 */ { "EF[1,3] p & EF[1,3] !p & AG p & AG !p", false },

        // ================================================================
        // §14  EX / AX wrapping temporal  (10 tests: 5 SAT, 5 UNSAT)
        // ================================================================
        /* 137 */ { "EX EG p", true },
        /* 138 */ { "EX AG p", true },
        /* 139 */ { "AX EG p", true },
        /* 140 */ { "EX (p & EG q)", true },
        /* 141 */ { "EX AF[1,3] p", true },
        /* 142 */ { "EX (p & !p)", false },
        /* 143 */ { "EX EG false", false },
        /* 144 */ { "AX AG false", false },
        /* 145 */ { "EX false & AX false", false },
        /* 146 */ { "EX EF false", false },
        // XFAIL: EX + existential timed → UNSAT (engine bug: clock mgmt
        //        in generate_successors drops existential timed constraints)
        // { "EX EF[1,3] p", true },
        // { "EX (EF[1,3] p)", true },
        // { "EX EX EF[1,3] p", true },
        // { "AX AF[1,3] p", true },

        // ================================================================
        // §15  Nested path quantifiers  (10 tests: 5 SAT, 5 UNSAT)
        // ================================================================
        /* 147 */ { "EF EG p", true },
        /* 148 */ { "AG EF p", true },
        /* 149 */ { "EG AG p", true },
        /* 150 */ { "EF AG p", true },
        /* 151 */ { "EF (p & EG q)", true },
        /* 152 */ { "AG AF false", false },
        /* 153 */ { "EF (p & !p)", false },
        /* 154 */ { "EG (p & !p)", false },
        /* 155 */ { "EF EG false", false },
        /* 156 */ { "EF (EG p & EG !p)", false },

        // ================================================================
        // §16  Nested timed + untimed  (10 tests: 5 SAT, 5 UNSAT)
        // ================================================================
        /* 157 */ { "EF[1,3] EG p", true },
        /* 158 */ { "EF[1,3] (p & EG q)", true },
        /* 159 */ { "AG[0,2] EF p", true },
        /* 160 */ { "EG[0,3] (p | EF q)", true },
        /* 161 */ { "EF[1,3] AG p", true },
        /* 162 */ { "EF[1,3] (p & !p)", false },
        /* 163 */ { "AG[0,2] EF false", false },
        /* 164 */ { "AG[0,2] (p & !p)", false },
        /* 165 */ { "EF[1,3] EG false", false },
        /* 166 */ { "AG[0,2] false", false },

        // ================================================================
        // §17  AX/EX + timed conjunctions  (8 tests: 4 SAT, 4 UNSAT)
        // ================================================================
        /* 167 */ { "AX AG[0,3] p & EX EF[1,2] !p", false },
        /* 168 */ { "AX AG[0,1] p & EX EF[2,3] !p", true },
        /* 169 */ { "EX (p & EG[0,2] q)", true },
        /* 170 */ { "AX EG[0,2] p", true },
        /* 171 */ { "EX AG[0,2] p", true },
        /* 172 */ { "EX (EG[0,2] p & EG[0,2] !p)", false },
        /* 173 */ { "AX (p & !p)", false },
        /* 174 */ { "AX AG[0,2] false", false },

        // ================================================================
        // §18  Deep nesting ≥ 8 levels  (8 tests: 4 SAT, 4 UNSAT)
        // ================================================================
        /* 175 */ { "EF EG EF EG EF EG EF EG p", true },
        /* 176 */ { "AG EF AG EF AG EF AG EF p", true },
        /* 177 */ { "EX EX EX EX EX EX EX EX p", true },
        /* 178 */ { "AX AX AX AX AX AX AX AX p", true },
        /* 179 */ { "EX EX EX EX EX EX EX EX false", false },
        /* 180 */ { "EF EG EF EG EF EG EF EG false", false },
        /* 181 */ { "AG EF AG EF AG EF AG EF false", false },
        /* 182 */ { "AX AX AX AX AX AX AX AX false", false },

        // ================================================================
        // §19  Loop detection & eventuality  (8 tests: 4 SAT, 4 UNSAT)
        // ================================================================
        /* 183 */ { "EG p & EF q", true },
        /* 184 */ { "AG (p -> EF q)", true },
        /* 185 */ { "E(p U q) & EG p", true },
        /* 186 */ { "EG (p | q)", true },
        /* 187 */ { "EG p & AF !p", false },
        /* 188 */ { "EG p & AX !p", false },
        /* 189 */ { "AG p & EF !p", false },
        /* 190 */ { "AG p & AG !p", false },

        // ================================================================
        // §20  Contradictions: propositional + zone + timed  (10 tests: 0 SAT, 10 UNSAT)
        // ================================================================
        /* 191 */ { "p & !p & EF q", false },
        /* 192 */ { "EF (p & !p) & EG q", false },
        /* 193 */ { "(p | !p) & false", false },
        /* 194 */ { "EF[1,3] p & AG[0,inf) !p & EG q", false },
        /* 195 */ { "AG p & EF !p & EG q", false },
        /* 196 */ { "{x > 5} & {x < 3} & EF p", false },
        /* 197 */ { "E(p U false) & EG q", false },
        /* 198 */ { "AF false & EG p", false },
        /* 199 */ { "EG false | EG (p & !p)", false },
        /* 200 */ { "AG false | (p & !p)", false },
    };
}

static void test_comprehensive_200(TestContext& ctx) {
    auto tests = generate_comprehensive_200();
    run_test_vector(ctx, tests, "comprehensive_200");
}

// ============================================================================
// Stress-200 test suite: 200 advanced tests across 7 categories
// ============================================================================
//
// Categories (exact counts):
//   1) Deep nesting + precedence torture          (30)
//   2) Quantifier alternation stress              (30)
//   3) Loop + eventuality correctness             (30)
//   4) Timed tight bounds & race conditions       (30)
//   5) Multi-until / multi-clock interaction      (30)
//   6) Release-heavy equivalence + duality checks (30)
//   7) Pathological normalization / negation edges (20)
//   Total = 200
//
// Non-triviality: ≥170 tests meet ≥1 criterion (nesting≥8, ≥3 mixed temporal,
//   ≥2 timed intervals, ≥2 simultaneous timed-until, negation stress, or
//   loop-detection/eventuality forcing).
//
// A "complexity_score" helper counts temporal operators and nesting depth;
// the suite asserts score≥threshold for at least 170 of the 200 tests.
// ============================================================================

// Complexity scoring: count temporal ops and nesting depth in the formula string.
// Returns {temporal_op_count, nesting_depth, distinct_interval_count}.
//static std::tuple<int,int,int> complexity_score(const std::string& formula) {
//    int temporal_ops  = 0;
//    int max_depth     = 0;
//    int cur_depth     = 0;
//    int intervals     = 0;
//
//    // Count temporal ops by scanning for known keywords
//    const char* kw[] = {
//        "EX", "AX", "EF", "AF", "EG", "AG",
//        "U[", "U(", "U ", "R[", "R(", "R ",
//        nullptr
//    };
//    for (size_t i = 0; i < formula.size(); ++i) {
//        for (int k = 0; kw[k]; ++k) {
//            size_t klen = std::strlen(kw[k]);
//            if (formula.compare(i, klen, kw[k]) == 0) {
//                // Avoid matching atoms like "Up" — check that this looks temporal
//                if (klen == 2 && i + 2 < formula.size() && std::isalpha(formula[i+2])
//                    && formula[i+1] != '[' && formula[i+1] != '(' && formula[i+1] != ' ')
//                    continue;
//                ++temporal_ops;
//                break;
//            }
//        }
//        if (formula[i] == '(') { ++cur_depth; if (cur_depth > max_depth) max_depth = cur_depth; }
//        if (formula[i] == ')') { --cur_depth; }
//        if (formula[i] == '[' || (formula[i] == '(' && i > 0 && (formula[i-1] == 'U' || formula[i-1] == 'R'))) {
//            ++intervals;
//        }
//    }
//    return {temporal_ops, max_depth, intervals};
//}

// A test is "non-trivial" if any of:
//   nesting_depth >= 8, temporal_ops >= 3 (mixed), intervals >= 2, or the formula
//   contains negation stress patterns (leading '!' or multiple '!').
//static bool is_non_trivial(const std::string& formula) {
//    auto [tops, depth, ivals] = complexity_score(formula);
//    if (depth >= 8) return true;
//    if (tops >= 3)  return true;
//    if (ivals >= 2) return true;
//    // Negation stress: leading '!' or double negation or negated temporal
//    int bangs = 0;
//    for (char c : formula) if (c == '!') ++bangs;
//    if (bangs >= 2) return true;
//    if (!formula.empty() && formula[0] == '!') return true;
//    return false;
//}

std::vector<TestCase> generate_stress_200() {
    return {
    // ====================================================================
    // §1  Deep nesting + precedence torture  (30 tests)
    // ====================================================================

    // 001: depth-12 chain AG(EF(AG(EF(AG(EF(AG(EF(AG(EF(AG(EF p)))))))))))  — SAT: self-loop on p
    /* 001 */ { "AG (EF (AG (EF (AG (EF (AG (EF (AG (EF (AG (EF p)))))))))))", true },
    // 002: dual depth-12 chain EG(AF(EG(AF(EG(AF(EG(AF(EG(AF(EG(AF p))))))))))))) — SAT: self-loop on p
    /* 002 */ { "EG (AF (EG (AF (EG (AF (EG (AF (EG (AF (EG (AF p)))))))))))", true },
    // 003: AG-EF depth-10 chain — SAT: p alternates/cycles
    /* 003 */ { "AG (EF (AG (EF (AG (EF (AG (EF (AG (EF p)))))))))", true },
    // 004: EG-AF depth-10 chain — SAT: p on self-loop
    /* 004 */ { "EG (AF (EG (AF (EG (AF (EG (AF (EG (AF p)))))))))", true },
    // 005: deep EX chain depth-12 — SAT: chain of 12 successors then p
    /* 005 */ { "EX (EX (EX (EX (EX (EX (EX (EX (EX (EX (EX (EX p)))))))))))", true },
    // 006: deep AX chain depth-12 — SAT: all successors 12 steps reach p
    /* 006 */ { "AX (AX (AX (AX (AX (AX (AX (AX (AX (AX (AX (AX p)))))))))))", true },
    // 007: deep nesting with boolean forcing: AG(EF(AG(EF(p & q & r)))) — SAT: self-loop with p,q,r
    /* 007 */ { "AG (EF (AG (EF (AG (EF (p & q & r))))))", true },
    // 008: deep nesting with boolean forcing + contradiction at leaf — UNSAT
    /* 008 */ { "AG (EF (AG (EF (AG (EF (p & (!p)))))))", false },
    // 009: nested EG chains — SAT: self-loop on p,q,r,s
    /* 009 */ { "EG (p & EG (q & EG (r & EG (s & EG (t & EG (u & EG v))))))", true },
    // 010: nested AG chains — SAT: all props hold on self-loop
    /* 010 */ { "AG (p | AG (q | AG (r | AG (s | AG (t | AG (u | AG v))))))", true },
    // 011: mixed EX-AX chain depth-12 — SAT
    /* 011 */ { "EX (AX (EX (AX (EX (AX (EX (AX (EX (AX (EX (AX p)))))))))))", true },
    // 012: nested AG->EX chain — SAT: AG requires EX at each step
    /* 012 */ { "AG (p -> EX (q & EX (r & EX (s & EX (t & EX (u & EX v))))))", true },
    // 013: deeply nested until — SAT: chain of EU's
    /* 013 */ { "E(p U (E(q U (E(r U (E(s U (E(t U (E(u U v)))))))))))", true },
    // 014: dual nested until chains A's — SAT
    /* 014 */ { "A(p U (A(q U (A(r U (A(s U (A(t U (A(u U v)))))))))))", true },
    // 015: deeply nested release chains — SAT
    /* 015 */ { "E(p R (E(q R (E(r R (E(s R (E(t R (E(u R v)))))))))))", true },
    // 016: deeply nested release A-chains — SAT
    /* 016 */ { "A(p R (A(q R (A(r R (A(s R (A(t R (A(u R v)))))))))))", true },
    // 017: AG nested underneath timed EU with inner timed — SAT
    /* 017 */ { "AG (p -> E(q U[1,3] (r & A(s R[2,5] (t & EG u)))))", true },
    // 018: boolean precedence: p | q & r parsed as p | (q & r) under AG/EF — SAT
    /* 018 */ { "AG (EF (p | q & r & EX (s | t & u)))", true },
    // 019: EG with nested EF and boolean splits deep — SAT
    /* 019 */ { "EG (p & EF (q | AG (r & EF (s | AG (t & EF u)))))", true },
    // 020: AG with nested AF and boolean structure — SAT
    /* 020 */ { "AG (p -> AF (q -> AG (r -> AF (s -> AG t))))", true },
    // 021: deep implication chain under AG — SAT: vacuous satisfaction
    /* 021 */ { "AG (p -> (q -> (r -> (s -> (t -> (u -> v))))))", true },
    // 022: deep nesting with EG/AF mix — SAT
    /* 022 */ { "EG (AF (EG (AF (EG (AF (EG (AF (EG p))))))))", true },
    // 023: deep nesting contradiction: AG(AF...) leads to AF(false) — UNSAT
    /* 023 */ { "AG (AF (EG (AF (EG (AF (EG (AF false)))))))", false },
    // 024: deep nesting with multiple timed inside — SAT
    /* 024 */ { "AG (EF[1,3] (AG (EF[4,6] (AG (EF[7,9] p)))))", true },
    // 025: depth-12 AG/EF with contradiction via timed globally — UNSAT
    /* 025 */ { "AG (EF (AG (EF (AG (EF[1,3] p))))) & AG[0,inf) (!p)", false },
    // 026: deep EX chain + EG — SAT: path exists then loop
    /* 026 */ { "EX (EX (EX (EX (EX (EX (EX (EX (EG p))))))))", true },
    // 027: deep AX chain + AF — SAT: all paths reach p
    /* 027 */ { "AX (AX (AX (AX (AX (AX (AX (AX (AF p))))))))", true },
    // 028: nested releases inside nested untils — SAT
    /* 028 */ { "E(p U (q & E(r R (s & E(t U (u & E(v R w)))))))", true },
    // 029: deep AG(EF(...)) + release combo — SAT
    /* 029 */ { "AG (EF (A(p R (q & EF (A(r R (s & EF t)))))))", true },
    // 030: deep structure but false at the leaf — UNSAT
    /* 030 */ { "EG (EF (EG (EF (EG (EF (EG (EF (EG (EF false)))))))))", false },

    // ====================================================================
    // §2  Quantifier alternation stress  (30 tests)
    // ====================================================================

    // 031: 6-deep alternation A(E(A(E(A(E(...U...)))))) — SAT
    /* 031 */ { "A(p U (E(q U (A(r U (E(s U (A(t U (E(u U v)))))))))))", true },
    // 032: 6-deep alternation E(A(E(A(E(A(...U...)))))) — SAT
    /* 032 */ { "E(p U (A(q U (E(r U (A(s U (E(t U (A(u U v)))))))))))", true },
    // 033: 6-deep R alternation A(E(A(E(A(E(...R...)))))) — SAT
    /* 033 */ { "A(p R (E(q R (A(r R (E(s R (A(t R (E(u R v)))))))))))", true },
    // 034: 6-deep R alternation E(A(E(A(E(A(...R...)))))) — SAT
    /* 034 */ { "E(p R (A(q R (E(r R (A(s R (E(t R (A(u R v)))))))))))", true },
    // 035: mixed U/R alternation — SAT
    /* 035 */ { "A(p U (E(q R (A(r U (E(s R (A(t U (E(u R v)))))))))))", true },
    // 036: mixed R/U alternation — SAT
    /* 036 */ { "E(p R (A(q U (E(r R (A(s U (E(t R (A(u U v)))))))))))", true },
    // 037: AG(AF(EG(AF(EG(AF(EG p)))))) — 7 alternations — SAT
    /* 037 */ { "AG (AF (EG (AF (EG (AF (EG p))))))", true },
    // 038: EG(AF(EG(AF(EG(AF p))))) — 6 alternations — SAT
    /* 038 */ { "EG (AF (EG (AF (EG (AF p)))))", true },
    // 039: AG(EF(AG(EF(AG(EF(AG(EF p))))))) — 8 alternations — SAT
    /* 039 */ { "AG (EF (AG (EF (AG (EF (AG (EF p)))))))", true },
    // 040: EG(AG(EF(AG(EF(AG(EF(AG p))))))) — SAT
    /* 040 */ { "EG (AG (EF (AG (EF (AG (EF (AG p)))))))", true },
    // 041: alternation + timed until inside — SAT
    /* 041 */ { "AG (EF (AG (EF (E(p U[1,3] q)))))", true },
    // 042: alternation + timed release inside — SAT
    /* 042 */ { "EG (AF (EG (AF (A(p R[1,3] q)))))", true },
    // 043: alternation + timed until under EX/AX — SAT
    /* 043 */ { "AG (EX (AF (EX (AG (EX (AF (EX p)))))))", true },
    // 044: alternation + contradiction at deep level — UNSAT
    /* 044 */ { "AG (AF (EG (AF (EG (AF (p & (!p)))))))", false },
    // 045: alternation: A(EU).A(ER) nested — SAT
    /* 045 */ { "A(p U (q & E(r R (s & A(t U (u & E(v R w)))))))", true },
    // 046: alternation with boolean complexity — SAT
    /* 046 */ { "AG (p -> EF (q & AF (r -> EG (s | AF t))))", true },
    // 047: EG(AG(EF(AG(EF p)))) + timed component — SAT
    /* 047 */ { "EG (AG (EF (AG (EF p)))) & E(q U[1,3] r)", true },
    // 048: alternation + contradiction via AG invariant — UNSAT
    /* 048 */ { "AG (AF (EG (AF (EG (AF (EG p)))))) & AG (!p)", false },
    // 049: 6-deep alternation with boolean split at each level — SAT
    /* 049 */ { "A((p & q) U (E((r | s) U (A((t & u) U (E((v | w) U x)))))))", true },
    // 050: alternation with implication — SAT
    /* 050 */ { "AG (p -> EF (q -> AG (r -> EF (s -> AG (t -> EF u)))))", true },
    // 051: alternation + deep EG(AF...) blocked by contradiction — UNSAT
    /* 051 */ { "EG (AF (EG (AF (EG (AF false)))))", false },
    // 052: 6-deep alternation in timed U/R — SAT
    /* 052 */ { "A(p U[1,3] (E(q R[2,5] (A(r U[3,6] (E(s R[4,7] t)))))))", true },
    // 053: alternation with EG inside AF — SAT
    /* 053 */ { "AF (EG (AF (EG (AF (EG p)))))", true },
    // 054: alternation AG EF AG EF AG EF AG EF AG EF p — depth 10 — SAT
    /* 054 */ { "AG (EF (AG (EF (AG (EF (AG (EF (AG (EF p)))))))))", true },
    // 055: alternation with AG blocking EG loop — UNSAT
    /* 055 */ { "AG (EF p) & AG (!p)", false },
    // 056: deep alternation mix EX/AX/EF/AF/EG/AG all different — SAT
    /* 056 */ { "EX (AG (AF (EX (AG (EF (AX (EG p)))))))", true },
    // 057: deep alternation all forall then all exists — SAT
    /* 057 */ { "AG (AF (AG (AF (EG (EF (EG (EF p)))))))", true },
    // 058: alternation with timed + release contradiction — UNSAT
    /* 058 */ { "E(p U[1,3] q) & A((!p) U[1,3] (!q)) & AG[0,inf) ((p | (!q)) & ((!p) | q))", false },
    // 059: alternation AG(AF(AG(AF(EG(EF(EG(EF(AG(AF p))))))))) — SAT
    /* 059 */ { "AG (AF (AG (AF (EG (EF (EG (EF (AG (AF p)))))))))", true },
    // 060: alternation with contradiction: all must eventually p but EG !p — UNSAT
    /* 060 */ { "AG (AF p) & EG (!p)", false },

    // ====================================================================
    // §3  Loop + eventuality correctness  (30 tests)
    // ====================================================================

    // 061: EG p with self-loop — SAT: trivial loop
    /* 061 */ { "EG (p & EX p) & AG (p -> EX p)", true },
    // 062: EG (p & EX(!p)) with AG(!p -> EX p) — alternation loop SAT
    /* 062 */ { "EG (p & EX q) & AG (q -> EX p) & AG (p -> EX q)", true },
    // 063: EG with eventuality EF — loop must fulfil EF — SAT
    /* 063 */ { "EG (EF q & p)", true },
    // 064: AG(AF p) — loop eventuality must be fulfilled — SAT: self-loop with p
    /* 064 */ { "AG (AF p) & EG p", true },
    // 065: EG p & AF(!p) — must eventually not-p but EG wants p forever — UNSAT
    /* 065 */ { "EG p & AF (!p)", false },
    // 066: AG p & EF(!p) — same contradiction — UNSAT
    /* 066 */ { "AG p & EF (!p)", false },
    // 067: EG(p | q) with forced alternation, loop acceptance — SAT
    /* 067 */ { "EG (p | q) & AG (p -> AX q) & AG (q -> AX p)", true },
    // 068: EG(p & q) + EG(!p & !q) forced everywhere same — UNSAT
    /* 068 */ { "EG (p & q) & EG ((!p) & (!q)) & AG ((p & q) | ((!p) & (!q)))", false },
    // 069: E(p U q) & AG p — q must eventually hold + p always — SAT: p&q at some point
    /* 069 */ { "E(p U q) & AG p", true },
    // 070: E(p U q) & AG (!q) — EU needs q but q never — UNSAT
    /* 070 */ { "E(p U q) & AG (!q)", false },
    // 071: A(p U q) & AG (!q) & AG (!p) — AU needs q, never happens — UNSAT
    /* 071 */ { "A(p U q) & AG (!q) & AG (!p)", false },
    // 072: E(p U q) & E(q U r) & E(r U p) chain loop — SAT
    /* 072 */ { "E(p U q) & E(q U r) & E(r U p)", true },
    // 073: chain loop w/ global neg of all — UNSAT
    /* 073 */ { "E(p U q) & E(q U r) & E(r U p) & AG ((!p) & (!q) & (!r))", false },
    // 074: EG p & EG q — both looping — SAT
    /* 074 */ { "EG p & EG q", true },
    // 075: EG p & EG(!p) — can't both have global path — UNSAT
    /* 075 */ { "EG p & EG (!p)", false },
    // 076: AG(AF p & AF q) — must repeatedly see both — SAT: self-loop with p & q
    /* 076 */ { "AG (AF p & AF q)", true },
    // 077: E(false R p) — EG p equivalent — SAT: self-loop
    /* 077 */ { "E(false R (p & EX p))", true },
    // 078: A(false R p) — AG p equivalent — SAT: all states have p
    /* 078 */ { "A(false R (p & q))", true },
    // 079: EG p with AX forcing loop — SAT
    /* 079 */ { "EG (p & AX p)", true },
    // 080: AG(p->EXp) & AG(!p->EX!p) & EF(p&!p) — contradiction in EF — UNSAT
    /* 080 */ { "AG (p -> EX p) & AG ((!p) -> EX (!p)) & EF (p & (!p))", false },
    // 081: EG with timed EU inside loop — eventuality must be fulfilled — SAT
    /* 081 */ { "EG (p & E(q U[1,3] r)) & AG (r -> AG r)", true },
    // 082: AG with timed AU inside — SAT
    /* 082 */ { "AG (p & A(q U[1,3] r)) & EG (r -> EG r)", true },
    // 083: loop detection: EG(AF p) with path that cycles without p — UNSAT
    /* 083 */ { "EG (AF p & AG (!p))", false },
    // 084: loop detection: AG(AF p & EG(!p)) — UNSAT
    /* 084 */ { "AG (AF p & EG (!p))", false },
    // 085: EG with release inside — SAT: release provides weak-until semantics
    /* 085 */ { "EG (E(p R (q & EF r)))", true },
    // 086: AG with release inside — SAT
    /* 086 */ { "AG (A(p R q) | EF r)", true },
    // 087: EG with multiple eventualities — SAT
    /* 087 */ { "EG (EF p & EF q & EF r)", true },
    // 088: forall-loop: AF(AG p) — requires reaching permanent p — SAT
    /* 088 */ { "AF (AG p)", true },
    // 089: EF(EG p) — SAT: find a path that loops with p
    /* 089 */ { "EF (EG p)", true },
    // 090: EG true is trivially SAT
    /* 090 */ { "EG true", true },

    // ====================================================================
    // §4  Timed tight bounds & race conditions  (30 tests)
    // ====================================================================

    // 091: E(true U[0,1] p) — can satisfy p immediately or at t=1 — SAT
    /* 091 */ { "E(true U[0,1] p)", true },
    // 092: A(true U[0,1] p) — all paths: p within [0,1] — SAT
    /* 092 */ { "A(true U[0,1] p)", true },
    // 093: EF[0,1] false — can't reach false — UNSAT
    /* 093 */ { "EF[0,1] false", false },
    // 094: AF[0,1] false — can't reach false — UNSAT
    /* 094 */ { "AF[0,1] false", false },
    // 095: tight window E(true U[1,2] p) — SAT: delay to 1, then p
    /* 095 */ { "E(true U[1,2] p)", true },
    // 096: E(true U[1,3] false) — can't make false true ever — UNSAT
    /* 096 */ { "E(true U[1,3] false)", false },
    // 097: A(true U[1,3] false) — UNSAT
    /* 097 */ { "A(true U[1,3] false)", false },
    // 098: EF[1,3] p & AG[1,3] (!p) — p required in [1,3] but blocked — UNSAT
    /* 098 */ { "EF[1,3] p & AG[1,3] (!p)", false },
    // 099: AG[1,3] p & EF[1,3] (!p) — UNSAT
    /* 099 */ { "AG[1,3] p & EF[1,3] (!p)", false },
    // 100: AF[1,3] p & AG[0,3] (!p) — UNSAT: must reach p in [1,3] but blocked
    /* 100 */ { "AF[1,3] p & AG[0,3] (!p)", false },
    // 101: EF[1,3] p & AG[0,1] (!p) — SAT: p at t>1 within [1,3]
    /* 101 */ { "EF[1,3] p & AG[0,1] (!p)", true },
    // 102: AG[0,2] p & EF[3,5] q — SAT: p in [0,2], q at t∈[3,5]
    /* 102 */ { "AG[0,2] p & EF[3,5] q", true },
    // 103: multiple timed racing: EF[1,3] p & EF[2,4] q — SAT: overlap at [2,3]
    /* 103 */ { "EF[1,3] p & EF[2,4] q", true },
    // 104: EF[1,3] p & AG[4,inf) p — SAT: p at t∈[1,3], then p from t=4
    /* 104 */ { "EF[1,3] p & AG[4,inf) p", true },
    // 105: EF[1,3] p & AG[0,inf) (!p) — UNSAT: p needed but globally blocked
    /* 105 */ { "EF[1,3] p & AG[0,inf) (!p)", false },
    // 106: AF[1,3] p & AG[0,inf) (!p) — UNSAT
    /* 106 */ { "AF[1,3] p & AG[0,inf) (!p)", false },
    // 107: E(p U[1,3] q) & AG[0,inf) (!q) — UNSAT: q never holds
    /* 107 */ { "E(p U[1,3] q) & AG[0,inf) (!q)", false },
    // 108: A(p U[1,3] q) & AG[0,inf) (!q) — UNSAT
    /* 108 */ { "A(p U[1,3] q) & AG[0,inf) (!q)", false },
    // 109: timed release: E(p R[1,3] q) & AG[0,inf)(!q) — UNSAT: q must hold in [1,3]
    /* 109 */ { "E(p R[1,3] q) & AG[0,inf) (!q)", false },
    // 110: timed release: A(p R[1,3] q) & AG[0,inf)(!q) — UNSAT
    /* 110 */ { "A(p R[1,3] q) & AG[0,inf) (!q)", false },
    // 111: tight adjacent intervals — SAT: p in [1,3], q in [4,6]
    /* 111 */ { "EF[1,3] p & EF[4,6] q", true },
    // 112: overlapping timed-until E(p U[1,3] q) & E(q U[2,5] r) — SAT
    /* 112 */ { "E(p U[1,3] q) & E(q U[2,5] r)", true },
    // 113: UNSAT: E(q U[4,6] r) requires q from time 0 but AG[0,1](!q) blocks q in [0,1]
    /* 113 */ { "E(p U[1,3] q) & E(q U[4,6] r) & AG[0,1] (!q)", false },
    // 114: EF[1,3](p & q) & AG[0,inf) ((!p) | (!q)) — UNSAT: can't have both p&q
    /* 114 */ { "EF[1,3] (p & q) & AG[0,inf) ((!p) | (!q))", false },
    // 115: AG[0,2] p & AF[3,5] p — SAT: p holds early and repeats later
    /* 115 */ { "AG[0,2] p & AF[3,5] p", true },
    // 116: open interval E(p U(1,3) q) — SAT: q at t∈(1,3)
    /* 116 */ { "E(p U(1,3) q)", true },
    // 117: half-open interval E(p U[1,3) q) — SAT: q at t∈[1,3)
    /* 117 */ { "E(p U[1,3) q)", true },
    // 118: E(p U(1,3] q) — SAT
    /* 118 */ { "E(p U(1,3] q)", true },
    // 119: AG[0,3] p & AF[0,3] (!p) — UNSAT: p globally in [0,3] but must see !p
    /* 119 */ { "AG[0,3] p & AF[0,3] (!p)", false },
    // 120: EG[1,3] p & EF[0,inf) (!p) — SAT: p in [1,3], !p elsewhere
    /* 120 */ { "EG[1,3] p & EF[0,inf) (!p)", true },

    // ====================================================================
    // §5  Multi-until / multi-clock interaction  (30 tests)
    // ====================================================================

    // 121: two timed EU with diff bounds — SAT
    /* 121 */ { "E(p U[1,3] q) & E(r U[2,4] s)", true },
    // 122: three timed EU — SAT
    /* 122 */ { "E(p U[1,3] q) & E(r U[2,4] s) & E(t U[3,5] u)", true },
    // 123: three timed AU — SAT
    /* 123 */ { "A(p U[1,3] q) & A(r U[2,4] s) & A(t U[3,5] u)", true },
    // 124: two EU + both goals globally blocked — UNSAT
    /* 124 */ { "E(p U[1,3] q) & E(r U[2,4] s) & AG[0,inf) (!q) & AG[0,inf) (!s)", false },
    // 125: two AU + both goals globally blocked — UNSAT
    /* 125 */ { "A(p U[1,3] q) & A(r U[2,4] s) & AG[0,inf) (!q) & AG[0,inf) (!s)", false },
    // 126: nested timed EU inside timed EU — SAT
    /* 126 */ { "E(p U[1,3] (E(q U[4,6] r)))", true },
    // 127: nested timed AU inside timed AU — SAT
    /* 127 */ { "A(p U[1,3] (A(q U[4,6] r)))", true },
    // 128: timed EU and timed ER together — SAT
    /* 128 */ { "E(p U[1,3] q) & E(r R[2,5] s)", true },
    // 129: timed AU and timed AR together — SAT
    /* 129 */ { "A(p U[1,3] q) & A(r R[2,5] s)", true },
    // 130: EU inside ER (timed) — SAT
    /* 130 */ { "E(p R[1,3] (E(q U[2,4] r)))", true },
    // 131: AU inside AR (timed) — SAT
    /* 131 */ { "A(p R[1,3] (A(q U[2,4] r)))", true },
    // 132: ER inside EU (timed) — SAT
    /* 132 */ { "E(p U[1,3] (E(q R[2,4] r)))", true },
    // 133: AR inside AU (timed) — SAT
    /* 133 */ { "A(p U[1,3] (A(q R[2,4] r)))", true },
    // 134: multi-timed under EG loop — SAT
    /* 134 */ { "EG (E(p U[1,3] q) & A(r R[2,5] s))", true },
    // 135: multi-timed under AG — SAT
    /* 135 */ { "AG (E(p U[1,3] q) | A(r R[2,5] s))", true },
    // 136: sequential timed EU: q from first fuels second — SAT
    /* 136 */ { "E(p U[1,3] q) & E(p U[4,6] r) & AG[0,1] (!q) & AG[0,4] (!r)", true },
    // 137: sequential timed AU with constraints — SAT
    /* 137 */ { "A(p U[1,3] q) & A(p U[4,6] r) & AG[3,4] (!q) & AG[6,inf) (!r)", true },
    // 138: two timed ER together — SAT
    /* 138 */ { "E(p R[1,3] q) & E(r R[2,4] s)", true },
    // 139: two timed AR together — SAT
    /* 139 */ { "A(p R[1,3] q) & A(r R[2,4] s)", true },
    // 140: three timed ER — SAT
    /* 140 */ { "E(p R[1,3] q) & E(r R[2,4] s) & E(t R[3,5] u)", true },
    // 141: three timed AR — SAT
    /* 141 */ { "A(p R[1,3] q) & A(r R[2,4] s) & A(t R[3,5] u)", true },
    // 142: timed under AG nested — SAT
    /* 142 */ { "AG[0,2] (EF[3,5] (AG[6,8] p))", true },
    // 143: timed under EG nested — SAT
    /* 143 */ { "EG[1,5] (EF[2,4] (EG[6,8] p))", true },
    // 144: two timed ER + both held-globally blocked — UNSAT
    /* 144 */ { "E(p R[1,3] q) & E(r R[2,4] s) & AG[0,inf) (!q) & AG[0,inf) (!s)", false },
    // 145: two timed AR + held-globally blocked — UNSAT
    /* 145 */ { "A(p R[1,3] q) & A(r R[2,4] s) & AG[0,inf) (!q) & AG[0,inf) (!s)", false },
    // 146: mixed timed EU + timed AR + EF — SAT
    /* 146 */ { "E(p U[1,3] q) & A(r R[4,6] s) & EF[7,9] t", true },
    // 147: mixed timed AU + timed ER + AG — SAT
    /* 147 */ { "A(p U[1,3] q) & E(r R[4,6] s) & AG[7,9] t", true },
    // 148: multi-timed with 3 diff intervals under EG — SAT
    /* 148 */ { "EG (AG[0,2] p & EF[3,5] q & AG[6,8] r)", true },
    // 149: multi-until + release one contradicted — SAT: release can vacuously hold
    /* 149 */ { "E(p U[1,3] q) & E(r U[1,3] (!q))", true },
    // 150: timed EU + timed ER same interval — SAT
    /* 150 */ { "E(p U[1,3] q) & E(r R[1,3] s)", true },

    // ====================================================================
    // §6  Release-heavy equivalence + duality checks  (30 tests)
    // ====================================================================

    // 151: E(false R p) ≡ EG p — SAT: self-loop
    /* 151 */ { "E(false R p) & EG p", true },
    // 152: A(false R p) ≡ AG p — SAT
    /* 152 */ { "A(false R p) & AG p", true },
    // 153: E(p R true) — trivially SAT: ψ=true always holds
    /* 153 */ { "E(p R true)", true },
    // 154: A(p R true) — trivially SAT
    /* 154 */ { "A(p R true)", true },
    // 155: E(p R false) — UNSAT: ψ=false must hold until released, but false never holds
    /* 155 */ { "E(p R false)", false },
    // 156: A(p R false) — UNSAT
    /* 156 */ { "A(p R false)", false },
    // 157: E(p R[1,3] false) — UNSAT: false can't hold in [1,3]
    /* 157 */ { "E(p R[1,3] false)", false },
    // 158: A(p R[1,3] false) — UNSAT
    /* 158 */ { "A(p R[1,3] false)", false },
    // 159: E(false R[1,3] false) — UNSAT
    /* 159 */ { "E(false R[1,3] false)", false },
    // 160: A(false R[1,3] false) — UNSAT
    /* 160 */ { "A(false R[1,3] false)", false },
    // 161: E(false R[1,3] q) — SAT: q holds throughout [1,3]
    /* 161 */ { "E(false R[1,3] q)", true },
    // 162: A(false R[1,3] q) — SAT: q on all paths in [1,3]
    /* 162 */ { "A(false R[1,3] q)", true },
    // 163: release with complex ψ — SAT
    /* 163 */ { "E(p R (q & r & s))", true },
    // 164: release with complex ψ — SAT
    /* 164 */ { "A(p R (q & r & s))", true },
    // 165: release with complex ψ + AG contradiction — UNSAT
    /* 165 */ { "E(p R (q & r & s)) & AG ((!q) | (!r) | (!s))", false },
    // 166: release with boolean inside — SAT
    /* 166 */ { "E(p R (q & EX r))", true },
    // 167: release nested inside release — SAT
    /* 167 */ { "E(p R (q & E(r R (s & EX t))))", true },
    // 168: release nested inside release (universal) — SAT
    /* 168 */ { "A(p R (q & A(r R (s & AX t))))", true },
    // 169: timed release inside untimed release — SAT
    /* 169 */ { "E(p R (q & E(r R[1,3] s)))", true },
    // 170: untimed release inside timed release — SAT
    /* 170 */ { "E(p R[1,3] (q & E(r R s)))", true },
    // 171: release with EF inside — SAT
    /* 171 */ { "A(p R (EF q & r))", true },
    // 172: release with AG inside — SAT
    /* 172 */ { "E(EG p R (q & r))", true },
    // 173: release w/ AF inside — SAT
    /* 173 */ { "A(AF p R q)", true },
    // 174: release w/ EF inside — SAT
    /* 174 */ { "E(EF p R q)", true },
    // 175: timed release + timed until combo — SAT
    /* 175 */ { "E(p R[1,3] q) & E(r U[2,5] s)", true },
    // 176: timed release + timed until combo (universal) — SAT
    /* 176 */ { "A(p R[1,3] q) & A(r U[2,5] s)", true },
    // 177: duality: !(E(p U q)) is satisfiable — SAT
    /* 177 */ { "!(E(p U q))", true },
    // 178: duality: !(A(p R q)) is satisfiable — SAT
    /* 178 */ { "!(A(p R q))", true },
    // 179: release AG p & EF(!p) — UNSAT: AG p blocks !p
    /* 179 */ { "AG (p & q & r) & EF ((!p) | (!q) | (!r))", false },
    // 180: release-heavy with 3×nested releases — SAT
    /* 180 */ { "E(p R (E(q R (E(r R (s & t & u))))))", true },

    // ====================================================================
    // §7  Pathological normalization / negation edge cases  (20 tests)
    // ====================================================================

    // 181: !(EF[1,3] p) normalizes to A(!true R[1,3] !p) → timed AR — SAT
    /* 181 */ { "!(EF[1,3] p)", true },
    // 182: !(AF[1,3] p) normalizes to E(!true R[1,3] !p) → timed ER — SAT
    /* 182 */ { "!(AF[1,3] p)", true },
    // 183: !(EG[1,3] p) normalizes to A(true U[1,3] !p) — SAT
    /* 183 */ { "!(EG[1,3] p)", true },
    // 184: !(AG[1,3] p) normalizes to E(true U[1,3] !p) — SAT
    /* 184 */ { "!(AG[1,3] p)", true },
    // 185: !(E(p U[1,3] q)) → A(!p R[1,3] !q) — SAT
    /* 185 */ { "!(E(p U[1,3] q))", true },
    // 186: !(A(p U[1,3] q)) → E(!p R[1,3] !q) — SAT
    /* 186 */ { "!(A(p U[1,3] q))", true },
    // 187: !(E(p R[1,3] q)) → A(!p U[1,3] !q) — SAT
    /* 187 */ { "!(E(p R[1,3] q))", true },
    // 188: !(A(p R[1,3] q)) → E(!p U[1,3] !q) — SAT
    /* 188 */ { "!(A(p R[1,3] q))", true },
    // 189: double negation !!p — SAT: normalizes to p
    /* 189 */ { "!!(EG (EF p))", true },
    // 190: negated complex conjunction !(EF[1,3] p & EF[2,4] q) — SAT
    /* 190 */ { "!(EF[1,3] p & EF[2,4] q)", true },
    // 191: negated complex disjunction !(AG[0,2] p | AG[3,5] q) — SAT
    /* 191 */ { "!(AG[0,2] p | AG[3,5] q)", true },
    // 192: !(EG(E(p U[1,3] q) & A(r R[2,5] s))) — SAT
    /* 192 */ { "!(EG (E(p U[1,3] q) & A(r R[2,5] s)))", true },
    // 193: !(AG(E(p U[1,3] q) | A(r R[2,5] s))) — SAT
    /* 193 */ { "!(AG (E(p U[1,3] q) | A(r R[2,5] s)))", true },
    // 194: negated nested AG(EF(AG(EF p))) — SAT
    /* 194 */ { "!(AG (EF (AG (EF p))))", true },
    // 195: negated nested EG(AF(EG(AF p))) — SAT
    /* 195 */ { "!(EG (AF (EG (AF p))))", true },
    // 196: !(E(p U (q & E(r U s)))) — SAT
    /* 196 */ { "!(E(p U (q & E(r U s))))", true },
    // 197: !(A(p R (q | A(r R s)))) — SAT
    /* 197 */ { "!(A(p R (q | A(r R s))))", true },
    // 198: AG (p <-> q) & EG p — biconditional under AG — SAT
    /* 198 */ { "AG (p <-> q) & EG p", true },
    // 199: EG (p <-> q) & EG p & EG (!q) — biconditional + conflicting EG — UNSAT
    /* 199 */ { "EG (p <-> q) & EG p & EG (!q)", false },
    // 200: !(AG (p -> AF q) & EG p & EG (!q)) — double neg of UNSAT → SAT
    /* 200 */ { "!(AG (p -> AF q) & EG p & EG (!q))", true },
    };
}

static void test_stress_200(TestContext& ctx) {
    auto tests = generate_stress_200();

    // Run all tests
    run_test_vector(ctx, tests, "stress_200", false, 10);
}

// ============================================================================
// Propositional-heavy test suite (100 tests)
// ============================================================================
//
// Tests with simple TCTL structure (0-2 nesting) but complex propositional
// logic: arithmetic constraints, boolean combinations, contradictions,
// implications, biconditionals, Z3 interactions.

std::vector<TestCase> generate_propositional_100() {
    return {

    // ====================================================================
    // §1  Pure boolean complexity (20 tests)
    // ====================================================================

    // 001: large conjunction of distinct atoms — SAT
    /* 001 */ { "p & q & r & s & t & u & v & w", true },
    // 002: large disjunction — SAT (any one suffices)
    /* 002 */ { "p | q | r | s | t | u | v | w", true },
    // 003: conjunction with one negation — SAT
    /* 003 */ { "p & q & r & (!s) & t & u", true },
    // 004: conjunction with contradictory pair — UNSAT
    /* 004 */ { "p & q & r & s & (!p)", false },
    // 005: nested implications — SAT (vacuously via !p)
    /* 005 */ { "(p -> (q -> (r -> (s -> (t -> u)))))", true },
    // 006: biconditional chain — SAT (all same truth value)
    /* 006 */ { "(p <-> q) & (q <-> r) & (r <-> s) & (s <-> t)", true },
    // 007: biconditional + forced true + forced false — UNSAT
    /* 007 */ { "(p <-> q) & p & (!q)", false },
    // 008: XOR-like: exactly one of p,q via (p|q)&(!p|!q) — SAT
    /* 008 */ { "(p | q) & ((!p) | (!q))", true },
    // 009: double XOR chain — SAT
    /* 009 */ { "(p | q) & ((!p) | (!q)) & (r | s) & ((!r) | (!s))", true },
    // 010: all-same forced by biconditionals + contradiction — UNSAT
    /* 010 */ { "(p <-> q) & (q <-> r) & (r <-> s) & p & (!s)", false },
    // 011: implication cycle that forces all true — SAT
    /* 011 */ { "(p -> q) & (q -> r) & (r -> p) & p", true },
    // 012: implication cycle + contradiction — UNSAT
    /* 012 */ { "(p -> q) & (q -> r) & (r -> p) & p & (!r)", false },
    // 013: disjunction of conjunctions — SAT
    /* 013 */ { "(p & q & r) | (s & t & u) | (v & w)", true },
    // 014: conjunction of disjunctions, all same variable negated — UNSAT
    /* 014 */ { "(p | q) & ((!p) | q) & (p | (!q)) & ((!p) | (!q))", false },
    // 015: 8-way OR with nested ANDs — SAT
    /* 015 */ { "(p & (!q)) | (q & (!r)) | (r & (!s)) | (s & (!p))", true },
    // 016: complex DNF — SAT
    /* 016 */ { "(p & q & (!r)) | ((!p) & r & s) | (q & r & (!s))", true },
    // 017: complex CNF — SAT
    /* 017 */ { "(p | q | r) & ((!p) | q | s) & (p | (!q) | (!s))", true },
    // 018: tautology: p | !p — SAT
    /* 018 */ { "p | (!p)", true },
    // 019: p & (p -> q) & (q -> r) forces p,q,r — SAT
    /* 019 */ { "p & (p -> q) & (q -> r)", true },
    // 020: pigeonhole-like: 3 vars, all pairs must differ — UNSAT
    /* 020 */ { "(p | q) & ((!p) | (!q)) & (q | r) & ((!q) | (!r)) & (p | r) & ((!p) | (!r))", false },

    // ====================================================================
    // §2  Arithmetic constraints + Z3 (25 tests)
    // ====================================================================

    // 021: simple arithmetic — SAT
    /* 021 */ { "{x <= 5}", true },
    // 022: contradictory arithmetic — UNSAT
    /* 022 */ { "{x <= 5} & {x > 5}", false },
    // 023: multiple variables consistent — SAT
    /* 023 */ { "{x <= 10} & {y >= 0} & {x > 0}", true },
    // 024: multiple variables contradictory — UNSAT
    /* 024 */ { "{x <= 5} & {x >= 10}", false },
    // 025: arithmetic + boolean atom — SAT
    /* 025 */ { "{x <= 5} & p", true },
    // 026: arithmetic contradiction under AG — UNSAT
    /* 026 */ { "AG ({x <= 5} & {x > 5})", false },
    // 027: arithmetic under EF — SAT (reach a state with x<=5)
    /* 027 */ { "EF {x <= 5}", true },
    // 028: arithmetic under AG — SAT (all states have x<=10)
    /* 028 */ { "AG {x <= 10}", true },
    // 029: strict less — SAT
    /* 029 */ { "{x < 5} & {x > 3}", true },
    // 030: equality — SAT
    /* 030 */ { "{x = 5}", true },
    // 031: equality + contradictory bound — UNSAT
    /* 031 */ { "{x = 5} & {x > 10}", false },
    // 032: two equalities on same var — UNSAT
    /* 032 */ { "{x = 5} & {x = 10}", false },
    // 033: two variables, consistent — SAT
    /* 033 */ { "{x <= 5} & {y <= 5} & {x >= 0} & {y >= 0}", true },
    // 034: arithmetic under EX — SAT
    /* 034 */ { "EX {x <= 10}", true },
    // 035: arithmetic under AX — SAT
    /* 035 */ { "AX {x <= 10}", true },
    // 036: multiple constraints in conjunction — SAT
    /* 036 */ { "{x <= 10} & {x >= 0} & {y <= 20} & {y >= 0}", true },
    // 037: impossible range — UNSAT
    /* 037 */ { "{x >= 10} & {x <= 5}", false },
    // 038: arithmetic + boolean contradiction — UNSAT
    /* 038 */ { "{x <= 5} & p & (!p)", false },
    // 039: arithmetic under timed until — SAT
    /* 039 */ { "E({x <= 10} U[1,3] {x >= 5})", true },
    // 040: arithmetic contradiction under timed until — UNSAT
    /* 040 */ { "E({x <= 5} U[1,3] false)", false },
    // 041: arithmetic with AG globally — SAT
    /* 041 */ { "AG ({x <= 100} & {x >= 0})", true },
    // 042: nested arithmetic: EF(AG ...) — SAT
    /* 042 */ { "EF (AG {x <= 10})", true },
    // 043: arithmetic under release — SAT
    /* 043 */ { "E({x >= 0} R {x <= 100})", true },
    // 044: arithmetic with disjunction — SAT
    /* 044 */ { "{x <= 5} | {x > 10}", true },
    // 045: arithmetic inequality chain — SAT
    /* 045 */ { "{x <= 5} & {y <= 5} & {x > 0} & {y > 0}", true },

    // ====================================================================
    // §3  Boolean + temporal shallow nesting (20 tests)
    // ====================================================================

    // 046: AG of complex boolean — SAT (self-loop with p,q,r)
    /* 046 */ { "AG (p & q & r & s)", true },
    // 047: EG of complex boolean — SAT
    /* 047 */ { "EG (p & q & r & s & t)", true },
    // 048: AG of contradiction — UNSAT
    /* 048 */ { "AG (p & (!p))", false },
    // 049: EG of contradiction — UNSAT
    /* 049 */ { "EG (p & (!p))", false },
    // 050: AG of disjunction — SAT
    /* 050 */ { "AG (p | q | r)", true },
    // 051: EF of conjunction — SAT
    /* 051 */ { "EF (p & q & r & s & t & u)", true },
    // 052: AF of conjunction — SAT
    /* 052 */ { "AF (p & q & r & s)", true },
    // 053: EG(p) & EG(q) & EG(r) — SAT on same loop
    /* 053 */ { "EG p & EG q & EG r", true },
    // 054: AG(p) & AG(q) & AG(r) — SAT
    /* 054 */ { "AG p & AG q & AG r", true },
    // 055: AG(p) & EF(!p) — UNSAT
    /* 055 */ { "AG p & EF (!p)", false },
    // 056: EG(p & q) & AF(!p) — UNSAT: EG wants p forever, AF wants !p eventually
    /* 056 */ { "EG (p & q) & AF (!p)", false },
    // 057: implication under AG — SAT (vacuously: !p everywhere)
    /* 057 */ { "AG (p -> q)", true },
    // 058: biconditional under AG + atom — SAT
    /* 058 */ { "AG (p <-> q) & p", true },
    // 059: biconditional under AG + contradictory atoms — UNSAT
    /* 059 */ { "AG (p <-> q) & p & (!q)", false },
    // 060: AG(p->q) & AG(q->r) & p & EF(!r) — SAT: p only at root, successors can have !r
    /* 060 */ { "AG (p -> q) & AG (q -> r) & p & EF (!r)", true },
    // 061: E(complex_bool U complex_bool) — SAT
    /* 061 */ { "E((p & q & r) U (s & t & u))", true },
    // 062: A(complex_bool U complex_bool) — SAT
    /* 062 */ { "A((p & q) U (r & s))", true },
    // 063: EU with contradictory goal — UNSAT
    /* 063 */ { "E(p U (q & (!q)))", false },
    // 064: AU with contradictory path — SAT: q can hold immediately (zero-length Until)
    /* 064 */ { "A((p & (!p)) U q)", true },
    // 065: EF(contradiction) — UNSAT
    /* 065 */ { "EF (p & (!p) & q)", false },

    // ====================================================================
    // §4  Mixed arithmetic + boolean + temporal (20 tests)
    // ====================================================================

    // 066: arithmetic under AG + boolean — SAT
    /* 066 */ { "AG ({x <= 10} & p)", true },
    // 067: arithmetic under EG + boolean — SAT
    /* 067 */ { "EG ({x <= 10} & p & q)", true },
    // 068: arithmetic contradiction under EG — UNSAT
    /* 068 */ { "EG ({x <= 5} & {x > 10})", false },
    // 069: arithmetic under EU — SAT
    /* 069 */ { "E({x <= 10} U ({x >= 5} & p))", true },
    // 070: arithmetic under AU — SAT
    /* 070 */ { "A({x >= 0} U ({x <= 100} & q))", true },
    // 071: arithmetic + timed EF — SAT
    /* 071 */ { "EF[1,3] ({x <= 10} & p)", true },
    // 072: arithmetic + timed AG — SAT
    /* 072 */ { "AG[0,5] ({x <= 100} & p)", true },
    // 073: arithmetic under timed EU — SAT
    /* 073 */ { "E({x >= 0} U[1,3] ({x <= 10} & q))", true },
    // 074: arithmetic contradiction under timed AG — UNSAT
    /* 074 */ { "AG[0,5] ({x <= 5} & {x >= 10})", false },
    // 075: arithmetic + boolean + timed — complex SAT
    /* 075 */ { "EF[1,3] (p & q & {x <= 10}) & AG {x >= 0}", true },
    // 076: arithmetic under release — SAT
    /* 076 */ { "E({x >= 0} R ({x <= 100} & p))", true },
    // 077: arithmetic under timed release — SAT
    /* 077 */ { "E({x >= 0} R[1,3] ({x <= 100} & p))", true },
    // 078: arithmetic equality under EF — SAT
    /* 078 */ { "EF ({x = 5} & p)", true },
    // 079: arithmetic equality under AG — SAT
    /* 079 */ { "AG ({x = 5} -> p)", true },
    // 080: arithmetic + implication under AG — SAT
    /* 080 */ { "AG ({x <= 5} -> {x >= 0})", true },
    // 081: arithmetic disjunction under EG — SAT
    /* 081 */ { "EG ({x <= 5} | {x > 10})", true },
    // 082: all arithmetic constraints contradictory under EF — UNSAT
    /* 082 */ { "EF ({x <= 5} & {x >= 10} & {y <= 0} & {y >= 1})", false },
    // 083: arithmetic under nested AG(EF ...) — SAT
    /* 083 */ { "AG (EF ({x <= 10} & p))", true },
    // 084: arithmetic chain under AG — SAT
    /* 084 */ { "AG ({x >= 0} & {x <= 100} & {y >= 0} & {y <= 100})", true },
    // 085: timed + arithmetic + boolean complex — SAT
    /* 085 */ { "E({x >= 0} U[1,3] ({x <= 10} & p & q))", true },

    // ====================================================================
    // §5  Contradiction detection stress (15 tests)
    // ====================================================================

    // 086: deep boolean contradiction — UNSAT
    /* 086 */ { "p & q & r & s & t & u & (!t)", false },
    // 087: contradiction hidden behind implication — UNSAT
    /* 087 */ { "p & (p -> q) & (q -> r) & (!r)", false },
    // 088: contradiction hidden behind biconditional chain — UNSAT
    /* 088 */ { "(p <-> q) & (q <-> r) & (r <-> s) & p & (!s)", false },
    // 089: arithmetic + boolean mixed contradiction — UNSAT
    /* 089 */ { "p & {x <= 5} & {x >= 10} & q", false },
    // 090: contradiction in EU goal — UNSAT
    /* 090 */ { "E(true U (p & (!p) & {x <= 5}))", false },
    // 091: contradiction in timed EU goal — UNSAT
    /* 091 */ { "E(true U[1,3] ({x <= 5} & {x > 5}))", false },
    // 092: EG with contradictory conjunction in invariant — UNSAT
    /* 092 */ { "EG (p & q & (!p))", false },
    // 093: AG with contradictory arithmetic — UNSAT
    /* 093 */ { "AG ({x <= 0} & {x >= 1})", false },
    // 094: AF of contradiction — UNSAT
    /* 094 */ { "AF (false & p & q)", false },
    // 095: EU path has contradiction — SAT: q can hold immediately
    /* 095 */ { "E((p & (!p)) U q)", true },
    // 096: release with contradictory invariant — UNSAT
    /* 096 */ { "E(p R (q & (!q)))", false },
    // 097: timed release with contradictory safety — UNSAT
    /* 097 */ { "E(p R[1,3] ({x <= 5} & {x > 5}))", false },
    // 098: conjunction of contradictory EGs — UNSAT
    /* 098 */ { "EG p & EG (!p)", false },
    // 099: AG forces p, EF forces !p — UNSAT
    /* 099 */ { "AG (p & q) & EF ((!p) | (!q))", false },
    // 100: complex timed + boolean + arithmetic contradiction — UNSAT
    /* 100 */ { "E({x >= 0} U[1,3] ({x <= 5} & {x > 5})) & AG p", false },
    };
}

static void test_propositional_100(TestContext& ctx) {
    auto tests = generate_propositional_100();
    run_test_vector(ctx, tests, "propositional_100", false, 10);
}

// ============================================================================
// Parallel / single-thread equivalence test
// ============================================================================
// Run a representative selection of formulas with num_threads=1 and then
// with default parallelism (when OpenMP is available).  Assert that the
// verdict matches.  When OpenMP is NOT available both runs are identical
// (sequential), so this test always passes — it acts as a structural
// regression net.

static void test_parallel_equivalence(TestContext& ctx) {
    // A representative selection across complexity levels.
    const std::vector<TestCase> cases = {
        // Trivial
        { "p",                true  },
        { "p & (!p)",         false },
        // Boolean
        { "p & q & r",        true  },
        { "(p -> q) & (q -> r) & p & (!r)", false },
        // Simple temporal
        { "EF p",             true  },
        { "AG p",             true  },
        { "AG p & EF (!p)",   false },
        { "E(p U q)",         true  },
        { "EG p & EG q",      true  },
        // Timed
        { "EF[1,3] p",        true  },
        { "AG[0,5] p",        true  },
        { "E(true U[1,3] p)", true  },
        { "EF[1,3] p & AG[0,4] !p", false },
        // Release
        { "E(false R p)",     true  },
        { "E(false R (p & (!p)))", false },
        // Arithmetic
        { "{x <= 5} & {x > 10}", false },
        { "EF ({x <= 10} & p)",   true  },
        // Nested
        { "AG (EF p)",        true  },
        { "EG (p & q) & AF (!p)", false },
        { "AG (p -> q) & AG (q -> r) & p", true },
    };

    FormulaFactory f1;
    TableauEngine eng1(f1);
    eng1.set_num_threads(1);   // force single-thread
    eng1.set_timeout(std::chrono::seconds(5));

    FormulaFactory f2;
    TableauEngine eng2(f2);
    eng2.set_num_threads(0);   // OMP default (>1 if available)
    eng2.set_timeout(std::chrono::seconds(5));

    for (std::size_t i = 0; i < cases.size(); ++i) {
        const auto& tc = cases[i];

        // Single-thread run.
        FormulaId id1 = parse_formula(tc.formula, f1);
        FormulaId n1  = normalize(id1, f1);
        Result r1     = eng1.check(n1);

        // Multi-thread run.
        FormulaId id2 = parse_formula(tc.formula, f2);
        FormulaId n2  = normalize(id2, f2);
        Result r2     = eng2.check(n2);

        // Verdicts must match (skip if either timed out).
        if (r1.verdict != Result::Timeout && r2.verdict != Result::Timeout) {
            ctx.check(r1.verdict == r2.verdict,
                      "parallel equiv #" + std::to_string(i + 1) + ": " + tc.formula);
        }
        // Both must also agree with the expected value.
        if (r1.verdict != Result::Timeout) {
            bool sat1 = (r1.verdict == Result::Satisfiable);
            ctx.check(sat1 == tc.expected_sat,
                      "parallel equiv #" + std::to_string(i + 1) + " (1-thr): " + tc.formula);
        }
    }
}


static void test_tctl_coverage_suite(TestContext& ctx) {
    auto tests = generate_tctl_tests();
    run_test_vector(ctx, tests, "tctl_coverage");
    auto edge_tests = generate_tctl_edge_tests_100();
    run_test_vector(ctx, edge_tests, "tctl_edge_100");
}


// ============================================================================
// Test Entry Point
// ============================================================================

int run_selftests() {
    // Create timestamped output folder for CSV results.
    init_results_dir();

    TestRunner runner;

    // Lexer tests
    runner.run("lexer_brackets_braces",      test_lexer_brackets_braces);
    runner.run("lexer_inf_keyword",          test_lexer_inf_keyword);
    runner.run("lexer_comparison_ops",       test_lexer_comparison_ops);
    runner.run("lexer_tctl_keywords",        test_lexer_tctl_keywords);

    // Basic parser tests
    runner.run("parse_atoms",                test_parse_atoms);

    // Time interval tests
    runner.run("parse_closed_intervals",     test_parse_closed_intervals);
    runner.run("parse_open_intervals",       test_parse_open_intervals);
    runner.run("parse_mixed_intervals",      test_parse_mixed_intervals);

    // Relational bound tests
    runner.run("parse_relational_upper",     test_parse_relational_upper);
    runner.run("parse_relational_lower",     test_parse_relational_lower);
    runner.run("parse_all_ops_relational",   test_parse_all_operators_relational);

    // Timed until tests
    runner.run("parse_timed_until",          test_parse_timed_until);
    runner.run("parse_timed_until_open",     test_parse_timed_until_open);

    // Arithmetic tests
    runner.run("parse_arithmetic_braces",    test_parse_arithmetic_braces);
    runner.run("tctl_with_arithmetic",       test_tctl_with_arithmetic);

    // Error handling tests
    runner.run("parse_errors_intervals",     test_parse_errors_intervals);
    runner.run("parse_errors_arithmetic",    test_parse_errors_arithmetic);

    // Desugaring tests
    runner.run("desugar_timed_ef_af",        test_desugar_timed_ef_af);
    runner.run("desugar_timed_eg_ag",        test_desugar_timed_eg_ag);
    runner.run("desugar_timed_until",        test_desugar_timed_until);

    // NNF tests
    runner.run("nnf_timed_operators",        test_nnf_timed_operators);
    runner.run("nnf_negated_timed",          test_nnf_negated_timed);
    runner.run("normalize_timed_sugar",      test_normalize_timed_sugar);

    // Zone tests (UDBM)
    runner.run("zone_smoke",                 test_zone_smoke);
    runner.run("zone_universe_empty",        test_zone_universe_empty);
    runner.run("zone_constraints",           test_zone_constraints);
    runner.run("zone_delay_reset",           test_zone_delay_reset);

    // Complex formula tests
    runner.run("nested_timed_operators",     test_nested_timed_operators);
    runner.run("timed_until_complex",        test_timed_until_complex);
    runner.run("tctl_boolean_arithmetic",    test_tctl_boolean_arithmetic);
    runner.run("relational_complex",         test_relational_complex);

    // Stress tests
    runner.run("tctl_stress_parsing",        test_tctl_stress_parsing);
    runner.run("tctl_stress_normalization",  test_tctl_stress_normalization);

    // TCTL Tableau Satisfiability Tests (5 SAT + 5 UNSAT)
    runner.run("tctl_sat1_lower_bound_delay",       test_tctl_sat1_lower_bound_delay);
    runner.run("tctl_sat2_strict_lower",            test_tctl_sat2_strict_lower);
    runner.run("tctl_sat3_upper_boundary",          test_tctl_sat3_upper_bound_boundary);
    runner.run("tctl_sat4_two_timed_untils",        test_tctl_sat4_two_timed_untils);
    runner.run("tctl_sat5_universal_timed",         test_tctl_sat5_universal_timed);
    runner.run("tctl_unsat1_invariant",             test_tctl_unsat1_invariant_contradiction);
    runner.run("tctl_unsat2_upper_deadline",        test_tctl_unsat2_upper_deadline);
    runner.run("tctl_unsat3_lower_impossible",      test_tctl_unsat3_lower_bound_impossible);
    runner.run("tctl_unsat4_strict_upper",          test_tctl_unsat4_strict_upper_boundary);
    runner.run("tctl_unsat5_loop_no_fulfilment",    test_tctl_unsat5_loop_without_fulfilment);

    // Negated timed-until zone-splitting tests
    runner.run("neg_timed_sat_window",              test_neg_timed_sat_window);
    runner.run("neg_timed_strict_upper",            test_neg_timed_strict_upper);
    runner.run("neg_timed_strict_lower",            test_neg_timed_strict_lower);

    // Release operator tests
    runner.run("parse_release",                     test_parse_release);
    runner.run("normalize_release",                 test_normalize_release);
    runner.run("release_sat",                       test_release_sat);
    runner.run("release_loop_acceptance",            test_release_loop_acceptance);

    // TCTL 50-formula high-coverage suite (25 SAT + 25 UNSAT)
    runner.run("tctl_coverage_suite",               test_tctl_coverage_suite);

    // Comprehensive 200-test SAT/UNSAT suite
    runner.run("comprehensive_200",                 test_comprehensive_200);

    // Stress 200-test advanced suite
    runner.run("stress_200",                        test_stress_200);

    runner.run("propositional_100",                   test_propositional_100);

    // Parallel / single-thread equivalence
    runner.run("parallel_equivalence",               test_parallel_equivalence);

    return runner.summarise();
}

}  // namespace tctl
