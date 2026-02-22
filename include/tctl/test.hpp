// ============================================================================
// tctl/test.hpp — Lightweight selftest framework
// ============================================================================
//
// Defines a minimal test harness: register test functions, run them,
// and report pass/fail counts.  No external dependencies.
//
// Usage:
//   void test_foo(TestContext& ctx) {
//       ctx.check(1 + 1 == 2, "basic math");
//   }
//   // in run_selftests():  ctx.run("foo", test_foo);
//
// ============================================================================

#ifndef CTL_TEST_HPP
#define CTL_TEST_HPP

#include <functional>
#include <string>
#include <vector>

namespace tctl {

// ── TestContext ──────────────────────────────────────────────────────────────

class TestContext {
public:
    /// Record a check.  If `condition` is false, logs a failure.
    void check(bool condition, const std::string& description);

    /// Record a string-equality check with nice diff output.
    void check_eq(const std::string& actual, const std::string& expected,
                  const std::string& description);

    /// Total checks so far.
    int total() const noexcept { return total_; }

    /// Failed checks so far.
    int failed() const noexcept { return failed_; }

private:
    int total_  = 0;
    int failed_ = 0;
    std::string current_test_;

    friend class TestRunner;
};

// ── TestRunner ──────────────────────────────────────────────────────────────

class TestRunner {
public:
    using TestFunc = std::function<void(TestContext&)>;

    /// Register and immediately run a named test.
    void run(const std::string& name, TestFunc func);

    /// Print summary and return exit code (0 = all pass, 1 = failures).
    int summarise() const;

private:
    int tests_run_    = 0;
    int tests_failed_ = 0;
    int checks_total_ = 0;
    int checks_failed_ = 0;
};

// ── TestCase — data-driven TCTL coverage test ───────────────────────────────

struct TestCase {
    std::string formula;
    bool expected_sat;
};

/// Generate 50 high-coverage TCTL test properties (25 SAT / 25 UNSAT).
std::vector<TestCase> generate_tctl_tests();

/// Generate 200 stress-test properties across 7 categories.
std::vector<TestCase> generate_stress_200();

/// Generate 100 propositional-heavy tests.
std::vector<TestCase> generate_propositional_100();

/// Entry point: run all built-in self-tests.
/// Returns 0 on success, 1 on failure.
int run_selftests();

}  // namespace tctl

#endif  // CTL_TEST_HPP
