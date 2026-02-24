// ============================================================================
// tctl/z3_solver.hpp — Z3 wrapper for arithmetic constraint checking
// ============================================================================
//
// This module provides a wrapper around Z3 for checking satisfiability
// of arithmetic constraints (integer arithmetic only).
//
// Usage:
//   Z3Checker checker(factory);
//   checker.add_constraint(constraint_id);
//   if (checker.check() == Z3Result::SAT) {
//       // constraints are satisfiable
//   }
//
// IMPORTANT: Z3 is ONLY used to check consistency of arithmetic constraints
// within a single tableau node. It does NOT encode tctl semantics, temporal
// operators, or fixpoints.
//
// ============================================================================

#ifndef CTL_Z3_SOLVER_HPP
#define CTL_Z3_SOLVER_HPP

#include "tctl/ast.hpp"

#include <z3++.h>

#include <memory>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

namespace tctl {

// ── Z3Result ────────────────────────────────────────────────────────────────

enum class Z3Result {
    SAT,
    UNSAT,
    UNKNOWN
};

// ── Z3Checker ───────────────────────────────────────────────────────────────
// Maintains a Z3 context and solver for checking arithmetic constraints.
// Constraints are added incrementally, and check() determines satisfiability.

class Z3Checker {
public:
    explicit Z3Checker(const FormulaFactory& factory);

    /// Add an arithmetic constraint to the solver.
    /// The constraint must be a formula of type IntLessEq, IntLess,
    /// IntGreaterEq, IntGreater, or IntEqual.
    void add_constraint(FormulaId constraint_id);

    /// Add a boolean literal to the solver.
    /// If positive is true, asserts the atom is true; otherwise false.
    void add_boolean_literal(const std::string& atom_name, bool positive);

    /// Add a state predicate formula (propositional + arithmetic) to the solver.
    /// Returns true if the formula was supported and added, false if ignored.
    ///
    /// Supported state formulas are built from:
    ///   True/False, Atom, Not, And, Or, Implies, Iff,
    ///   and arithmetic constraints (IntLessEq, IntLess, IntGreaterEq,
    ///   IntGreater, IntEqual).
    ///
    /// Temporal operators are ignored (return false).
    bool add_state_formula(FormulaId formula_id);

    /// Check satisfiability of all added constraints.
    Z3Result check();

    /// Reset the solver to empty state.
    void reset();

    /// Get a model (if check() returned SAT).
    /// Returns a string representation of integer variable valuations.
    std::string get_model();

private:
    // Convert a FormulaId representing an arithmetic expression to Z3 expr.
    z3::expr to_z3_expr(FormulaId id);

    // Convert a FormulaId representing a constraint to Z3 expr (boolean).
    z3::expr to_z3_constraint(FormulaId id);

    // Convert a FormulaId representing a supported state predicate to Z3 expr.
    // Returns nullopt if the formula contains temporal operators or unsupported kinds.
    std::optional<z3::expr> to_z3_state_bool(FormulaId id);

    // Get or create a Z3 integer variable for the given name.
    z3::expr get_int_var(const std::string& name);

    // Get or create a Z3 boolean variable for the given atom name.
    z3::expr get_bool_var(const std::string& name);

    const FormulaFactory& factory_;
    z3::context          ctx_;
    z3::solver           solver_;

    // Map from variable names to Z3 integer constants (using optional to avoid default construction).
    std::unordered_map<std::string, std::unique_ptr<z3::expr>> int_vars_;
    
    // Map from atom names to Z3 boolean constants.
    std::unordered_map<std::string, std::unique_ptr<z3::expr>> bool_vars_;
};

}  // namespace tctl

#endif  // CTL_Z3_SOLVER_HPP
