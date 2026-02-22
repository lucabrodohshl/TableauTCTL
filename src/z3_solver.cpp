// ============================================================================
// z3_solver.cpp — Implementation of Z3 arithmetic constraint checker
// ============================================================================

#include "tctl/z3_solver.hpp"

#include <stdexcept>

namespace tctl {

// ── Z3Checker ───────────────────────────────────────────────────────────────

Z3Checker::Z3Checker(const FormulaFactory& factory)
    : factory_(factory), ctx_(), solver_(ctx_) {
    // Z3 solver initialized with default configuration for integer arithmetic
}

void Z3Checker::reset() {
    solver_.reset();
    int_vars_.clear();
    bool_vars_.clear();
}

z3::expr Z3Checker::get_int_var(const std::string& name) {
    auto it = int_vars_.find(name);
    if (it != int_vars_.end()) {
        return *it->second;
    }
    // Create new integer variable
    auto var = std::make_unique<z3::expr>(ctx_.int_const(name.c_str()));
    z3::expr result = *var;
    int_vars_[name] = std::move(var);
    return result;
}

z3::expr Z3Checker::get_bool_var(const std::string& name) {
    auto it = bool_vars_.find(name);
    if (it != bool_vars_.end()) {
        return *it->second;
    }
    // Create new boolean variable
    auto var = std::make_unique<z3::expr>(ctx_.bool_const(name.c_str()));
    z3::expr result = *var;
    bool_vars_[name] = std::move(var);
    return result;
}

void Z3Checker::add_boolean_literal(const std::string& atom_name, bool positive) {
    z3::expr atom = get_bool_var(atom_name);
    if (positive) {
        solver_.add(atom);
    } else {
        solver_.add(!atom);
    }
}

z3::expr Z3Checker::to_z3_expr(FormulaId id) {
    const FormulaNode& n = factory_.node(id);

    switch (n.kind) {
        case NodeKind::IntVar:
            return get_int_var(n.atom_name);

        case NodeKind::IntConst:
            return ctx_.int_val(n.int_value);

        case NodeKind::IntPlus: {
            z3::expr lhs = to_z3_expr(n.children[0]);
            z3::expr rhs = to_z3_expr(n.children[1]);
            return lhs + rhs;
        }

        case NodeKind::IntMinus: {
            z3::expr lhs = to_z3_expr(n.children[0]);
            z3::expr rhs = to_z3_expr(n.children[1]);
            return lhs - rhs;
        }

        case NodeKind::IntTimes: {
            z3::expr lhs = to_z3_expr(n.children[0]);
            z3::expr rhs = to_z3_expr(n.children[1]);
            return lhs * rhs;
        }

        default:
            throw std::runtime_error("to_z3_expr: expected arithmetic expression, got " +
                                     std::string(node_kind_name(n.kind)));
    }
}

z3::expr Z3Checker::to_z3_constraint(FormulaId id) {
    const FormulaNode& n = factory_.node(id);

    switch (n.kind) {
        case NodeKind::IntLessEq: {
            z3::expr lhs = to_z3_expr(n.children[0]);
            z3::expr rhs = to_z3_expr(n.children[1]);
            return lhs <= rhs;
        }

        case NodeKind::IntLess: {
            z3::expr lhs = to_z3_expr(n.children[0]);
            z3::expr rhs = to_z3_expr(n.children[1]);
            return lhs < rhs;
        }

        case NodeKind::IntGreaterEq: {
            z3::expr lhs = to_z3_expr(n.children[0]);
            z3::expr rhs = to_z3_expr(n.children[1]);
            return lhs >= rhs;
        }

        case NodeKind::IntGreater: {
            z3::expr lhs = to_z3_expr(n.children[0]);
            z3::expr rhs = to_z3_expr(n.children[1]);
            return lhs > rhs;
        }

        case NodeKind::IntEqual: {
            z3::expr lhs = to_z3_expr(n.children[0]);
            z3::expr rhs = to_z3_expr(n.children[1]);
            return lhs == rhs;
        }

        default:
            throw std::runtime_error("to_z3_constraint: expected arithmetic constraint, got " +
                                     std::string(node_kind_name(n.kind)));
    }
}

void Z3Checker::add_constraint(FormulaId constraint_id) {
    z3::expr constraint = to_z3_constraint(constraint_id);
    solver_.add(constraint);
}

Z3Result Z3Checker::check() {
    z3::check_result result = solver_.check();

    switch (result) {
        case z3::sat:
            return Z3Result::SAT;
        case z3::unsat:
            return Z3Result::UNSAT;
        case z3::unknown:
            return Z3Result::UNKNOWN;
    }

    return Z3Result::UNKNOWN;
}

std::string Z3Checker::get_model() {
    if (solver_.check() != z3::sat) {
        return "(no model available)";
    }

    z3::model model = solver_.get_model();
    std::string result = "{";
    bool first = true;

    for (const auto& entry : int_vars_) {
        if (!first) {
            result += ", ";
        }
        first = false;

        z3::expr var = *entry.second;
        z3::expr value = model.eval(var, true);
        result += entry.first + " = " + value.to_string();
    }

    result += "}";
    return result;
}

}  // namespace tctl
