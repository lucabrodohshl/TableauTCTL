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

std::optional<z3::expr> Z3Checker::to_z3_state_bool(FormulaId id) {
    const FormulaNode& n = factory_.node(id);

    switch (n.kind) {
        case NodeKind::True:
            return ctx_.bool_val(true);
        case NodeKind::False:
            return ctx_.bool_val(false);

        case NodeKind::Atom:
            return get_bool_var(n.atom_name);

        case NodeKind::Not: {
            auto child = to_z3_state_bool(n.children[0]);
            if (!child) return std::nullopt;
            return !(*child);
        }

        case NodeKind::And: {
            auto lhs = to_z3_state_bool(n.children[0]);
            auto rhs = to_z3_state_bool(n.children[1]);
            if (!lhs || !rhs) return std::nullopt;
            return (*lhs) && (*rhs);
        }

        case NodeKind::Or: {
            auto lhs = to_z3_state_bool(n.children[0]);
            auto rhs = to_z3_state_bool(n.children[1]);
            if (!lhs || !rhs) return std::nullopt;
            return (*lhs) || (*rhs);
        }

        case NodeKind::Implies: {
            auto lhs = to_z3_state_bool(n.children[0]);
            auto rhs = to_z3_state_bool(n.children[1]);
            if (!lhs || !rhs) return std::nullopt;
            return z3::implies(*lhs, *rhs);
        }

        case NodeKind::Iff: {
            auto lhs = to_z3_state_bool(n.children[0]);
            auto rhs = to_z3_state_bool(n.children[1]);
            if (!lhs || !rhs) return std::nullopt;
            return (*lhs) == (*rhs);
        }

        case NodeKind::IntLessEq:
        case NodeKind::IntLess:
        case NodeKind::IntGreaterEq:
        case NodeKind::IntGreater:
        case NodeKind::IntEqual:
            return to_z3_constraint(id);

        // Temporal operators are not state predicates.
        case NodeKind::EX:
        case NodeKind::AX:
        case NodeKind::EU:
        case NodeKind::AU:
        case NodeKind::ER:
        case NodeKind::AR:
        case NodeKind::EF:
        case NodeKind::AF:
        case NodeKind::EG:
        case NodeKind::AG:
        case NodeKind::TimedEU:
        case NodeKind::TimedAU:
        case NodeKind::TimedER:
        case NodeKind::TimedAR:
        case NodeKind::TimedEF:
        case NodeKind::TimedAF:
        case NodeKind::TimedEG:
        case NodeKind::TimedAG:
            return std::nullopt;

        // Integer expressions are not boolean formulas on their own.
        case NodeKind::IntVar:
        case NodeKind::IntConst:
        case NodeKind::IntPlus:
        case NodeKind::IntMinus:
        case NodeKind::IntTimes:
            return std::nullopt;
    }

    return std::nullopt;
}

bool Z3Checker::add_state_formula(FormulaId formula_id) {
    auto expr = to_z3_state_bool(formula_id);
    if (!expr) {
        return false;
    }
    solver_.add(*expr);
    return true;
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
