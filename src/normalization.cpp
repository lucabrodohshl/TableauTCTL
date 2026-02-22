// ============================================================================
// normalization.cpp — Desugaring, implication elimination, and NNF
// ============================================================================
//
// Each phase is a recursive, bottom-up transformation over the interned
// formula DAG.  Because FormulaFactory interns everything, repeated
// sub-formulas are normalised at most once.
//
// IMPORTANT: When recursively calling these functions, we must copy child IDs
// *before* the recursive call, because the call may grow the factory and
// invalidate any references to FormulaNode (e.g., `const FormulaNode& n`).
//
// ============================================================================

#include "tctl/normalization.hpp"

namespace tctl {

// ============================================================================
// Phase 1: Desugaring
// ============================================================================
//
// We recursively descend the formula tree.  Whenever we encounter a sugar
// node (EF, AF, EG, AG), we replace it with its definition in terms of the
// primitive temporal operators EU and AU (and negation).
//
//   EF φ   →   E(true U φ')            where φ' = desugar(φ)
//   AF φ   →   A(true U φ')
//   EG φ   →   ¬A(true U ¬φ')          i.e. ¬AF(¬φ)
//   AG φ   →   ¬E(true U ¬φ')          i.e. ¬EF(¬φ)
//
// All other nodes are rebuilt from their desugared children (which is a
// no-op when children are unchanged thanks to interning).

FormulaId desugar(FormulaId id, FormulaFactory& f) {
    // Copy node kind and children BEFORE any recursive calls.
    // Recursive calls may grow the factory, invalidating node references.
    NodeKind kind = f.node(id).kind;
    FormulaId child0 = f.node(id).children[0];
    FormulaId child1 = f.node(id).children[1];

    switch (kind) {
        // ── Leaves: nothing to desugar ──────────────────────────────────
        case NodeKind::True:
        case NodeKind::False:
        case NodeKind::Atom:
        case NodeKind::IntVar:
        case NodeKind::IntConst:
            return id;

        // ── Arithmetic expressions: recurse into children ───────────────
        case NodeKind::IntPlus: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_int_plus(c0, c1);
        }
        case NodeKind::IntMinus: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_int_minus(c0, c1);
        }
        case NodeKind::IntTimes: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_int_times(c0, c1);
        }

        // ── Arithmetic constraints: recurse into children ───────────────
        case NodeKind::IntLessEq: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_int_less_eq(c0, c1);
        }
        case NodeKind::IntLess: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_int_less(c0, c1);
        }
        case NodeKind::IntGreaterEq: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_int_greater_eq(c0, c1);
        }
        case NodeKind::IntGreater: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_int_greater(c0, c1);
        }
        case NodeKind::IntEqual: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_int_equal(c0, c1);
        }

        // ── Unary connectives: recurse into child ───────────────────────
        case NodeKind::Not:
            return f.make_not(desugar(child0, f));

        case NodeKind::EX:
            return f.make_ex(desugar(child0, f));

        case NodeKind::AX:
            return f.make_ax(desugar(child0, f));

        // ── Binary connectives: recurse into both children ──────────────
        case NodeKind::And: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_and(c0, c1);
        }

        case NodeKind::Or: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_or(c0, c1);
        }

        case NodeKind::Implies: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_implies(c0, c1);
        }

        case NodeKind::Iff: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_iff(c0, c1);
        }

        case NodeKind::EU: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_eu(c0, c1);
        }

        case NodeKind::AU: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_au(c0, c1);
        }

        case NodeKind::ER: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_er(c0, c1);
        }

        case NodeKind::AR: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_ar(c0, c1);
        }

        // ── TCTL canonical nodes: just recurse into children ────────────
        case NodeKind::TimedEU: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_timed_eu(c0, c1, 
                                   f.node(id).time_lower, 
                                   f.node(id).time_upper);
        }

        case NodeKind::TimedAU: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_timed_au(c0, c1,
                                   f.node(id).time_lower,
                                   f.node(id).time_upper);
        }

        // TCTL timed release: keep as-is (lowered to ¬timed-until in NNF)
        case NodeKind::TimedER: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_timed_er(c0, c1,
                                   f.node(id).time_lower,
                                   f.node(id).time_upper);
        }

        case NodeKind::TimedAR: {
            auto c0 = desugar(child0, f);
            auto c1 = desugar(child1, f);
            return f.make_timed_ar(c0, c1,
                                   f.node(id).time_lower,
                                   f.node(id).time_upper);
        }

        // ── Sugar nodes: rewrite using definitions ──────────────────────

        // EF φ  ≡  E(true U φ)
        case NodeKind::EF: {
            FormulaId c = desugar(child0, f);
            return f.make_eu(f.make_true(), c);
        }

        // AF φ  ≡  A(true U φ)
        case NodeKind::AF: {
            FormulaId c = desugar(child0, f);
            return f.make_au(f.make_true(), c);
        }

        // EG φ  ≡  E(false R φ)  — greatest-fixpoint via Release
        case NodeKind::EG: {
            FormulaId c = desugar(child0, f);
            return f.make_er(f.make_false(), c);
        }

        // AG φ  ≡  A(false R φ)  — greatest-fixpoint via Release
        case NodeKind::AG: {
            FormulaId c = desugar(child0, f);
            return f.make_ar(f.make_false(), c);
        }

        // ── TCTL sugar nodes: rewrite using timed-until definitions ─────

        // TimedEF[a,b] φ  ≡  E(true U[a,b] φ)
        case NodeKind::TimedEF: {
            FormulaId c = desugar(child0, f);
            auto lower = f.node(id).time_lower;
            auto upper = f.node(id).time_upper;
            return f.make_timed_eu(f.make_true(), c, lower, upper);
        }

        // TimedAF[a,b] φ  ≡  A(true U[a,b] φ)
        case NodeKind::TimedAF: {
            FormulaId c = desugar(child0, f);
            auto lower = f.node(id).time_lower;
            auto upper = f.node(id).time_upper;
            return f.make_timed_au(f.make_true(), c, lower, upper);
        }

        // TimedEG[a,b] φ  ≡  ¬AF[a,b](¬φ)  =  ¬A(true U[a,b] ¬φ)
        case NodeKind::TimedEG: {
            FormulaId c = desugar(child0, f);
            FormulaId neg_c = f.make_not(c);
            auto lower = f.node(id).time_lower;
            auto upper = f.node(id).time_upper;
            FormulaId au = f.make_timed_au(f.make_true(), neg_c, lower, upper);
            return f.make_not(au);
        }

        // TimedAG[a,b] φ  ≡  ¬EF[a,b](¬φ)  =  ¬E(true U[a,b] ¬φ)
        case NodeKind::TimedAG: {
            FormulaId c = desugar(child0, f);
            FormulaId neg_c = f.make_not(c);
            auto lower = f.node(id).time_lower;
            auto upper = f.node(id).time_upper;
            FormulaId eu = f.make_timed_eu(f.make_true(), neg_c, lower, upper);
            return f.make_not(eu);
        }
    }

    return id;  // unreachable, but silences warnings
}

// ============================================================================
// Phase 2: Implication Elimination
// ============================================================================
//
// Rewrite rules:
//   φ → ψ    becomes   ¬φ ∨ ψ
//   φ ↔ ψ    becomes   (¬φ ∨ ψ) ∧ (¬ψ ∨ φ)
//
// All other nodes are rebuilt from recursively transformed children.

FormulaId eliminate_implications(FormulaId id, FormulaFactory& f) {
    // Copy node kind and children BEFORE any recursive calls.
    NodeKind kind = f.node(id).kind;
    FormulaId child0 = f.node(id).children[0];
    FormulaId child1 = f.node(id).children[1];

    switch (kind) {
        // ── Leaves ──────────────────────────────────────────────────────
        case NodeKind::True:
        case NodeKind::False:
        case NodeKind::Atom:
        case NodeKind::IntVar:
        case NodeKind::IntConst:
            return id;

        // ── Arithmetic expressions: recurse into children ───────────────
        case NodeKind::IntPlus: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_int_plus(c0, c1);
        }
        case NodeKind::IntMinus: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_int_minus(c0, c1);
        }
        case NodeKind::IntTimes: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_int_times(c0, c1);
        }

        // ── Arithmetic constraints: recurse into children ───────────────
        case NodeKind::IntLessEq: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_int_less_eq(c0, c1);
        }
        case NodeKind::IntLess: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_int_less(c0, c1);
        }
        case NodeKind::IntGreaterEq: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_int_greater_eq(c0, c1);
        }
        case NodeKind::IntGreater: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_int_greater(c0, c1);
        }
        case NodeKind::IntEqual: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_int_equal(c0, c1);
        }

        // ── Unary ───────────────────────────────────────────────────────
        case NodeKind::Not:
            return f.make_not(eliminate_implications(child0, f));
        case NodeKind::EX:
            return f.make_ex(eliminate_implications(child0, f));
        case NodeKind::AX:
            return f.make_ax(eliminate_implications(child0, f));

        // ── Binary (non-implication) ────────────────────────────────────
        case NodeKind::And: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_and(c0, c1);
        }
        case NodeKind::Or: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_or(c0, c1);
        }
        case NodeKind::EU: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_eu(c0, c1);
        }
        case NodeKind::AU: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_au(c0, c1);
        }
        case NodeKind::ER: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_er(c0, c1);
        }
        case NodeKind::AR: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_ar(c0, c1);
        }

        // ── TCTL canonical nodes: just recurse into children ────────────
        case NodeKind::TimedEU: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_timed_eu(c0, c1,
                                   f.node(id).time_lower,
                                   f.node(id).time_upper);
        }
        case NodeKind::TimedAU: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_timed_au(c0, c1,
                                   f.node(id).time_lower,
                                   f.node(id).time_upper);
        }
        case NodeKind::TimedER: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_timed_er(c0, c1,
                                   f.node(id).time_lower,
                                   f.node(id).time_upper);
        }
        case NodeKind::TimedAR: {
            auto c0 = eliminate_implications(child0, f);
            auto c1 = eliminate_implications(child1, f);
            return f.make_timed_ar(c0, c1,
                                   f.node(id).time_lower,
                                   f.node(id).time_upper);
        }

        // ── Implication: φ → ψ  ≡  ¬φ ∨ ψ ─────────────────────────────
        case NodeKind::Implies: {
            FormulaId lhs = eliminate_implications(child0, f);
            FormulaId rhs = eliminate_implications(child1, f);
            return f.make_or(f.make_not(lhs), rhs);
        }

        // ── Biconditional: φ ↔ ψ  ≡  (¬φ ∨ ψ) ∧ (¬ψ ∨ φ) ────────────
        case NodeKind::Iff: {
            FormulaId lhs = eliminate_implications(child0, f);
            FormulaId rhs = eliminate_implications(child1, f);
            // forward direction: ¬lhs ∨ rhs
            FormulaId fwd = f.make_or(f.make_not(lhs), rhs);
            // backward direction: ¬rhs ∨ lhs
            FormulaId bwd = f.make_or(f.make_not(rhs), lhs);
            return f.make_and(fwd, bwd);
        }

        // ── Sugar nodes should be gone by now, but handle gracefully ────
        case NodeKind::EF:
        case NodeKind::AF:
        case NodeKind::EG:
        case NodeKind::AG:
        case NodeKind::TimedEF:
        case NodeKind::TimedAF:
        case NodeKind::TimedEG:
        case NodeKind::TimedAG:
            // These should have been desugared already.  If not, just
            // return id for robustness.
            return id;
    }

    return id;
}

// ============================================================================
// Phase 3: Negation Normal Form (NNF)
// ============================================================================
//
// Strategy: process the tree bottom-up.  For non-negated nodes, just
// recurse.  For negated nodes, apply the appropriate push-in rule.
//
// We implement a helper `negate_nnf` that takes a formula already in NNF
// (no implications, no sugar) and returns its negation in NNF.
//
// The main `to_nnf` function:
//   - For ¬φ:  compute to_nnf(φ), then negate_nnf the result.
//   - For non-¬: recurse into children, build the same node kind.

// Forward declaration of the negation-pusher.
static FormulaId negate_nnf(FormulaId id, FormulaFactory& f);

FormulaId to_nnf(FormulaId id, FormulaFactory& f) {
    // Copy node kind and children BEFORE any recursive calls.
    NodeKind kind = f.node(id).kind;
    FormulaId child0 = f.node(id).children[0];
    FormulaId child1 = f.node(id).children[1];

    switch (kind) {
        // ── Leaves: already in NNF ──────────────────────────────────────
        case NodeKind::True:
        case NodeKind::False:
        case NodeKind::Atom:
        case NodeKind::IntVar:
        case NodeKind::IntConst:
            return id;

        // ── Arithmetic expressions: recurse into children ───────────────
        case NodeKind::IntPlus: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_int_plus(c0, c1);
        }
        case NodeKind::IntMinus: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_int_minus(c0, c1);
        }
        case NodeKind::IntTimes: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_int_times(c0, c1);
        }

        // ── Arithmetic constraints: recurse into children ───────────────
        case NodeKind::IntLessEq: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_int_less_eq(c0, c1);
        }
        case NodeKind::IntLess: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_int_less(c0, c1);
        }
        case NodeKind::IntGreaterEq: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_int_greater_eq(c0, c1);
        }
        case NodeKind::IntGreater: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_int_greater(c0, c1);
        }
        case NodeKind::IntEqual: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_int_equal(c0, c1);
        }

        // ── Negation: compute NNF of child, then negate ─────────────────
        case NodeKind::Not: {
            FormulaId child_nnf = to_nnf(child0, f);
            return negate_nnf(child_nnf, f);
        }

        // ── Binary boolean ──────────────────────────────────────────────
        case NodeKind::And: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_and(c0, c1);
        }
        case NodeKind::Or: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_or(c0, c1);
        }

        // ── Temporal ────────────────────────────────────────────────────
        case NodeKind::EX:
            return f.make_ex(to_nnf(child0, f));
        case NodeKind::AX:
            return f.make_ax(to_nnf(child0, f));
        case NodeKind::EU: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_eu(c0, c1);
        }
        case NodeKind::AU: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_au(c0, c1);
        }
        case NodeKind::ER: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_er(c0, c1);
        }
        case NodeKind::AR: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_ar(c0, c1);
        }

        // ── TCTL temporal ───────────────────────────────────────────────
        case NodeKind::TimedEU: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_timed_eu(c0, c1,
                                   f.node(id).time_lower,
                                   f.node(id).time_upper);
        }
        case NodeKind::TimedAU: {
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_timed_au(c0, c1,
                                   f.node(id).time_lower,
                                   f.node(id).time_upper);
        }

        // ── Timed Release: keep first-class, just NNF-convert children ─────
        // E(φ R_I ψ) and A(φ R_I ψ) are handled directly by the tableau engine.
        // Their negations ¬E(φ R_I ψ) = A(¬φ U_I ¬ψ) and ¬A(φ R_I ψ) = E(¬φ U_I ¬ψ)
        // are pushed in by negate_nnf using R/U duality, producing plain TimedAU/TimedEU.
        case NodeKind::TimedER: {
            auto lower = f.node(id).time_lower;  // copy bounds before recursive calls
            auto upper = f.node(id).time_upper;
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_timed_er(c0, c1, lower, upper);
        }
        case NodeKind::TimedAR: {
            auto lower = f.node(id).time_lower;  // copy bounds before recursive calls
            auto upper = f.node(id).time_upper;
            auto c0 = to_nnf(child0, f);
            auto c1 = to_nnf(child1, f);
            return f.make_timed_ar(c0, c1, lower, upper);
        }

        // ── These should not appear after earlier phases ─────────────────
        case NodeKind::Implies:
        case NodeKind::Iff:
        case NodeKind::EF:
        case NodeKind::AF:
        case NodeKind::EG:
        case NodeKind::AG:
        case NodeKind::TimedEF:
        case NodeKind::TimedAF:
        case NodeKind::TimedEG:
        case NodeKind::TimedAG:
            return id;  // defensive fallthrough
    }

    return id;
}

// ── negate_nnf ──────────────────────────────────────────────────────────────
// Given a formula `id` that is already in NNF, return ¬id in NNF.
//
// Push-in rules:
//   ¬true         →  false
//   ¬false        →  true
//   ¬(atom)       →  ¬atom    (negation stays on atoms)
//   ¬¬φ           →  φ        (double negation elimination)
//   ¬(φ ∧ ψ)     →  ¬φ ∨ ¬ψ  (De Morgan)
//   ¬(φ ∨ ψ)     →  ¬φ ∧ ¬ψ  (De Morgan)
//   ¬EX φ         →  AX ¬φ    (temporal duality)
//   ¬AX φ         →  EX ¬φ    (temporal duality)
//   ¬E(φ U ψ)    →  kept as ¬E(φ U ψ) — the tableau handles this directly
//   ¬A(φ U ψ)    →  kept as ¬A(φ U ψ) — the tableau handles this directly

static FormulaId negate_nnf(FormulaId id, FormulaFactory& f) {
    // Copy node kind and children BEFORE any recursive calls.
    NodeKind kind = f.node(id).kind;
    FormulaId child0 = f.node(id).children[0];
    FormulaId child1 = f.node(id).children[1];

    switch (kind) {
        // ¬true → false
        case NodeKind::True:
            return f.make_false();

        // ¬false → true
        case NodeKind::False:
            return f.make_true();

        // ¬atom → ¬atom (literal)
        case NodeKind::Atom:
            return f.make_not(id);

        // ¬¬φ → φ  (the child of this Not is already in NNF)
        case NodeKind::Not:
            return child0;

        // ¬(φ ∧ ψ) → (¬φ ∨ ¬ψ)
        case NodeKind::And: {
            auto c0 = negate_nnf(child0, f);
            auto c1 = negate_nnf(child1, f);
            return f.make_or(c0, c1);
        }

        // ¬(φ ∨ ψ) → (¬φ ∧ ¬ψ)
        case NodeKind::Or: {
            auto c0 = negate_nnf(child0, f);
            auto c1 = negate_nnf(child1, f);
            return f.make_and(c0, c1);
        }

        // ¬EX φ → AX ¬φ
        case NodeKind::EX:
            return f.make_ax(negate_nnf(child0, f));

        // ¬AX φ → EX ¬φ
        case NodeKind::AX:
            return f.make_ex(negate_nnf(child0, f));

        // ¬E(φ U ψ) — leave as ¬E(φ U ψ) for the tableau engine.
        // The children are already in NNF, so we just wrap in Not.
        case NodeKind::EU:
            return f.make_not(id);

        // ¬A(φ U ψ) — leave as ¬A(φ U ψ) for the tableau engine.
        case NodeKind::AU:
            return f.make_not(id);

        // ¬E(φ R ψ) = A(¬φ U ¬ψ)  — Release/Until duality
        case NodeKind::ER: {
            auto c0 = negate_nnf(child0, f);  // ¬φ
            auto c1 = negate_nnf(child1, f);  // ¬ψ
            return f.make_au(c0, c1);
        }

        // ¬A(φ R ψ) = E(¬φ U ¬ψ)  — Release/Until duality
        case NodeKind::AR: {
            auto c0 = negate_nnf(child0, f);  // ¬φ
            auto c1 = negate_nnf(child1, f);  // ¬ψ
            return f.make_eu(c0, c1);
        }

        // ¬E(φ U_I ψ) = A(¬φ R_I ¬ψ) — Release / Until duality (timed)
        // Result is a plain TimedAR with NNF-negated children; no Not() wrapper needed.
        case NodeKind::TimedEU: {
            auto lower = f.node(id).time_lower;  // copy before recursive calls
            auto upper = f.node(id).time_upper;
            auto neg_c0 = negate_nnf(child0, f);
            auto neg_c1 = negate_nnf(child1, f);
            return f.make_timed_ar(neg_c0, neg_c1, lower, upper);
        }

        // ¬A(φ U_I ψ) = E(¬φ R_I ¬ψ) — Release / Until duality (timed)
        case NodeKind::TimedAU: {
            auto lower = f.node(id).time_lower;  // copy before recursive calls
            auto upper = f.node(id).time_upper;
            auto neg_c0 = negate_nnf(child0, f);
            auto neg_c1 = negate_nnf(child1, f);
            return f.make_timed_er(neg_c0, neg_c1, lower, upper);
        }

        // ── Arithmetic constraints: flip comparison operators ───────────
        
        // ¬(a <= b) → a > b
        case NodeKind::IntLessEq:
            return f.make_int_greater(child0, child1);

        // ¬(a < b) → a >= b
        case NodeKind::IntLess:
            return f.make_int_greater_eq(child0, child1);

        // ¬(a >= b) → a < b
        case NodeKind::IntGreaterEq:
            return f.make_int_less(child0, child1);

        // ¬(a > b) → a <= b
        case NodeKind::IntGreater:
            return f.make_int_less_eq(child0, child1);

        // ¬(a = b) → (a < b) | (a > b)
        case NodeKind::IntEqual: {
            FormulaId less = f.make_int_less(child0, child1);
            FormulaId greater = f.make_int_greater(child0, child1);
            return f.make_or(less, greater);
        }

        // ── Arithmetic expressions should not be directly negated ───────
        case NodeKind::IntVar:
        case NodeKind::IntConst:
        case NodeKind::IntPlus:
        case NodeKind::IntMinus:
        case NodeKind::IntTimes:
            // These should not appear as top-level formulas to negate
            // (only constraints can be formulas). If we hit this, just
            // return ¬id for robustness.
            return f.make_not(id);

        // These should not appear in input to this function.
        case NodeKind::Implies:
        case NodeKind::Iff:
        case NodeKind::EF:
        case NodeKind::AF:
        case NodeKind::EG:
        case NodeKind::AG:
        case NodeKind::TimedEF:
        case NodeKind::TimedAF:
        case NodeKind::TimedEG:
        case NodeKind::TimedAG:
            return f.make_not(id);

        // ¬E(φ R_I ψ) = A(¬φ U_I ¬ψ) — Release / Until duality (timed)
        case NodeKind::TimedER: {
            auto lower = f.node(id).time_lower;  // copy before recursive calls
            auto upper = f.node(id).time_upper;
            auto neg_c0 = negate_nnf(child0, f);
            auto neg_c1 = negate_nnf(child1, f);
            return f.make_timed_au(neg_c0, neg_c1, lower, upper);
        }

        // ¬A(φ R_I ψ) = E(¬φ U_I ¬ψ) — Release / Until duality (timed)
        case NodeKind::TimedAR: {
            auto lower = f.node(id).time_lower;  // copy before recursive calls
            auto upper = f.node(id).time_upper;
            auto neg_c0 = negate_nnf(child0, f);
            auto neg_c1 = negate_nnf(child1, f);
            return f.make_timed_eu(neg_c0, neg_c1, lower, upper);
        }
    }

    return f.make_not(id);
}

// ============================================================================
// Full Normalization Pipeline
// ============================================================================
// Chains: desugar → eliminate_implications → to_nnf.
//
// The order matters:
//   (1) Desugaring removes EF/AF/EG/AG, which introduce negations.
//   (2) Implication elimination removes →/↔, producing only ∧/∨/¬.
//   (3) NNF pushes all remaining negations to literals.

FormulaId normalize(FormulaId id, FormulaFactory& f) {
    FormulaId step1 = desugar(id, f);
    FormulaId step2 = eliminate_implications(step1, f);
    FormulaId step3 = to_nnf(step2, f);
    return step3;
}

}  // namespace tctl
