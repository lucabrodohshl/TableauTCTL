// ============================================================================
// tctl/normalization.hpp — Desugaring, implication elimination, and NNF
// ============================================================================
//
// The normalization pipeline transforms an arbitrary parsed tctl formula
// into a canonical normal form suitable for the tableau engine.
//
// The pipeline has three phases, each documented below:
//
//   1. Desugar        — replace EF, AF, EG, AG with primitive operators.
//   2. Eliminate →/↔  — rewrite implications to disjunctions.
//   3. NNF            — push negation inward until it rests only on atoms
//                       or constants.
//
// All three phases are pure functions: they take a FormulaId and a
// FormulaFactory and return a new (interned) FormulaId.
//
// The `normalize()` function chains all three in order.
//
// ============================================================================

#ifndef CTL_NORMALIZATION_HPP
#define CTL_NORMALIZATION_HPP

#include "tctl/ast.hpp"

namespace tctl {

// ── Phase 1: Desugaring ─────────────────────────────────────────────────────
//
// Rewrite rules (applied recursively, bottom-up):
//
//   EF φ   ≡   E(true U φ)
//   AF φ   ≡   A(true U φ)
//   EG φ   ≡   ¬AF ¬φ   =   ¬A(true U ¬φ)
//   AG φ   ≡   ¬EF ¬φ   =   ¬E(true U ¬φ)
//
// After this phase the formula contains no EF/AF/EG/AG nodes.

FormulaId desugar(FormulaId id, FormulaFactory& f);

// ── Phase 2: Implication elimination ────────────────────────────────────────
//
// Rewrite rules (applied recursively, bottom-up):
//
//   φ → ψ     ≡   ¬φ ∨ ψ
//   φ ↔ ψ     ≡   (¬φ ∨ ψ) ∧ (¬ψ ∨ φ)
//                 equivalently  (φ → ψ) ∧ (ψ → φ)
//
// After this phase the formula contains no Implies or Iff nodes.

FormulaId eliminate_implications(FormulaId id, FormulaFactory& f);

// ── Phase 3: Negation Normal Form (NNF) ─────────────────────────────────────
//
// Push negations inward using De Morgan's laws and duality of temporal
// operators until negation appears only directly above atoms or constants.
//
// Rewrite rules for ¬ (the recursive argument is already in NNF):
//
//   ¬¬φ         ≡   φ
//   ¬(φ ∧ ψ)   ≡   ¬φ ∨ ¬ψ            (De Morgan)
//   ¬(φ ∨ ψ)   ≡   ¬φ ∧ ¬ψ            (De Morgan)
//   ¬true       ≡   false
//   ¬false      ≡   true
//   ¬EX φ       ≡   AX ¬φ              (duality)
//   ¬AX φ       ≡   EX ¬φ              (duality)
//   ¬E(φ U ψ)  ≡   A(¬ψ U (¬φ ∧ ¬ψ)) ∨ AG ¬ψ
//                 — but since AG has been desugared, we use the primitive
//                   expansion instead.  Actually, for a clean NNF that
//                   preserves the primitive EU/AU, we leave ¬EU/¬AU
//                   alone because the tableau handles them directly.
//                   So negation on EU/AU is kept as ¬E(…U…) / ¬A(…U…)
//                   ONLY when children are already in NNF.
//
// In our design negation of EU and AU is NOT expanded further because:
//   - The classical tctl tableau already provides rules for ¬E(φ U ψ) and
//     ¬A(φ U ψ) directly.
//   - Expanding would reintroduce AG/EG which we just desugared.
//
// After NNF, negation appears only on:  Atom, True, False, EU, AU.

FormulaId to_nnf(FormulaId id, FormulaFactory& f);

// ── Full pipeline ───────────────────────────────────────────────────────────
// Chains: desugar → eliminate_implications → to_nnf.

FormulaId normalize(FormulaId id, FormulaFactory& f);

}  // namespace tctl

#endif  // CTL_NORMALIZATION_HPP
