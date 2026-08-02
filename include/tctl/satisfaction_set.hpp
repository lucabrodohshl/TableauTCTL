// ============================================================================
// tctl/satisfaction_set.hpp — S_X(mu) satisfaction sets (§4.2, §5.1)
// ============================================================================
//
// The cover rule discharges a demanded timed modality mu against S_X(mu): the
// set of clock valuations at which mu holds under context X.  S_X(mu) is, in
// general, a finite union of ~=_M-zones (a Knaster–Tarski least fixpoint for
// until, greatest for release) and is represented as a ZoneSet.
//
// Clock model.  For a self-contained S_X computation we work in a fixed clock
// space whose dimension is 1 (reference clock) + one formula-clock per distinct
// modality subformula of the input.  `assign_clocks(mu, f)` builds that map; the
// public satisfaction_set() wrapper allocates it and the extrapolation bound M.
//
// Z3 decides the *propositional/arithmetic* consistency of leaves jointly; the
// clock constraints (windows x_mu ∈ I, guards) stay in the ZoneSet layer.
// ============================================================================

#ifndef TCTL_SATISFACTION_SET_HPP
#define TCTL_SATISFACTION_SET_HPP

#include "tctl/ast.hpp"
#include "tctl/zone.hpp"
#include "tctl/zoneset.hpp"

#include <cstdint>
#include <map>
#include <string>
#include <unordered_map>
#include <vector>

namespace tctl {

// A distinct clock index per *timed* modality subformula (clock 0 = reference).
// Untimed modalities (window [0,∞), no deadline) get no clock.
using ClockMap = std::map<FormulaId, ClockId>;

// Sentinel for "this modality has no formula-clock" (an untimed modality).
inline constexpr ClockId kNoClock = static_cast<ClockId>(-1);

/// mu's formula-clock, or kNoClock if it is untimed (no clock allocated).
inline ClockId clock_of(const ClockMap& cmap, FormulaId mu) {
    auto it = cmap.find(mu);
    return it == cmap.end() ? kNoClock : it->second;
}

// Persistent memo for S_X(mu, X): the fixpoint is otherwise recomputed at every
// cover node — and recursively for nested modalities — which blows up
// exponentially with nesting depth.  Keyed by (mu, X).
using SatCache = std::unordered_map<std::uint64_t, ZoneSet>;

// ── Leaf regions and node closure ───────────────────────────────────────────

/// Clock-valuation region where a *modality-free* state predicate psi holds
/// under the propositional part of context X.  Returns the full universe (over
/// num_clocks) when {X_prop ∧ psi} is Z3-consistent, else the empty set.
/// (The modality-aware generalisation is holds_region(), below.)
ZoneSet sat_leaf(FormulaId psi, const FormulaSet& X, FormulaFactory& f,
                 std::size_t num_clocks);

/// A node is (propositionally) closed when the conjunction of its state-predicate
/// leaves Gamma_prop is Z3-UNSAT.  Temporal formulas in gamma are ignored.
bool node_closed(const FormulaSet& gamma, FormulaFactory& f);

// ── Satisfaction sets S_X(mu) ───────────────────────────────────────────────

/// S_X(mu) over a fixed clock space (num_clocks dims, extrapolation vector max),
/// with `cmap` assigning a clock to mu and to every modality inside it.  Least
/// fixpoint for until, greatest for release; recursion on FL(phi,psi).
ZoneSet satisfaction_set(FormulaId mu, const FormulaSet& X, const ClockMap& cmap,
                         std::size_t num_clocks,
                         const std::vector<std::int32_t>& max, FormulaFactory& f);

/// Memoised S_X(mu): shares the fixpoint across cover nodes and nested recursion.
ZoneSet satisfaction_set(FormulaId mu, const FormulaSet& X, const ClockMap& cmap,
                         std::size_t num_clocks,
                         const std::vector<std::int32_t>& max, FormulaFactory& f,
                         SatCache& cache);

/// Region (over num_clocks) at which state formula psi holds under X, evaluating
/// each top-level sub-modality via its S_X at "demanded now" (its clock = 0).
ZoneSet holds_region(FormulaId psi, const FormulaSet& X, const ClockMap& cmap,
                     std::size_t num_clocks,
                     const std::vector<std::int32_t>& max, FormulaFactory& f);

/// Convenience wrapper: assign clocks over mu's subtree, pick M = largest
/// constant, and return S_X(mu) over the resulting space.  `out_x_mu` (if not
/// null) receives mu's own formula-clock index; `out_num_clocks` the dimension.
ZoneSet satisfaction_set(FormulaId mu, const FormulaSet& X, FormulaFactory& f,
                         ClockId* out_x_mu = nullptr,
                         std::size_t* out_num_clocks = nullptr);

// ── Small helpers exposed for testing / reuse ───────────────────────────────

/// True for the temporal modalities of the fragment of §3 (EU/AU/ER/AR and
/// their timed forms).  After normalisation no sugar / object next remains.
bool is_modality(NodeKind k) noexcept;

/// Assign a distinct clock index (starting at 1) to every modality subformula
/// of `root`; returns the map.  Clock 0 stays the reference clock.
ClockMap assign_clocks(FormulaId root, FormulaFactory& f);

/// @brief Assign the *onset* clock @f$y_\mu@f$ of every modality that can become
/// persistent, numbering from `first`.
///
/// A pursuit reads two quantities.  @f$x_\mu@f$, from assign_clocks(), measures
/// the time since it last answered a demand and bounds the next witness.
/// @f$y_\mu@f$ measures the time since the demand was last *raised*, and is what
/// tells a persistent pursuit when it may stop: a witness answers every onset at
/// or before @f$w - \inf I@f$, so the pursuit may end at a witness exactly when
/// no onset has been raised since @f$\inf I@f$ before it.
///
/// Only a *universal* modality is ever absorbed into a persistent pursuit --
/// distinct onsets of an existential one may be served by distinct runs -- so
/// only a timed universal modality needs a @f$y_\mu@f$.  Allocating one for
/// every modality would double the DBM dimension for nothing.
ClockMap assign_onset_clocks(FormulaId root, FormulaFactory& f, ClockId first);

/// The largest integer constant M appearing in any time interval of `root`.
std::int32_t max_constant(FormulaId root, FormulaFactory& f);

}  // namespace tctl

#endif  // TCTL_SATISFACTION_SET_HPP
