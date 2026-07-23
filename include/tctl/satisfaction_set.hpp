// ============================================================================
// tctl/satisfaction_set.hpp — S_X(mu) satisfaction sets (ETAPS2026 §4.2, §5.1)
// ============================================================================
//
// The cover rule discharges a demanded timed modality mu against S_X(mu): the
// set of clock valuations at which mu holds under context X.  S_X(mu) is, in
// general, a finite union of ~=_M-zones (a Knaster–Tarski least fixpoint for
// until, greatest for release) and is represented as a ZoneSet.
//
// Content is added task-by-task:
//   Task 1 — sat_leaf (leaf/boolean regions via Z3) + node_closed.
//   Task 2 — satisfaction_set(mu, ...) fixpoint (until/release).
// ============================================================================

#ifndef TCTL_SATISFACTION_SET_HPP
#define TCTL_SATISFACTION_SET_HPP

#include "tctl/ast.hpp"

namespace tctl {
// Declarations land in Task 1.
}  // namespace tctl

#endif  // TCTL_SATISFACTION_SET_HPP
