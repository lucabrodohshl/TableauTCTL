# ETAPS2026 TCTL Tableau (verdict-first) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the old Wolper-style engine with a faithful implementation of the paper's cover-rule / launch-pursuit tableau that decides TCTL satisfiability (SAT/UNSAT), reusing the existing lexer/parser/AST/normalization/ZoneSet/Z3/UDBM infrastructure.

**Architecture:** A pure `S_X(μ)` satisfaction-set fixpoint over `ZoneSet` (`satisfaction_set.*`) feeds a cover rule inside an on-the-fly AND–OR graph (`paper_tableau.*`); acceptance is a marking computed by node elimination. Z3 is the node closure oracle for arithmetic/propositional leaves; all clock reasoning stays in DBM/`ZoneSet`. Witness-TA extraction is deferred.

**Tech Stack:** C++20, CMake, UDBM (DBM/federation), Z3, existing `tctl::` libraries.

## Global Constraints

- Language/build: C++20, compiled with `-Werror` (warnings fail the build). Follow the existing `-DUDBM_DIR="$PWD/UDBM"` CMake recipe (`BUILD_MACOS.md`).
- Fragment implemented: paper §3 TCTL only — `⊤ ⊥ p ¬p ∧ ∨ E(φU_Iφ) E(φR_Iφ) A(φU_Iφ) A(φR_Iφ)` in NNF. **No object-level `EX`/`AX`** (parser already rejects them). Untimed `U`/`R` are `I=[0,∞)`. `EF/AF/EG/AG` desugar as today.
- Time bounds `I`: integer endpoints, `[a,b] (a,b] [a,b) (a,b)` with `a<b`, **plus punctual `[a,a]`** (accepted). Empty intervals stay rejected.
- Deadline rule (paper §4.2 p.6): `D_μ = {(x_μ, sup I)}` **iff** `μ` is a universal until; empty otherwise.
- Guarantees: sound + terminating for all TCTL; complete for non-punctual; punctual at timed-nesting depth > 1 prints a stderr completeness warning.
- Testing oracle: verdicts justified from TCTL semantics (witness TA or impossibility), **never** from the old engine. `S_X`/`sat_X` unit-tested against hand-computed `ZoneSet` values.
- Z3/zone separation: Z3 sees only frozen state predicates (props + int/real arithmetic); it never encodes temporal operators, clocks, or fixpoints.
- Reference: full construction in `docs/superpowers/specs/2026-07-23-tctl-paper-tableau-design.md`; paper at `../../../ETAPS2026.pdf` (§4 rules, §4.4 Fig. 1 worked examples, §4.3/§5.1 acceptance).

---

## Task 0: Scaffolding — new modules, delete old engine, verdict stub

**Files:**
- Create: `include/tctl/paper_tableau.hpp`, `src/paper_tableau.cpp`
- Create: `include/tctl/satisfaction_set.hpp`, `src/satisfaction_set.cpp`
- Create: `include/tctl/paper_oracle.hpp`, `src/paper_oracle.cpp`
- Modify: `CMakeLists.txt` (add new sources; remove `tableau.cpp`, `test.cpp`, `benchmark.cpp` targets; keep Z3/UDBM), `src/cli.cpp` (rewire to new engine + oracle), `src/main.cpp` (if it references removed symbols)
- Delete: `include/tctl/tableau.hpp`, `src/tableau.cpp`, `include/tctl/test.hpp`, `src/test.cpp`, `include/tctl/benchmark.hpp`, `src/benchmark.cpp`; drop `#include "tctl/benchmark.hpp"` from `cli.hpp` and the `benchmark`/`legacy` `Options` fields.

**Interfaces:**
- Produces:
  ```cpp
  namespace tctl {
  enum class Verdict { Satisfiable, Unsatisfiable, Timeout };
  const char* verdict_to_string(Verdict v) noexcept;

  class PaperTableau {                     // src/paper_tableau.cpp
  public:
      explicit PaperTableau(FormulaFactory& f);
      Verdict check(FormulaId normalized_formula);   // stub returns Unsatisfiable for now
      void set_timeout(std::chrono::seconds s);
      // stats accessors added in Task 6
  private:
      FormulaFactory& factory_;
  };

  int paper_oracle_run();                  // src/paper_oracle.cpp — returns count of failures
  }
  ```

- [ ] **Step 1: Write the failing test (oracle harness + one trivially-true case)**

In `src/paper_oracle.cpp`:
```cpp
#include "tctl/paper_oracle.hpp"
#include "tctl/paper_tableau.hpp"
#include "tctl/parser.hpp"
#include "tctl/normalization.hpp"
#include <cstdio>

namespace tctl {
namespace {
int check_case(const char* src, Verdict want) {
    FormulaFactory f;
    FormulaId phi = normalize(parse_formula(src, f), f);
    PaperTableau engine(f);
    Verdict got = engine.check(phi);
    bool ok = (got == want);
    std::printf("[%s] %-28s want=%s got=%s\n", ok ? "PASS" : "FAIL", src,
                verdict_to_string(want), verdict_to_string(got));
    return ok ? 0 : 1;
}
} // namespace
int paper_oracle_run() {
    int fails = 0;
    fails += check_case("p", Verdict::Satisfiable);   // an atom is trivially SAT
    return fails;
}
} // namespace tctl
```
(Confirm `parse_formula`'s real signature in `include/tctl/parser.hpp:109` and match it.)

- [ ] **Step 2: Build & run to verify it fails**

Run: `cmake -S . -B build-macos -DCMAKE_BUILD_TYPE=Debug -DUDBM_DIR="$PWD/UDBM" && cmake --build build-macos -j4 && ./build-macos/tctl_sat --selftest`
Expected: the `p` case prints `FAIL` (stub returns `Unsatisfiable`).

- [ ] **Step 3: Minimal `PaperTableau::check` — decide bare propositional leaves**

In `src/paper_tableau.cpp`, implement `check` for the trivial base case only: normalize, and if the formula is a single satisfiable state predicate (no modality), return `Satisfiable` via a one-node Z3 check; otherwise `Unsatisfiable` (temporary). Wire `verdict_to_string`.

- [ ] **Step 4: Build & run to verify the `p` case passes**

Run: `cmake --build build-macos -j4 && ./build-macos/tctl_sat --selftest`
Expected: `[PASS] p`.

- [ ] **Step 5: Commit**

```bash
git add -A -- include/tctl src/*.cpp CMakeLists.txt
git commit -m "feat(engine): scaffold paper tableau, delete old engine + untrusted tests"
```

---

## Task 1: Node, saturation, and `sat_X` for leaves/booleans

**Files:**
- Modify: `include/tctl/paper_tableau.hpp` (add `Deadline`, `Pursuit`, `Node`), `src/paper_tableau.cpp`
- Create: `include/tctl/satisfaction_set.hpp`, `src/satisfaction_set.cpp` (leaf region only, this task)
- Test: `src/paper_oracle.cpp`

**Interfaces:**
- Produces (`satisfaction_set.hpp`):
  ```cpp
  // Clock-valuation region where a state formula holds under context X.
  // Leaves (props + arithmetic) collapse to ⊤ (Z3-consistent) or ∅; boolean
  // combinations distribute; modalities are handled in Task 2 (throws/asserts here).
  ZoneSet sat_leaf(FormulaId psi, const FormulaSet& X_props,
                   FormulaFactory& f, std::size_t num_clocks);
  bool node_closed(const FormulaSet& gamma, FormulaFactory& f); // Z3-UNSAT of Γ_prop
  ```
- Produces (`paper_tableau.hpp`): `Node`, `Deadline`, `Pursuit` structs per spec §4; `saturate(Node&)` internal helper (∧ deterministic, ∨ produces OR-children, AX moves arg into `X`).

- [ ] **Step 1: Write failing unit tests for `sat_leaf` / `node_closed`**

Add to `paper_oracle.cpp` a `sat_unit()` section:
```cpp
// x<=2 ∧ x>=5 is inconsistent → node closed
{ FormulaFactory f; FormulaId c = parse_formula("(x<=2) & (x>=5)", f);
  FormulaSet g; g.insert(c); assert(node_closed(g, f)); }
// p alone → not closed; sat_leaf(p) == universe
{ FormulaFactory f; FormulaId p = f.make_atom("p");
  FormulaSet empty;
  assert(!sat_leaf(p, empty, f, 1).is_empty()); }
// p ∧ ¬p → closed
{ FormulaFactory f; FormulaId p=f.make_atom("p"); FormulaId np=f.make_not(p);
  FormulaSet g; g.insert(p); g.insert(np); assert(node_closed(g, f)); }
```

- [ ] **Step 2: Run to verify failure** — `... --selftest`; expect assertion/compile failure (symbols undefined).

- [ ] **Step 3: Implement `sat_leaf` + `node_closed`**

`node_closed`: build a `Z3Checker`, `add_state_formula` for each leaf in `gamma`, return `check()==UNSAT`. `sat_leaf`: recurse on `∧`/`∨` (intersect/unite `ZoneSet`s); for a leaf, return `ZoneSet::universe(num_clocks)` if `{X_props ∧ psi}` is Z3-SAT else `ZoneSet::empty(num_clocks)`; assert on modality (Task 2).

- [ ] **Step 4: Implement `saturate`** in `paper_tableau.cpp`: fixpoint applying `(∧)` (replace `φ∧ψ` by `φ,ψ`), `(AX)` (move `AXφ` arg into `X`); collect `(∨)` disjunctions as OR-branch points returned to the caller. No timed handling yet.

- [ ] **Step 5: Run tests, commit**

Run: `cmake --build build-macos -j4 && ./build-macos/tctl_sat --selftest`; expect the `sat_unit` assertions to pass.
```bash
git add -A -- include/tctl/satisfaction_set.hpp src/satisfaction_set.cpp include/tctl/paper_tableau.hpp src/paper_tableau.cpp src/paper_oracle.cpp
git commit -m "feat(engine): node model, saturation, Z3 leaf regions + closure"
```

---

## Task 2: `S_X(μ)` fixpoint — until (least) then release (greatest)

**Files:**
- Modify: `include/tctl/satisfaction_set.hpp`, `src/satisfaction_set.cpp`, `src/paper_oracle.cpp`

**Interfaces:**
- Produces:
  ```cpp
  // S_X(μ) as a ZoneSet over C ∪ {x_μ}. x_mu is the fresh formula-clock index.
  // max is the per-clock extrapolation vector (≅_M). Recurses on FL(φ) for
  // sub-modalities inside φ,ψ (each with its own fresh clock), memoized by (μ,X).
  ZoneSet satisfaction_set(FormulaId mu, const FormulaSet& X,
                           ClockId x_mu, std::size_t num_clocks,
                           const std::vector<std::int32_t>& max,
                           FormulaFactory& f);
  ```
- `sat_leaf` extended: a modality leaf `ν` returns `satisfaction_set(ν, …)` projected into the ambient clock space.

- [ ] **Step 1: Write failing `S_X` unit tests (hand-computed zones, paper Fig. 1)**

```cpp
// Until window [1,2] on clock x_mu, target q reachable, no forbidding context:
//   base zone = (x_mu ∈ [1,2]) since sat(q)=⊤. Least fixpoint back-delays to
//   x_mu ≤ 2 (down of x_mu∈[1,2]). So x_mu=0 ∈ S_X(E(⊤ U[1,2] q)).
{ FormulaFactory f; FormulaId q=f.make_atom("q");
  FormulaId mu=f.make_timed_eu(f.make_true(), q, TimeBound::closed(1), TimeBound::closed(2));
  FormulaSet X; ZoneSet s = satisfaction_set(mu, X, /*x_mu=*/1, 2, {0,2}, f);
  Zone onset(2); /* x_mu=0 */ assert(s.contains(onset)); }

// Paper Example 1: ν=E(pU[1,2]q) under context forcing ¬q on [0,3] ⇒ S_X(ν)=∅
// at the onset. Encode X = {¬q} (persistent), expect onset ∉ S_X(ν).
{ FormulaFactory f; FormulaId p=f.make_atom("p"), q=f.make_atom("q");
  FormulaId nu=f.make_timed_eu(p, q, TimeBound::closed(1), TimeBound::closed(2));
  FormulaSet X; X.insert(f.make_not(q));
  ZoneSet s = satisfaction_set(nu, X, 1, 2, {0,2}, f);
  Zone onset(2); assert(!s.contains(onset)); }
```
(Exact `Zone` construction API from `include/tctl/zone.hpp`; build the `x_mu=0` point via the zone constructor + `constrain`.)

- [ ] **Step 2: Run to verify failure.**

- [ ] **Step 3: Implement the until least-fixpoint.** Operator `F(Y) = B_μ ∪ (sat_X(φ) ∩ pre_Q(Y))` with `B_μ = sat_X(ψ) ∩ (x_μ∈I)`; `pre_Q(Y)` = `ZoneSet(Y).down()` (time-predecessor) further closed under the discrete-step freedom (a discrete edge we are free to build to any `X`-consistent successor; for `Q=A`, intersect over the universal obligation). Iterate from `∅` to a fixpoint (`equals` on successive `ZoneSet`s, after `extrapolate`+`reduce`). **Develop against the Step-1 tests** — the precise `pre_Q` for `Q=A` and the discrete freedom are tuned until both the reachable-`q` and Example-1 cases pass.

- [ ] **Step 4: Implement the release greatest-fixpoint.** Dual: start from `⊤`, `G(Y) = base_release ∪ (obligation narrowing over `x_μ∈I` unless `sat_X(φ)` releases) ∩ post-closure`, iterate down to fixpoint. Add a release unit test (e.g. `A(⊥ R[0,3] ¬q)` = `AG[0,3]¬q`: its `S_X` at onset is the whole zone since `¬q` is freely labelled, but forbids `q` in `[0,3]`).

- [ ] **Step 5: Run all `S_X` tests, commit.**
```bash
git add -A -- include/tctl/satisfaction_set.hpp src/satisfaction_set.cpp src/paper_oracle.cpp
git commit -m "feat(engine): S_X(mu) satisfaction-set fixpoint (until/release)"
```

---

## Task 3: Cover rule `Cov` / `Cov*` / close

**Files:** Modify `src/paper_tableau.cpp`, `include/tctl/paper_tableau.hpp`, `src/paper_oracle.cpp`.

**Interfaces:**
- Produces (internal):
  ```cpp
  struct CoverResult {
      enum Kind { Cover, PartialCover, Close } kind;
      std::vector<Node> children;   // Cover: {discharge, launch} (AND);
                                     // PartialCover: one narrowed OR-child per cvx component
  };
  CoverResult apply_cover(const Node& n, FormulaId mu, /*engine ctx*/…);
  ```

- [ ] **Step 1: Failing test** — a node whose zone lies inside `S_X(μ)` yields `Cover` with exactly two children (discharge drops `μ`; launch adds a `Pursuit` with fresh `x_μ`, `Z[x_μ:=0]`, and a deadline **iff** `μ` is A-until). A node with `Z ∩ S_X(μ)=∅` yields `Close`.

- [ ] **Step 2: Run to verify failure.**

- [ ] **Step 3: Implement `apply_cover`.** Compute `s = satisfaction_set(mu,…)`. Test `(Z ∧ x_μ=0) ⊆ s` (lift `Z` with `x_μ=0`, `s.contains(lifted)` / `is_subset_of`). Full → build discharge + launch nodes. Partial (`Z ∩ s ≠ ∅`) → `components()` of `Z ∩ s` as OR-children. Empty → `Close`. Apply `D_μ` only for A-until.

- [ ] **Step 4: Run tests, commit** (`feat(engine): cover rule Cov/Cov*/close`).

---

## Task 4: Pursuit rules `U•`, `R^split`, `R•`

**Files:** Modify `src/paper_tableau.cpp`, `src/paper_oracle.cpp`.

**Interfaces:**
- Produces (internal): `std::vector<Node> pursue(const Node& n, const Pursuit& p, …)` producing the OR-children of `U•`/`R•_{≺I}`/`R•_{∈I}` or the AND-children of `R^split`, per spec §6.

- [ ] **Step 1: Failing tests** for each rule shape:
  - `U•` (E): stop child adds `ψ`, constrains `Z ∩ (x_μ∈I)`, drops the deadline; go child adds `φ` and stages `μ•` `DeferEX`.
  - `U•` (A): go child stages `μ•` `DeferAX` and puts the residual into `X`.
  - `R^split`: partitions `Z` into ≤3 region children by `x_μ` vs `I`; the `≻I` child drops the pursuit.
  - `R•_{∈I}`: stop `{φ,ψ}`; go `{ψ}` + `EX/AX μ•`.

- [ ] **Step 2: Run to verify failure.**

- [ ] **Step 3: Implement `pursue`** using `ZoneSet::constrain_lower/upper` (with strictness from `TimeBound`) to build `x_μ∈I`, `Z^{≺I}`, `Z^{∈I}`, `Z^{≻I}`; drop empty regions.

- [ ] **Step 4: Run tests, commit** (`feat(engine): pursuit rules U•, R^split, R•`).

---

## Task 5: Successor generation — Delay `Δ°/Δ^∂` and EX + stutter

**Files:** Modify `src/paper_tableau.cpp`, `src/paper_oracle.cpp`.

**Interfaces:**
- Produces (internal):
  ```cpp
  std::pair<Zone,Zone> delay_split(const Node& n, const std::vector<std::int32_t>& max); // (Δ°Z, Δ^∂Z), each ∩ Inv(N)
  std::vector<Node> ex_successors(const Node& n); // one child per EXμ•; stutter if none
  ```

- [ ] **Step 1: Failing tests.**
  - `delay_split` on `Z` with an active bound at the next hyperplane `x=b (b≤M)`: `Δ°Z` = time-successor strictly below `x=b`; `Δ^∂Z` = the `x=b` slice; both `∩ Inv(N)`. When no hyperplane ≤ M remains, `Δ^∂Z = ↑Z`.
  - `ex_successors`: with a `DeferEX` pursuit, one child carries `{μ•}∪X` under context `X`; with none, a single stutter child `⟨X,X,Z,O,D⟩`.

- [ ] **Step 2: Run to verify failure.**

- [ ] **Step 3: Implement.** `delay_split`: from the current extrapolated `Z`, compute the least integer hyperplane strictly above the current zone among active clocks (≤ M); `Δ°Z = up(Z)` constrained `< b`; `Δ^∂Z = up(Z)` constrained `= b`; intersect both with `Inv(N)`. `ex_successors`: gather `DeferEX` pursuits into per-child `{μ•}∪X`; else stutter.

- [ ] **Step 4: Run tests, commit** (`feat(engine): Delay Δ°/Δ^∂ and EX successors`).

---

## Task 6: Graph construction + memoization + loop closure

**Files:** Modify `include/tctl/paper_tableau.hpp` (graph storage, stats), `src/paper_tableau.cpp`, `src/paper_oracle.cpp`.

**Interfaces:**
- Produces: full `PaperTableau::check` builds the AND–OR graph on the fly: saturate → cover every demanded `μ` → pursue launched `μ•` → generate Delay+EX successors; memoize nodes by `(Γ, X, canon_{≅_M}(Z), O-sig, D, pursuits)`; a child equal to an ancestor becomes a back-edge (loop). Graph exposed for Task 7. Add `struct PaperStats { uint32_t nodes, loops, distinct_zones; }` + `const PaperStats& stats() const`.

- [ ] **Step 1: Failing test** — a small formula that must be SAT purely by graph existence with a trivial always-accepting loop, e.g. `AG[0,2] p` (an untimed-ish safety that a 1-node stutter loop satisfies). Assert `check == Satisfiable` (acceptance still trivial/true here — real acceptance in Task 7).

- [ ] **Step 2: Run to verify failure.**

- [ ] **Step 3: Implement graph build + memo.** Node table keyed by the canonical tuple; DFS with an ancestor set for loop detection; store AND/OR kind per node and child edges (incl. back-edges).

- [ ] **Step 4: Run tests, commit** (`feat(engine): on-the-fly AND-OR graph with memo + loop closure`).

---

## Task 7: Marking / elimination acceptance + non-Zeno loop condition

**Files:** Modify `src/paper_tableau.cpp`, `src/paper_oracle.cpp`.

**Interfaces:**
- Produces (internal):
  ```cpp
  bool time_progressing(const std::vector<const Node*>& loop, const std::vector<std::int32_t>& max);
  bool until_discharged_on(const std::vector<const Node*>& loop, const Pursuit& p);
  bool root_survives();   // elimination fixpoint; PaperTableau::check returns SAT iff true
  ```

- [ ] **Step 1: Failing tests — the paper's Fig. 1 oracle** (the real acceptance test):
```cpp
check_case("AG[0,4]E(p U[1,2] q) & AG[0,3](!q)", Verdict::Unsatisfiable); // Fig 1a
check_case("AG[0,4]E(p U[1,2] q)",               Verdict::Satisfiable);   // Fig 1b
check_case("EF[1,2] q & AG[0,3](!q)",            Verdict::Unsatisfiable);
check_case("EF[2,2] q & AG[0,1](!q)",            Verdict::Satisfiable);   // punctual (Task 8 relaxes parser)
check_case("EF[2,2] q & AG[0,3](!q)",            Verdict::Unsatisfiable); // punctual
```
Plus a **Zeno discriminator**: a formula whose only would-be model needs a bounded cycle with zero elapsed time must be `Unsatisfiable` (fails time-progress).

- [ ] **Step 2: Run to verify failure.**

- [ ] **Step 3: Implement elimination** (spec §7): repeatedly delete closed nodes, OR-with-all-children-gone, AND-with-a-dead-child, nodes with no surviving path to a time-progressing loop, and nodes with an undischarged active until-pursuit. `time_progressing`: positive elapsed delay on the segment and every clock reset-on-segment or extrapolated `> M`. `until_discharged_on`: some node on the loop took the `(U•)` stop branch with `Z_k ∩ (x_μ∈I) ≠ ∅`. Root survives ⇔ SAT. Iterate ≤ node-count rounds.

- [ ] **Step 4: Run the full Fig. 1 oracle + Zeno case, commit** (`feat(engine): marking/elimination acceptance with non-Zeno loop condition`).

---

## Task 8: Punctuality — accept `[a,a]`, warn at depth > 1

**Files:** Modify `src/parser.cpp` (~line 282), `UppaalPlugin/translator/uppaal2tctl.py` (~line 357), `src/cli.cpp` (emit warning via `analyze_punctuality`), `README.md`, `UppaalPlugin/DESIGN.md`, `src/paper_oracle.cpp`.

- [ ] **Step 1: Failing test** — `parse_formula("EF[2,2] p", f)` must not throw; `EF[3,3) p` must still throw (empty). Add both to the oracle harness.
- [ ] **Step 2: Run to verify failure** (parser currently rejects `a=b`).
- [ ] **Step 3: Relax the gate** in `parser.cpp` to allow `a==b` for closed-closed `[a,a]` only; keep `(a,a)`, `[a,a)`, `(a,a]`, `a>b` rejected. Mirror in `uppaal2tctl.py`. In `cli.cpp`, call `analyze_punctuality`; if it reports a punctual interval at timed-nesting depth > 1, print the stderr completeness warning.
- [ ] **Step 4: Run tests; update README + plugin note; commit** (`feat(parser): accept punctual [a,a] with depth>1 completeness warning`).

---

## Task 9: End-to-end CLI wiring + oracle audit

**Files:** Modify `src/cli.cpp`, `src/main.cpp`, `src/paper_oracle.cpp`, `README.md`.

- [ ] **Step 1: Failing test** — end-to-end: `printf 'AG[0,2] p\n' | ./build-macos/tctl_sat /dev/stdin` prints `SATISFIABLE`; a known-UNSAT prints `UNSATISFIABLE`. Add a shell smoke check to the oracle or a `scripts/smoke.sh`.
- [ ] **Step 2: Run to verify failure/gaps.**
- [ ] **Step 3: Wire `run(Options)`** fully to `PaperTableau` (verdict, `--stats`), remove dead `--legacy`/benchmark paths. Broaden the oracle: boolean/arithmetic consistency cases, an existential-until SAT witness, a release SAT/UNSAT pair, nested-depth-2 SAT.
- [ ] **Step 4: Full `--selftest` green; commit** (`feat(cli): wire verdict path end-to-end; broaden semantic oracle`).

---

## Later (separate spec): Witness TA extraction (Theorem 2)

Read the witness TA off the surviving marking (locations = marking nodes labelled by `Γ_prop` with `Inv(N)`; discrete transitions = AND-children guarded by `Z_N ∩ Inv(N)`; `x_μ` reset at launches; Delay contributes no transition). Rebuild `src/timed_automaton.cpp` around the new node model. Out of scope here.

## Self-review notes

- **Spec coverage:** every spec §2–§9 item maps to a task (modules→T0; node/saturation/Z3→T1; `S_X`→T2; cover→T3; pursuit→T4; successors→T5; graph→T6; acceptance→T7; punctuality→T8; CLI+oracle→T9; TA deferred per §1/§11).
- **`pre_Q` risk:** T2 is explicitly TDD against hand-computed zones incl. paper Example 1 (`S_X(ν)=∅`) — the correctness-critical operator is pinned by tests, not assumed.
- **Type consistency:** `satisfaction_set(...)`, `sat_leaf(...)`, `node_closed(...)`, `apply_cover`, `pursue`, `delay_split`, `ex_successors`, `Verdict`, `Node/Pursuit/Deadline` names are used consistently across T0–T9.
- **Order safety:** acceptance (T7) depends on the graph (T6) which depends on successors/pursuit/cover (T3–T5) which depend on `S_X` (T2) and the node model (T1); no forward references.
