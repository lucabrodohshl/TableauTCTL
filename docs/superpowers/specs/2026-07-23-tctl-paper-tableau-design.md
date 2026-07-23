# A faithful port of the ETAPS2026 tableau for TCTL satisfiability

**Status:** design approved (direction), implementation choices delegated to the
implementer. **Paper:** Brodo, Scalora, Henkler, *"A Tableau for TCTL"*
(ETAPS 2026, `../../../ETAPS2026.pdf`). **Repo:** `Implementation/` (git,
branch `newstuff`).

## 1. Goal and scope

Replace the engine core with the paper's construction. The current
`src/tableau.cpp` is the *old* Wolper-style direct timed tableau; the functions
named `expand_timed_paper` / `paper_delay_regions` are a facade — there is **no**
satisfaction set `S_X(μ)`, **no** cover rule, **no** marking/elimination
acceptance, and the witness is an untimed Kripke model, not a timed automaton.
We build a clean engine that mirrors §4 of the paper, reusing only sound
infrastructure.

**Fragment.** The paper's TCTL (§3): `⊤ | ⊥ | p | ¬p | φ∧φ | φ∨φ |
E(φ U_I φ) | E(φ R_I φ) | A(φ U_I φ) | A(φ R_I φ)`, in NNF, over time bounds `I`
with integer endpoints. Atoms `p` are **state predicates** — boolean
combinations of propositions and integer/real arithmetic constraints — whose
consistency is decided by Z3 (see §3). There is **no object-level next**: over
dense time no configuration has an immediate successor. `EX`/`AX` appear only as
internal pursuit markers. Untimed operators map to `I = [0,∞)`. Sugar
`EF/AF/EG/AG` desugars as today (`AG_I φ ≡ A(⊥ R_I φ)`, etc.).

**Out of scope for this deliverable (verdict-first):** the Theorem-2 witness
timed-automaton extraction. The engine returns SAT/UNSAT (+ statistics). TA
extraction is a following phase; `src/timed_automaton.cpp` is parked until then.

**Deliverable guarantees (paper §5.2, Remark 1):** sound and terminating for all
of TCTL incl. punctual `[a,a]`; complete for the non-punctual fragment (`a<b`).
Punctual input is accepted; at timed-nesting depth `> 1` a completeness warning
is printed (a SAT verdict stays reliable, an UNSAT verdict may be a false
negative). Empty intervals stay rejected.

## 2. Module layout

New:

| file | responsibility | testable in isolation? |
|---|---|---|
| `include/tctl/satisfaction_set.hpp`, `src/satisfaction_set.cpp` | the pure fixpoint `S_X(μ) → ZoneSet` and the leaf `sat_X(ψ)` region helper. No graph search. | yes — the crux, developed test-first |
| `include/tctl/paper_tableau.hpp`, `src/paper_tableau.cpp` | node `⟨Γ,X,Z,O,D⟩` + pursuits; saturation; cover; pursuit; Delay/EX successors; memoized DFS graph; marking/elimination acceptance; verdict | via oracle suite |
| `src/paper_oracle.cpp` (+ header) | hand-verified semantic oracle replacing `test.cpp`/`benchmark.cpp` | — |

Reused unchanged: `lexer`, `parser`, `ast`, `normalization`, `zone`, `zoneset`,
`z3_solver`, `utils`, UDBM.

Kept but re-roled: `z3_solver` — node closure oracle (§3).

Deleted: `src/tableau.{cpp}` + `include/tctl/tableau.hpp` (old engine),
`src/test.cpp`, `src/benchmark.cpp` (+ their headers), and their `CMakeLists.txt`
targets. `cli.cpp` rewired to the new engine.

Parked: `src/timed_automaton.cpp` (old Kripke extraction) — revisited in the TA
phase.

## 3. Z3 as the node closure oracle

`Z3Checker::add_state_formula` already ingests propositional + arithmetic state
predicates and ignores temporal operators. A node is **closed** when either its
zone `Z` is empty, or the conjunction of its propositional/arithmetic leaves
`Γ_prop` is Z3-`UNSAT`. The arithmetic/real state variables Z3 reasons about are
frozen state data at a node, **orthogonal to the DBM clocks** that advance with
time. Consequently, in `S_X(μ)` a propositional/arithmetic leaf `ψ` contributes
`⊤` (all clock valuations) when Z3 says it is consistent under the context, and
`∅` otherwise; all *clock* constraints (`x_μ ∈ I`, guards, resets) stay in
`ZoneSet`. Z3 and the zone machinery never mix.

## 4. Node data model (paper §4.1)

`N = ⟨Γ, X, Z, O, D⟩` plus the pursuit state:

```cpp
struct Deadline { ClockId x_mu; std::int64_t bound; bool strict; };   // x_mu ≤/< bound

struct Pursuit {
    FormulaId mu;                 // launched modality Q(φ ∘_I ψ)
    ClockId   x_mu;               // its formula-clock (also a key in O)
    enum Stage { Here, DeferEX, DeferAX } stage;   // μ• | EXμ• | AXμ•
    enum Part  { Whole, BeforeI, InI }   part;     // R^split region (Whole for until)
    bool      is_until;           // true → until (acceptance cond. (i) applies)
};

struct Node {
    FormulaSet             Gamma;      // goal formulas + literals
    FormulaSet             X;          // universal context (AX obligations)
    Zone                   Z;          // canonical ≅_M-extrapolated DBM
    std::map<FormulaId,ClockId> O;     // launched μ ↦ x_μ
    std::vector<Deadline>  D;          // ⇒ Inv(N) = ⋀ x_μ ≤/< bound
    std::vector<Pursuit>   pursuits;   // active μ• (with stage/part)
};
```

**Design choice:** pursuit markers `μ•/EXμ•/AXμ•` live in the dedicated
`pursuits` field, **not** as synthetic AST nodes in `Γ`. `Γ` stays a clean set of
TCTL formulas; the `EX/AX` residual and the `R`-region are explicit, which the
`R•` rules and acceptance condition (i) need. `AXμ•` residuals additionally
seed `X` so they propagate to all successors automatically.

`Inv(N) = ⋀_{(x_μ,b,s)∈D} x_μ ≤/< b`. A deadline is applied (paper §4.2 p.6)
**iff** `μ` is a *universal until*: `D_μ = {(x_μ, sup I)}`; existential untils and
both releases add no deadline.

**Node identity (memo / loop closure):** the tuple
`(Γ, X, canon_{≅_M}(Z), O-signature, D, pursuits)`. Two nodes are `N_i ≡ N_j`
(close a loop) when equal componentwise with zones compared modulo `≅_M`
(`extrapolate` then canonical DBM). Zones are extrapolated with the per-clock max
constants before hashing.

## 5. `S_X(μ)` — the satisfaction set (crux; §4.2, §5.1)

`S_X(μ) ⊆ ℝ_{≥0}^{C∪{x_μ}}` is the set of clock valuations at which `μ` holds
under context `X`, with `x_μ` the fresh formula-clock measuring `I` from the
onset (`x_μ = 0` at the demanding configuration).

**Coverage test.** The cover rule tests the node's zone at the onset:
`Z ⊆ S_X(μ)` is read as `(Z ∧ x_μ = 0) ⊆ S_X(μ)` — i.e. every valuation of `Z`,
extended with `x_μ = 0`, lies in `S_X(μ)`. Equivalently, `Z ⊆ (S_X(μ)|_{x_μ=0})`
projected back to `C`.

**Leaf region `sat_X(ψ)`** (clock-valuation set where `ψ` holds under `X`), by
recursion on `ψ`:
- `ψ` propositional/arithmetic leaf → `⊤` if `Γ_prop(X) ∧ ψ` is Z3-SAT, else `∅`.
- `ψ = a ∧ b` → `sat_X(a) ∩ sat_X(b)`; `ψ = a ∨ b` → `sat_X(a) ∪ sat_X(b)`.
- `ψ = ν` a modality → `S_X(ν)` (recursion on `FL(φ)`; `ν` has its own fresh
  clock, existentially quantified out of the ambient clock space when composing).

**Fixpoint.** `S_X(μ)` is a Knaster–Tarski fixpoint of a monotone operator on
finite unions of `≅_M`-zones (`ZoneSet`): **least** for until, **greatest** for
release; reached by finite iteration (the lattice is finite). The operator is
the pursuit unfolding of §4.2:

- **Until** `Q(φ U_I ψ)` (least, from `∅`):
  `F(Y) = B_μ ∪ ( sat_X(φ) ∩ pre_Q(Y) )` where
  `B_μ = sat_X(ψ) ∩ (x_μ ∈ I)` is the base (stop) zone and `pre_Q` is the
  timed/discrete predecessor operator (delay `down` composed with the discrete
  step freedom; `∃`-successor for `Q=E`, `∀`-successor for `Q=A`).
- **Release** `Q(φ R_I ψ)` (greatest, from `⊤`): dual — obligation `ψ` enforced
  for `x_μ ∈ I` unless released by `φ`, per the `R^split`/`R•` unfolding.

`down()` (time-predecessor) is the ZoneSet primitive behind the until
least-fixpoint. The operator refers to `S_X` only through modalities strictly
inside `φ,ψ`, so the whole computation is well-founded induction on `FL(φ)` and
memoizable by `(μ, X)`.

> **Highest-risk component.** The exact `pre_Q` operator — the discrete-step
> freedom "we may build any successor consistent with `X`", the `Q=A`
> "all successors" universal predecessor, and the release greatest-fixpoint
> narrowing — is where a faithful port can go wrong. It is developed
> **test-first** against hand-computed `S_X` values, using the paper's own
> worked examples as oracles: Example 1 gives `S_X(ν) = ∅` at the onset for
> `ν = E(p U_{[1,2]} q)` under a context forcing `¬q` on `[0,3]`, and the
> `μ1 ∧ μ2` run closing at `Z ∩ S_X(μ1) = ∅`; Example 2 gives the SAT run
> where covering `ν` at `N_4` succeeds.

## 6. Rules (paper §4.2)

**Saturation** (applied until no rule fires; only saturated+covered nodes make
successors):
- `(∧)` deterministic: `Γ∪{φ∧ψ} → Γ∪{φ,ψ}`.
- `(∨)` OR-branch: `Γ∪{φ∨ψ} → Γ∪{φ} | Γ∪{ψ}`.
- `(AX)` deterministic: `Γ∪{AXφ}, X → Γ, X∪{φ}` (move argument into context).
  (Object-level `AX` only ever arrives as the `AXμ•` residual placed in `X`; see
  §1 — the input fragment has no object next.)

**Cover** on a demanded `μ = Q(φ ∘_I ψ) ∈ Γ` (compute `S_X(μ)` first):
- `Z ⊆ S_X(μ)` → `Cov` (AND ⊗ of two children):
  **discharge** `⟨Γ, X, Z, O, D⟩` (drop `μ`) and
  **launch** `⟨Γ∪{μ•}, X, Z[x_μ:=0], O[μ↦x_μ], D∪D_μ⟩`
  (`x_μ` fresh; `D_μ = {(x_μ,sup I)}` iff `μ` is an A-until, else `∅`).
- `Z ⊄ S_X(μ)` but `Z ∩ S_X(μ) ≠ ∅` → `Cov*` (OR ⊕ over convex components):
  narrow to `Z_i ∈ cvx(Z ∩ S_X(μ))` = `ZoneSet::components()`, one OR-child each.
- `Z ∩ S_X(μ) = ∅` → **close**.

**Pursuit** (in the launch branch, one step at a time):
- Until `(U•)` on `μ• = Q(φ U_I ψ)` — OR ⊕:
  **stop** `⟨Γ∪{ψ}, X, Z∩(x_μ∈I), O, D∖{(x_μ,sup I)}⟩` (discharge; drop deadline);
  **go** `E → ⟨Γ∪{φ}, X, Z, O, D⟩` with `μ•` staged `DeferEX`;
  `A → ⟨Γ, X, Z, O, D⟩` with `μ•` staged `DeferAX` (residual into `X`).
- Release `(R^split)` on `μ• = Q(φ R_I ψ)` — AND ⊗, partition `Z` by `x_μ` vs `I`:
  `Z^{≺I}` (before), `Z^{∈I}` (in), `Z^{≻I}` (after → drop `μ•`, lapsed). Empty
  parts dropped. Pursue before/in:
  - `(R•_{≺I})` — OR ⊕: **stop** `⟨Γ∪{φ}, X, Z^{≺I},…⟩`; **go**
    `E → {EXμ•}`, `A → X∪{AXμ•}` (no `ψ` obligation before the window).
  - `(R•_{∈I})` — OR ⊕: **stop** `⟨Γ∪{φ,ψ}, X, Z^{∈I},…⟩`; **go**
    `⟨Γ∪{ψ}, …⟩` + `E → EXμ•` / `A → AXμ•` (`ψ` obligatory each in-window step).

**Successor generation** (saturated + covered node):
- `(Delay)` AND ⊗, integer-hyperplane split: `Δ°Z` = time-successor of `Z`
  strictly below the next hyperplane `x = b` (`b ≤ M`) of an active bound;
  `Δ^∂Z` = that hyperplane (`= ↑Z` when none remains at/below `M`). Two children
  `⟨Γ,X,Δ°Z∩Inv(N),O,D⟩` and `⟨Γ,X,Δ^∂Z∩Inv(N),O,D⟩`.
- `(EX)` AND ⊗: one child `⟨{ψ}∪X, X, Z, O, D⟩` per demanded `EXψ` (i.e. per
  `DeferEX` pursuit residual `EXμ•`); a single **stutter** child
  `⟨X, X, Z, O, D⟩` when there is no `EXψ`. Every child inherits `X`, so `AXμ•`
  residuals and universal obligations constrain the whole branching.

## 7. Acceptance (paper §4.3, §5.1)

Build the AND–OR graph on the fly (DFS, memoize by §4 node identity, close loops
at repeated nodes mod `≅_M`). A **marking** picks one child at each OR-node and
all children at each AND-node. A **candidate loop** `N_i ≡ N_j` is **accepting**
iff:
1. every **until** pursuit `μ•` active at `N_i` is discharged on the segment —
   the `(U•)` stop branch is taken for `μ` at some `N_k` with
   `Z_k ∩ (x_μ ∈ I) ≠ ∅`;
2. it is **time-progressing** — positive elapsed time on the segment, and every
   clock is either reset on the segment or extrapolated above `M`.

**Successful marking via elimination** (greatest fixpoint; ≤ `m` rounds, each
deletes ≥1 node): repeatedly delete
- every **closed** node;
- every **OR** node whose children are all deleted;
- every **AND** node with a deleted child;
- every node with no surviving path to a time-progressing loop;
- every node with an undischarged active until-pursuit (no surviving path takes
  its `(U•)` stop branch).

The last two are reachability queries over the surviving subgraph, recomputed
each round (sound because deletion only removes paths). **Root survives ⇔ SAT.**

**Termination** (§5.1): nodes are drawn from a finite set
(`2^{O(n)} · M^{O(n²)}`); memoization expands each at most once; DFS never
unfolds past a repeated node, so every infinite branch closes into a loop.

## 8. Punctuality (Remark 1)

Accept punctual `[a,a]` (the procedure is sound + terminating on all TCTL).
Relax the two rejection gates (`src/parser.cpp:~282`,
`UppaalPlugin/translator/uppaal2tctl.py:~357`) to admit `[a,a]` while keeping
empty intervals (`(a,a)`, `[a,a)`, `(a,a]`, `a>b`) rejected. Emit a stderr
completeness warning when a punctual interval occurs at timed-nesting depth `> 1`
(depth-1 punctual is author-asserted complete; the Uppaal flat shapes are
depth-1). Document in README + plugin note.

## 9. Testing — a hand-verified semantic oracle

Per project guidance, the existing `test.cpp`/`benchmark.cpp` expected verdicts
are **not** a trusted oracle. Replace them with `paper_oracle.cpp`, each case
justified from TCTL semantics (an explicit witness TA, or an explicit
impossibility argument), not from the old engine. Seed cases:

| formula | verdict | justification |
|---|---|---|
| `AG[0,4]E(pU[1,2]q) ∧ AG[0,3]¬q` (Fig. 1a) | UNSAT | paper Example 1 |
| `AG[0,4]E(pU[1,2]q)` (Fig. 1b) | SAT | paper Example 2 (1-loc witness) |
| `EF[1,2]q ∧ AG[0,3]¬q` | UNSAT | window inside the forbidden band |
| `EF[2,2]q ∧ AG[0,1]¬q` (punctual) | SAT | `q` reachable at exactly `2` |
| `EF[2,2]q ∧ AG[0,3]¬q` (punctual) | UNSAT | `2` inside the forbidden band |

Additionally, **unit-test `S_X`/`sat_X` directly** against hand-computed
`ZoneSet` values (§5), independent of the graph search — this is where
correctness is won or lost. Layer in: boolean/propositional consistency via Z3
(incl. arithmetic-atom cases like `x≤2 ∧ x≥5` UNSAT), release/greatest-fixpoint
cases, and non-Zeno loop discrimination (a bounded-cycle "zeno" formula must be
UNSAT).

## 10. Phase plan (implementation order)

Each phase ends green (built with `-Werror`, oracle passing) before the next.

| # | phase | gate |
|---|---|---|
| 0 | Module scaffolding: new headers/sources, CMake targets, delete old engine + tests, rewire `cli.cpp` to a stub verdict path; keep Z3 | builds; `--selftest` runs the (initially tiny) oracle |
| 1 | Node + saturation (∧, ∨, AX) + Z3 closure + `sat_X` for leaves/booleans | `sat_X` unit tests green |
| 2 | `S_X(μ)` fixpoint: until (least) then release (greatest), recursion on FL | `S_X` unit tests vs hand-computed zones (incl. Fig. 1 `S_X(ν)=∅`) |
| 3 | Cover `Cov`/`Cov*`/close using `S_X` | cover-decision unit tests |
| 4 | Pursuit `U•`, `R^split`, `R•` (drives launch branch + reused by `S_X`) | pursuit unfolding tests |
| 5 | Successors: Delay `Δ°/Δ^∂`, EX + stutter | successor-shape tests |
| 6 | Graph construction + memo + loop closure | small SAT/UNSAT decided |
| 7 | Marking / elimination acceptance + non-Zeno loop condition | full oracle green incl. Fig. 1a/1b |
| 8 | Punctuality gate relax + depth>1 warning + docs | punctuality quick-check green |
| 9 | Audit + broaden oracle; wire verdict path end-to-end in CLI | end-to-end green |
| (later) | TA witness extraction (Theorem 2) | separate spec |

## 11. Non-goals / deferred

- Witness TA extraction (Theorem 2) — next deliverable.
- The §6 evaluation benchmark harness — regenerated after the engine is correct.
- OpenMP parallel DFS — the old engine's concurrency is not ported until the
  sequential engine is validated (correctness before speed).
