# Performance-evaluation plan — TCTL satisfiability tableau

**Status:** design only. A second engineer implements directly from this document. No
benchmark code is written here.

**What this is and is NOT.** This is a *performance characterization* of one decision
procedure, not a comparison. There is **no comparable baseline**: La Torre–Napoli give no
implementation, and UPPAAL does *model checking*, not *satisfiability*. We therefore frame
every result as "where does this single procedure spend its time/space, and is it practical
on real-shaped queries", never as "faster/slower than X". State this explicitly in the paper.

**Relationship to the existing correctness benchmark.** The correctness suite
(`bench_*.py`, `ANALYSIS.md`) already established *soundness* against a by-construction
oracle (0/199 mismatches) and gave the first scaling hints. This plan **does not re-run the
oracle and produces no verdict-validation table.** It reuses that suite's empirical walls as
*priors* and turns them into a clean, single-factor performance story:

| Prior observed in `ANALYSIS.md`                          | What this plan does with it                              |
|----------------------------------------------------------|----------------------------------------------------------|
| Nested double-check: UNSAT exponential, SAT cheap        | RQ1 headline driver + the SAT/UNSAT asymmetry figure     |
| Clock/obligation pressure: 2nd wall, 12/36 timeouts      | RQ1 secondary driver (zone-dimensionality)               |
| Large M (≤8192) absorbed sub-second by zones             | RQ1 negative control: M is *not* a driver                |
| Zeno rejection cheap                                     | Not a cost axis; excluded from this perf eval            |

**Implementation reuse.** Build on the existing harness — do not rewrite it:
- *Generators:* new module `perf_families.py`, mirroring `bench_families.py` (same `Variant`
  dataclass; reuse the low-level builders `ag/ef/af/eu/au/er/conj`, `_iv`, `validate`,
  `max_constant`).
- *Materialise + manifest:* reuse `bench_generate.py` (point `--outdir` at a fresh
  `outputs_perf/` and import `perf_families` instead of `bench_families`, or add a
  `--families-module` flag).
- *Runner:* reuse `bench_run.py` unchanged (parses `<n>: SATISFIABLE|UNSATISFIABLE|TIMEOUT`
  and the `  Stats: nodes=… distinct_zones=… peak_mem_kb=…` line; writes `results.csv`).
  Add only repetition support (below).
- *Plots/tables:* new module `perf_plot.py` producing exactly the figures/tables in §4.

**Solver interface (verified against source).**
- Invoke per formula: `<solver prefix> [timeout …] tctl_sat --stats <file>` (one formula per
  file). Verdict line: `1: SATISFIABLE` / `1: UNSATISFIABLE`. Stats line (`src/tableau.cpp`
  `TableauStats::to_string`):
  `  Stats: nodes=… open=… closed=… max_depth=… memo_hits=… loop_checks=… distinct_zones=… peak_mem_kb=… avg_mem_per_node=…`.
- Syntax (verified against `src/lexer.cpp`, `examples/tctl_examples.txt`): atoms `p,q,p1,…`;
  `! & | -> <->`, `true/false`; `EF AF EG AG` (timed `EF[a,b] φ`, untimed = `[0,inf)`);
  `E(. U[a,b] .) A(. U[a,b] .) E(. R[a,b] .) A(. R[a,b] .)`; intervals `[a,b] (a,b) [a,inf)`,
  non-punctual (`a<b`), no `EX/AX`. Nesting such as `AG(p -> EF q)` parses, so the UPPAAL
  leads-to shape `AG[0,inf)((p) -> AF[a,b](q))` is expressible directly.

**Complexity facts that ground the hypotheses** (from `tableau.tex`, `correctness.tex`):
distinct nodes ≤ `2^{O(n log n)} · M^{O(n²)}`, with `n=|φ|`, `M`=largest integer constant,
`K=O(n)` formula-clocks (one per timed subformula). ExpTime-complete. The cost has three
algebraic handles: (i) `2^{O(n)}` from the Fischer–Ladner closure / AND-OR branching of the
*nested* check; (ii) `M^{O(K²)}` zones from the DBM dimension = number of *simultaneously
live* formula-clocks; (iii) `M` enters only inside the zone bounds, absorbed by max-constant
extrapolation `≅_M`. RQ1 maps one family onto each handle, plus the SAT/UNSAT asymmetry that
decides whether the search is short-circuited (a witness) or exhausted (a refutation).

---

## 1. Research questions and hypotheses

### RQ1 — Cost drivers & scalability
*Which structural parameters of the input dominate the procedure's time and memory, how does
it scale in each, and where is the practical wall?* Isolate **one factor per family**, all
others fixed.

> **H1 (hypothesis).** Cost is driven by the two *branching/dimension* handles of the bound,
> not by the magnitude of constants: **nesting depth of the timed double-check** is the
> dominant driver — runtime and search size grow **exponentially** in depth on UNSAT
> (forced exhaustion of the AND-OR graph, the `2^{O(n)}` handle) but stay **near-linear** on
> SAT (an early witness short-circuits the search); the **number of simultaneously-active
> clocks/obligations** is the secondary wall — **super-polynomial** growth in distinct zones
> (the `M^{O(K²)}` handle); whereas the **max-constant M** and **raw propositional formula
> size at fixed depth/clocks** are *absorbed* (flat curves), because `≅_M` extrapolation and
> on-the-fly memoisation keep the realised node set small. Practical wall ≈ depth d≈6 (UNSAT)
> and k≈12–15 simultaneous clocks.

### RQ2 — UPPAAL-style (flat, 1-level) queries
*How does the procedure perform on the flat TCTL queries engineers actually write in UPPAAL —
reachability, safety, bounded liveness, leads-to — over atomic propositions, as query size
and time-bounds scale? Is it practical, in contrast with RQ1's adversarial nested families?*

> **H2 (hypothesis).** Flat (1-level) UPPAAL-shaped queries are **outside the exponential
> regime**: they have nesting depth ≤ 2 and O(1) simultaneously-live clocks, so neither RQ1
> wall is triggered. Runtime, nodes and memory stay in the **sub-second to low-seconds**
> range and are **essentially flat** in both query size and time-bound (bounds absorbed by
> zones, size absorbed by memoisation). The procedure is practical exactly on the case
> engineers care about; the adversarial nested families of RQ1 are the *only* ones that
> approach the timeout.

**What counts as the answer.**
- RQ1: the *ranked* list of drivers (depth ≫ clocks ≫ {M, size}), each annotated with its
  fitted growth law (exp vs power vs flat; §4 Table T1), and the located wall (first depth /
  k that times out at 60 s). The SAT/UNSAT asymmetry (Fig F1) is part of the answer.
- RQ2: the *practical envelope* — max median time, max nodes, max peak memory, and #timeouts
  over the entire UPPAAL sweep (Table T2) — together with the cactus contrast (Fig F4)
  showing flat queries solved orders of magnitude below the nested families.

---

## 2. RQ1 families (one factor each; others fixed)

All RQ1 families ship matched **SAT** and **UNSAT** variants unless noted, so the SAT/UNSAT
asymmetry is measurable on every axis. Generators reuse `bench_families.py` builders. The
designed verdict is recorded only to *colour the curves and split SAT/UNSAT*, **not** to
re-validate correctness.

### F1 — DEPTH: nesting depth of the timed double-check  *(dominant driver; the ExpTime wall)*
- **Controlled factor (x-axis):** nesting depth `d` of the universal-over-timed-until.
- **Range:** `d ∈ {1,2,3,4,5,6,7,8,9,10}` (linear x). Prior: UNSAT nodes 60→~8000 by d=5,
  timeouts d≥6 — so 1..10 brackets the wall on both sides.
- **Held fixed:** window `[L,U]=[1,3]`, band `B=2`, atoms `{p,q}`, M small (≤ `d·U+1`).
- **Shape (solver syntax):** `Layer₀ = q`, `Layerᵢ = AG[0,2]( E(p U[1,3] (Layerᵢ₋₁)) )`.
  - **SAT** (`DEPTH_sat`): `Layer_d` alone — the p,q-invariant model satisfies every layer.
  - **UNSAT** (`DEPTH_unsat`): `Layer_d  &  AG[0,d*3+1]( !q )` — the nested bands force `q`
    into an absolute window the global band forbids; refutation must unwind all `d` layers.
- **This is the `2^{O(n)}` handle:** depth grows the AND-OR branching of the nested check.

### F2 — OBL: number of simultaneously-active clocks/obligations  *(secondary wall; zone dim.)*
- **Controlled factor (x-axis):** number `k` of conjoined independent timed-untils =
  number of simultaneously-live formula-clocks (DBM dimension `k+1`).
- **Range:** `k ∈ {1,…,18}` (linear x). Prior: 12/36 timeouts in this regime.
- **Held fixed:** depth 1, staggered narrow windows `[i,i+2]`, fresh atom per obligation,
  M = O(k) (small).
- **Shape:**
  - **SAT** (`OBL_sat`): `⋀_{i=1..k} E(true U[i,i+2] q_i)` — k live clocks, all satisfiable.
  - **UNSAT** (`OBL_unsat`): the same conjunction `& AG[0,k+2]( ⋀_{i} !q_i )` — every target
    forbidden across the union of windows, so all k obligations refute simultaneously.
- **This is the `M^{O(K²)}` handle:** all k clocks live at once ⇒ per-node zone work Θ(k²)
  and a distinct-zone count that should grow super-polynomially in k.

### F3 — MAXCONST: magnitude of the largest constant M  *(negative control: not a driver)*
- **Controlled factor (x-axis):** max constant `M`, log-swept.
- **Range:** `M ∈ {1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192}` (log₂ x).
- **Held fixed:** structure = a *single, flat* double-check (depth 1, one timed subformula,
  K=O(1) clocks); only the interval constants scale with M.
- **Shape (reuse `_dcm_base`):** base `AG[0,2M]( E(p U[M,2M] q) )`.
  - **SAT** (`MAXCONST_sat`): `base & AG[0,M-1]( !q )` (killer band below the window ⇒ SAT).
  - **UNSAT** (`MAXCONST_unsat`): `base & AG[0,2M+1]( !q )` (window inside forbidden band ⇒
    UNSAT). One constant flips the verdict; structure is identical across the sweep.
- **Expected (the point):** flat in M — DBM/`≅_M` absorbs large bounds without enumerating
  the timeline. Confirms M is *not* a cost driver.

### F4 — SIZE: raw formula size / # distinct subformulas at fixed depth & O(1) clocks  *(control)*
- **Controlled factor (x-axis):** propositional payload size `m` (number of distinct atoms /
  conjuncts), with nesting depth and *simultaneous* clock count held at O(1). This isolates
  "formula size / number of distinct subformulas" (the `n` in `2^{O(n log n)}`) **away from**
  the simultaneity of F2 and the depth of F1.
- **Range:** `m ∈ {1,2,4,8,16,32,64,128}` (log₂ x).
- **Held fixed:** depth 1, M small fixed (=4), exactly **one** timed modality wrapping a
  large *Boolean* payload (so K stays O(1) while `|φ|` grows linearly in m).
- **Shape:**
  - **SAT** (`SIZE_sat`): `EF[1,4]( p_1 & p_2 & … & p_m )` — `|φ|` grows with m, one clock,
    satisfiable.
  - *(no UNSAT variant needed; this is a control for benign size.)*
- **Expected (the point):** near-flat / mild-polynomial — propositional size inflates the
  Fischer–Ladner closure in principle, but the on-the-fly memoised search realises few nodes,
  so size alone is *not* a wall. Establishes that it is *depth* (F1) and *simultaneity* (F2),
  not raw size, that drive cost.

**RQ1 coverage of the five required factors:** formula size/#subformulas → **F4**; nesting
depth → **F1**; max-constant M → **F3**; simultaneously-active clocks/obligations → **F2**;
SAT-vs-UNSAT asymmetry → matched variants in F1/F2/F3, reported as a cross-cutting result
(Fig F1, and a column in Table T1).

---

## 3. RQ2 families (flat / 1-level UPPAAL queries over atomic propositions)

Abstract away locations/automata: payloads are Boolean formulas over atoms `p,q,r,p_i,q_i`.
Each shape below is the satisfiability instance of a query an engineer writes in UPPAAL.
Every shape is swept on **two** axes: query payload size `m` and time-bound `b`. Default the
*other* axis to its smallest value when sweeping one. Primary instances are **SAT** (the
common case for well-formed specs); each shape also ships one controlled **UNSAT** instance so
the procedure is shown doing real refutation work, not trivially accepting.

UPPAAL → solver mapping (1-level TCTL; leads-to is the canonical AG…AF nesting UPPAAL writes
as a single `-->` query):

| UPPAAL query        | TCTL          | Solver shape (payload `Φ` over atoms)                                  |
|---------------------|---------------|------------------------------------------------------------------------|
| `E<> p` reachability| `EF_[0,b] Φ`  | `EF[0,b]( Φ )`                                                          |
| `A[] p` safety      | `AG_[0,b] Φ`  | `AG[0,b]( Φ )`                                                          |
| `A<> p` liveness    | `AF_[1,b] Φ`  | `AF[1,b]( Φ )`                                                          |
| `p --> q` leads-to  | `AG(p→AF_[1,b]q)` | `AG[0,inf)( (Φ_p) -> AF[1,b]( Φ_q ) )`                              |
| `E[] p`             | `EG Φ`        | `EG[0,inf)( Φ )`                                                        |

**Payload `Φ(m)`** = a disjunction/conjunction over `m` fresh atoms,
e.g. `(q_1 | q_2 | … | q_m)` for reachability/liveness targets and
`(p_1 & p_2 & … & p_m)` for safety/EG invariants; pick whichever keeps the SAT instance SAT.

### U1 — Reachability (`EF`)
- **SAT:** `EF[0,b]( q_1 | … | q_m )`.
- **UNSAT:** `EF[1,b]( q ) & AG[0,b]( !q )` (target reachable in `[1,b]` yet globally forbidden).

### U2 — Safety (`AG`)
- **SAT:** `AG[0,b]( p_1 | … | p_m )`.
- **UNSAT:** `AG[0,b]( p ) & EF[1,b]( !p )` is *not* a clean refutation (SAT via early !p);
  use instead `AG[0,b]( false )` over a divergent reading is the Zeno corner — **avoid**.
  Clean UNSAT: `AG[0,inf)( q ) & EF[1,b]( !q )` (invariant q contradicted by a forced !q).

### U3 — Bounded liveness (`AF`)
- **SAT:** `AF[1,b]( q_1 | … | q_m )`.
- **UNSAT:** `AF[1,b]( q ) & AG[0,b]( !q )` (must reach q within `[1,b]` on all paths, q
  forbidden ⇒ UNSAT).

### U4 — Leads-to / bounded response (`AG(p→AF q)`)
- **SAT:** `AG[0,inf)( (p_1|…|p_m) -> AF[1,b]( q ) )` (vacuous/satisfiable model exists).
- **UNSAT:** `EF[0,b]( p ) & AG[0,inf)( (p) -> AF[1,b]( q ) ) & AG[0,B]( !q )` (a p-state is
  forced, demands a q-response in `[1,b]`, but q is globally forbidden), with `B ≥ b`.

### U5 — `E[]` (`EG`)  *(optional 5th shape; include only if it stays cheap)*
- **SAT:** `EG[0,inf)( p_1 & … & p_m )`.
- *(UNSAT EG is the Zeno corner already covered by the correctness suite; omit here.)*

**Sweep ranges (both axes, all shapes):**
- query size `m ∈ {1,2,4,8,16,32,64,128}` (log₂ x), bound fixed `b=4`.
- time-bound `b ∈ {1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192}` (log₂ x), size fixed
  `m=4`.

The expectation (H2) is that **all** these curves are flat and sub-second/low-seconds, in
sharp contrast with F1/F2.

---

## 4. Metrics, figures, tables

**Metrics recorded per instance** (from the `--stats` line + wall clock):
- `time_s` — wall-clock, **median over R repetitions** (primary).
- `nodes` — tableau nodes created (primary search-space metric; shows *where* cost is).
- `distinct_zones` — DBM/zone count (the `M^{O(K²)}` handle; for F2/F3 panels).
- `peak_mem_kb` — peak memory (for the RQ2 envelope table and a memory check).
- `max_depth`, `loop_checks`, `memo_hits` — recorded for the appendix, not plotted.

> Every figure shows **time *and* a search-space metric** so cost is explained by
> search-space size, never asserted from wall-clock alone.

### Figures (4) — quality over quantity

**F1 — RQ1 headline: SAT/UNSAT asymmetry on nesting depth.**
- *Type:* 2-panel (left = runtime, right = search size) line plot, family **F1 (DEPTH)**.
- *Axes:* x = nesting depth `d` (linear); left y = median time (s, **log**); right y =
  tableau `nodes` (**log**). Timeouts marked as `×` at the 60 s ceiling / last solved nodes.
- *Series:* two curves — `DEPTH_sat` (blue) and `DEPTH_unsat` (red); annotate each with its
  fitted law (semilog slope for UNSAT, near-linear for SAT).
- *Reader concludes:* nesting depth is the dominant driver — UNSAT blows up exponentially
  (the optimal ExpTime procedure exhausting the AND-OR graph to certify unsatisfiability)
  while SAT stays near-linear (a witness short-circuits the search); this gap **is** the
  SAT/UNSAT asymmetry.

**F2 — RQ1 driver comparison: which axes explode, which are absorbed.**
- *Type:* 1×3 small-multiples (one panel per axis), shared y. Optionally a 4th zones panel.
- *Panels & axes (all left y = median time (s, **log**)):*
  (a) F1 depth `d` (linear x) — SAT & UNSAT;
  (b) F2 clocks/obligations `k` (linear x) — SAT & UNSAT;
  (c) F3 max-constant `M` (**log₂** x) — SAT & UNSAT; overlay F4 SIZE `m` (log₂ x) as a
      second, flat reference curve.
- *Companion search-space panel (recommended):* `distinct_zones` vs `k` (F2) on log-y,
  showing the super-polynomial zone growth that F3/F4 lack.
- *Reader concludes:* depth (a) and clock-simultaneity (b) are walls (steep, hit timeouts);
  max-constant M (c) and raw formula size are flat — constants and propositional size are
  *absorbed*, confirming H1's ranking depth ≫ clocks ≫ {M, size}.

**F3 — RQ2: UPPAAL-query scalability (size and bound).**
- *Type:* 2-panel line plot. Left: time vs query size `m` (log₂ x). Right: time vs time-bound
  `b` (log₂ x). Left & right y = median time (s, **log**, same scale as F1/F2 for visual
  comparability). One curve per UPPAAL shape (U1–U4, optionally U5); SAT instances solid,
  matched UNSAT dashed.
- *Reader concludes:* every flat UPPAAL-shaped query stays sub-second/low-seconds and the
  curves are essentially flat in both size and bound — the procedure is practical on the
  queries engineers actually write.

**F4 — Contrast cactus: practical vs adversarial.**
- *Type:* cactus / survival plot (cumulative #instances solved vs per-instance median time,
  log-y), pooling all instances. Two groups: **RQ2 (flat UPPAAL)** vs **RQ1 (adversarial
  nested: F1/F2)**; timeouts shown as the tail hitting the 60 s ceiling.
- *Reader concludes:* in one glance — UPPAAL-shaped queries form a low, flat band orders of
  magnitude below the timeout, while only the nested adversarial families climb to and hit
  the wall. This is the headline practicality claim and the RQ1↔RQ2 contrast.

### Tables (2)

**T1 — RQ1 driver ranking & fitted scaling laws.**
- *Type:* table. *Columns:* Family | factor (x) | verdict (SAT/UNSAT) | param range | fit
  kind (exp / power / flat) | exponent α | R² | max median time (s) | max nodes | max
  distinct_zones | #timeouts. One row per (family × SAT/UNSAT).
- *Fits:* semilog `log t = αd + β` for linear-x families (F1,F2); log–log
  `log t = α log M + β` for log-x families (F3,F4). Reuse `_semilog_fit`/`_loglog_fit`.
- *Reader concludes:* quantifies H1 — F1-UNSAT exponential (α≫0, near-1 slope on log-nodes),
  F2 super-polynomial, F3/F4 ≈ flat (α≈0) — and ranks the drivers numerically.

**T2 — RQ2 practical envelope.**
- *Type:* table. *Columns:* UPPAAL shape | TCTL form | size range `m` | bound range `b` |
  max median time (s) | max nodes | max distinct_zones | max peak_mem_kb | #solved / #total
  | #timeouts.
- *Reader concludes:* the worst-case resource envelope across the entire UPPAAL sweep is
  small and timeout-free — a concrete practicality statement for the paper's claims section.

---

## 5. Protocol: repetitions, timeout, determinism, environment

- **Repetitions / medians.** Search-space metrics (`nodes`, `distinct_zones`, `peak_mem_kb`,
  `max_depth`, `loop_checks`, `memo_hits`) are **deterministic** functions of the formula —
  the tableau is a deterministic DFS over a memoised graph (single thread), so **one run**
  fixes them exactly; record them once and assert equality across reps as a sanity check.
  **Wall-clock** is noisy: run **R = 5 timed repetitions + 1 discarded warm-up** per
  instance, report the **median** `time_s` (also store min and IQR for an error band). The
  existing `BenchmarkOptions` already uses `warmup_runs` and a fixed `seed=1337`; extend
  `bench_run.py` with a `--reps 5` loop that re-invokes the same command and takes the median.
- **Timeout.** Per-instance **60 s** (matches the correctness suite; ANALYSIS shows a clean
  approach to this wall). Use `bench_run.py`'s coreutils-`timeout` wrapper (inner kill) plus
  the Python backstop. Timeouts are **right-censored** at the ceiling: plotted as `×`
  markers, counted in the `#timeouts` columns, and excluded from curve fits.
- **Determinism / fairness.** Single-threaded (`num_threads=1`); pin to one core
  (`taskset -c 0` / Docker `--cpus=1 --cpuset-cpus=0`) and `nice -n -5` to reduce scheduler
  noise; disable turbo/frequency scaling if the host allows. Run the entire suite on **one
  machine** in **one Docker image** (the Ubuntu/x86_64 build, UDBM statically linked).
- **Environment to report (artifact reproducibility).** CPU model + fixed frequency, RAM, OS,
  Docker image digest, `tctl_sat` git commit/build flags, compiler/version, UDBM version,
  R=5, timeout=60 s. Emit a `reproducibility.txt` alongside `results.csv` (the benchmark
  harness already writes one).
- **Pipeline (concrete commands).**
  1. `python3 bench_generate.py --outdir outputs_perf --families-module perf_families`
     → `outputs_perf/manifest.csv` + one `.txt` per instance.
  2. `python3 bench_run.py --outdir outputs_perf --binary /work/Implementation/tctl_sat \
        --solver "docker exec <CID>" --timeout 60 --reps 5` → `outputs_perf/results/results.csv`.
  3. `python3 perf_plot.py --outdir outputs_perf` → Figs F1–F4 (pdf+png), Tables T1–T2 (tex).

- **The answers, restated.**
  - **RQ1 answer** = driver ranking **depth ≫ simultaneous-clocks ≫ {M ≈ size}**, with the
    SAT/UNSAT asymmetry (SAT short-circuits, UNSAT exhausts), the located walls (UNSAT depth
    d≈6; clocks k≈12–15 at 60 s), all quantified in **T1** and shown in **F1/F2**.
  - **RQ2 answer** = the UPPAAL sweep's resource envelope (max time/nodes/mem, zero timeouts)
    in **T2**, and the cactus contrast in **F4**: flat 1-level queries are *practical*, the
    nested adversarial families of RQ1 are the only ones that reach the timeout.

- **Scope note for the paper.** No baseline exists (La Torre–Napoli: no implementation;
  UPPAAL: model checking, not satisfiability). Report all results as a *characterization* of
  this procedure's cost profile and its practicality on UPPAAL-shaped specifications — never
  as a head-to-head comparison.
