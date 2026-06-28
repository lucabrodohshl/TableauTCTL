# Performance evaluation — TCTL satisfiability tableau

Design: `scripts/PERF_EVAL_PLAN.md`. Implementation: `scripts/perf_families.py`, `scripts/perf_plot.py`
(reusing `bench_generate.py --families-module perf_families` and `bench_run.py --reps 5`).
Sweep: **237 instances**, fixed solver (nested-modality bug fixed), Docker/x86_64, single-thread, 60 s
timeout, median-of-5 wall-clock (search-space metrics deterministic — `det_metric_mismatches=0`).
Result: **0 verdict mismatches** (after correcting the `U4_unsat` killer band to `2b`), 18 timeouts (all on
the adversarial families, by design). Framed as a **characterization**, not a comparison (no baseline:
La Torre–Napoli unimplemented, UPPAAL does model-checking not satisfiability). Figures `F1–F4`, tables
`T1–T2` in `scripts/outputs_perf_container/{plots,tables}`.

## RQ1 — Which input parameters drive cost?

**Answer: depth ≫ clocks ≫ size ≫ M.** Fitted scaling laws (Table T1; Fig F2):

| factor | family | fit | exponent α (R²) | max time | max nodes | timeouts |
|--------|--------|-----|-----------------|----------|-----------|----------|
| nesting depth (UNSAT) | DEPTH | **exponential** | **0.48** (0.99) | 31.7 s | 7 638 | 5 |
| nesting depth (SAT) | DEPTH | flat | 0.05 (0.98) | 0.36 s | 131 | 0 |
| simultaneous clocks | OBL | **exponential** | 0.22–0.25 (≈0.98) | 48.8 s | 8 244 | 13 |
| max-constant M (≤8192) | MAXCONST | **flat** | ≈0.00 (≈0) | 0.32 s | 45 | 0 |
| formula size m (≤128) | SIZE | mild power | 0.55 (0.94) | 1.53 s | **9** | 0 |

- **Nesting depth of the timed double-check is the dominant driver**, and it is where the **SAT/UNSAT
  asymmetry** lives: UNSAT blows up exponentially (the optimal `ExpTime` procedure must exhaust the AND–OR
  graph to certify unsatisfiability — `nodes` 60→7 638), while SAT stays flat (an early witness
  short-circuits the search). This is Fig F2(a) and the clearest single result.
- **Simultaneously-active clocks are the secondary wall** — exponential in `k`, and Fig F2(d) shows the
  mechanism directly: `distinct_zones` grows from ~10 to ~8 000 over `k=1..12` (the DBM-dimension /
  `M^{O(K²)}` handle).
- **Max-constant M is absorbed** — essentially flat out to `M=8192` (45 nodes), confirming that zones and
  `≅_M` extrapolation represent large bounds symbolically rather than enumerating the timeline.
- **Raw propositional size is benign** — time grows only mildly and the realised search is trivial
  (**max 9 nodes**): the on-the-fly memoised construction does not materialise the Fischer–Ladner closure.

## RQ2 — Is it practical on UPPAAL-style queries?

**Answer: yes — every flat 1-level query class is fast and timeout-free.** (Table T2; Figs F3, F4.)

| UPPAAL query | TCTL | max time | max nodes | timeouts |
|--------------|------|----------|-----------|----------|
| reachability `E<>` | `EF_[0,b]` | 0.82 s | 257 | 0 |
| safety `A[]` | `AG_[0,b]` | 0.84 s | 261 | 0 |
| bounded liveness `A<>` | `AF_[1,b]` | 2.27 s | 517 | 0 |
| leads-to `p-->q` | `AG(p→AF_[1,b]q)` | 2.03 s | 444 | 0 |
| `E[]` | `EG` | 0.83 s | 7 | 0 |

Across the whole UPPAAL sweep (size `m≤128`, bound `b≤8192`, SAT and matched UNSAT): **146 solved, 0
timeouts, ≤2.3 s, ≤517 nodes**, and curves essentially flat in both size and bound (bounds absorbed by
zones, size by memoisation). Fig F4 contrasts this directly with the adversarial nested families (38 solved,
18 timeouts, climbing to the 60 s wall): **the queries engineers actually write sit orders of magnitude
below the timeout; only the adversarial nested specifications reach it.**

## Takeaways for the paper

- The empirical cost profile matches the `2^{O(n log n)}·M^{O(n²)}` bound term by term: the branching of the
  *nested* check (depth) and the DBM dimension (simultaneous clocks) are the walls; the constant magnitude M
  and raw size are not.
- The SAT/UNSAT asymmetry is a clean, citable result: refutation is exponential, witness-finding is cheap.
- On UPPAAL-shaped specifications the procedure is practical (sub-2.3 s, no timeouts), which is the case that
  matters for adoption.
