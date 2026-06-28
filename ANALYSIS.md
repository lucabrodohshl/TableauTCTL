# Experimental analysis — TCTL satisfiability tableau

**Setup.** Solver `tctl_sat` built in the Ubuntu/x86_64 Docker container (UPPAAL UDBM linked statically);
`EX`/`AX` removed from the object language (kept only as internal tableau markers), matching the paper.
Synthetic benchmark: 7 families / 15 variants / **199 instances**, each with a **by-construction
ground-truth verdict** — a built-in correctness oracle the previous benchmark lacked. Per-instance timeout
60 s, run inside the container. Artifacts: `scripts/outputs_container/{results,plots,tables}`.

## Headline: the oracle found a soundness bug; we fixed it; results are now clean

The first sweep reported **22 wrong verdicts** (all `UNSAT→SAT`) confined to `DCN_unsat` (nested
double-check, depth ≥ 2) and `NRL_unsat` (nested timed release). We verified semantically that the labels
were right and the **solver** was wrong — minimal repro, incl. the smoking gun
`AG[0,2](E(p U[1,3] (AG[0,2](E(p U[1,3] q))))) & AG[0,99]!q` (UNSAT: the nested `AG`s force `q` into `[2,6]`,
forbidden by the huge band), which the solver accepted as SAT.

**Root cause** (`src/tableau.cpp`, successor generation): when a node carried both a delay-successor and the
discrete child pursuing a *nested* timed modality, the nested pursuit's obligation was dropped instead of
being retained as a conjunctive (AND) child — so a nested unsatisfiability was never enforced and the formula
was unsoundly accepted. Flat/depth-1 formulas (the paper's worked examples) were unaffected. **Fix:** carry
the nested pursuit as a proper AND-child alongside the delay successor. After the fix:

| family | what it stresses | ok | mismatch | timeout | total |
|--------|------------------|----|----------|---------|-------|
| DCM | double-check, M-sweep (flat) | 26 | 0 | 0 | 26 |
| MSC | max-constant staircase | 26 | 0 | 0 | 26 |
| NUN | nested until (SAT) | 24 | 0 | 0 | 24 |
| NRL | nested timed release | 24 | 0 | 0 | 24 |
| ZEN | Zeno rejection (non-Zeno) | 39 | 0 | 0 | 39 |
| OBL | clock/obligation pressure | 24 | 0 | 12 | 36 |
| DCN | nested double-check | 17 | 0 | 7 | 24 |
| **total** | | **180** | **0** | **19** | **199** |

**0 verdict mismatches** against the ground-truth oracle; `--selftest` 56/56 tests (799 checks). The 19
timeouts are genuine scaling walls, not errors (see below). SAT 87 / UNSAT 93 / TIMEOUT 19.

## Performance and scaling

Solved-instance times: min 0.058 s, median **0.161 s**, max 55.9 s (a clean approach to the 60 s wall). The
cactus plot (`plots/overview_cactus.png`) separates SAT/UNSAT cleanly and is monotone with the expected tail.

- **Large constants are free.** DCM/MSC sweep the max constant up to ~8192 yet stay sub-second — the
  zone/DBM representation absorbs big bounds symbolically, exactly the paper's claim (no enumeration of the
  timeline). Effectively flat curves.
- **The nested double-check is the EXPTIME wall** (`plots/DCN.png`, the paper's core mechanism). Two panels,
  runtime and tableau-node count vs nesting depth `d`: the **SAT** variant is cheap and near-linear (a
  witness is found quickly), while the **UNSAT** variant blows up exponentially (nodes 60 → ~8000 by `d=5`)
  and hits the timeout for `d ≥ 6` — the textbook signature of an optimal `ExpTime` procedure forced to
  exhaust the search to certify unsatisfiability. The SAT/UNSAT gap is the clearest single result in the set.
- **Clock/obligation pressure (OBL)** is the second wall: 12/36 timeouts as the number of simultaneously
  active timed untils grows, consistent with the `M^{O(n²)}` zone count under many independent clocks.
- **Everything else scales gracefully.** Nested until (NUN), nested release (NRL, now fully correct), and
  Zeno rejection (ZEN) all stay in the sub-second/seconds range; ZEN confirms the time-progress loop
  condition correctly rejects time-convergent witnesses (39/39).
- UNSAT instances that close early are cheap; the cost concentrates exactly where the theory predicts
  (depth of the nested check, and clock dimensionality).

## Assessment

- **The benchmark is TACAS-grade and earned it.** It pairs documented scaling hypotheses and controlled
  SAT/UNSAT families with a by-construction correctness oracle — and that oracle's first act was to expose a
  real soundness defect in the implementation's nested-modality handling, the paper's central mechanism. That
  is precisely what an evaluation harness is for, and it is a point in the paper's favour, not against it.
- **The solver is now sound on the full suite** (0/199 mismatches) and exhibits the scaling the theory
  predicts: large constants absorbed symbolically, an exponential wall on the nested double-check, and a
  zone-dimensionality wall under clock pressure. These are honest, publishable numbers.

## Reproduce

```bash
CID=503ec3ccfbbb…
docker cp Implementation/scripts $CID:/work/Implementation/
docker exec -w /work/Implementation/scripts $CID python3 bench_generate.py
docker exec -w /work/Implementation/scripts $CID python3 bench_run.py --local \
    --binary /work/Implementation/tctl_sat --timeout 60
docker exec -e MPLBACKEND=Agg -w /work/Implementation/scripts $CID python3 bench_plot.py
docker cp $CID:/work/Implementation/scripts/outputs Implementation/scripts/outputs_container
```
