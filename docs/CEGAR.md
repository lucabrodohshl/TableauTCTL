# CEGAR over the onset-shift cut points (v2)

Implemented, sound, and **off by default** — `TCTL_CEGAR=1` enables it under `--version v2`.
It is off because it is measured to be a net loss on the current benchmark mix; the implementation
is kept because the abstraction is correct and the machinery is the place a better abstraction would
plug in.

## The one axis that is safe to coarsen

Coarsening cells in general is unsafe in *both* directions at once:

- fewer cut points means a zone can straddle a window endpoint, so the entailment tests
  (`Z |= x in I`) start failing where they should hold — stops become unavailable and the search
  answers **UNSAT wrongly**;
- fewer cut points also stops isolating *doomed onsets*, so a demand that no run can meet is never
  seen — the search answers **SAT wrongly**.

Refining only the **onset shifts** avoids the first. Every clock keeps its *own* window endpoints as
cut points (`collect_clock_bounds`), so a zone still lies wholly inside or wholly outside any window
on that clock and every entailment stays exact. The shifts (`add_onset_shifts`) contribute nothing
but onset isolation. So dropping them is a one-way approximation:

> **abstract UNSAT ⟹ concrete UNSAT.** Only doomed-onset isolation is lost, and losing it can
> only turn an UNSAT into a SAT, never the reverse.

Which gives the loop:

1. run with the coarse cut points (no shifts);
2. **UNSAT** → answer UNSAT, it is genuine;
3. **SAT** → possibly spurious; refine by re-running with the shifts, which is exactly the v1 search
   and therefore correct.

Worst case is two runs, the second being the full engine, so the verdict is always the v1 verdict.
Witness extraction skips the loop — the abstraction would describe an automaton for the coarse cut
points. Verified: **1050/1050 under `--version v2` with CEGAR on.**

The abstraction is *budgeted* (`TCTL_CEGAR_CAP`, default 4000 nodes). Without a cap the coarse run
can be dearer than the full one, because the shifts are also a **canonicaliser** — they align cells
so that zones reached by different branches coincide and their nodes merge. On the nested-E family
the uncapped abstraction cost 251 032 nodes against 68 624 for the full search. The cap bounds the
whole downside to the cap.

## Why it does not pay

| formula | v2, no CEGAR | v2 + CEGAR |
|---|---|---|
| `AG(EF[3,4] p) & AG[4,5] !p` — UNSAT | 515 | **283** |
| `AG(EG[2,4] p) & AG[6,7] !p` — UNSAT | 670 | **316** |
| `AG(EF[2,4] p) & AG[4,7] !p` — UNSAT | 945 | **518** |
| `AG(EF[1,2] p) & AG[2,3] !p` — UNSAT | 412 | **276** |
| `AG(EF[1,3](AG(EF[4,6](AG(EF[7,9] p)))))` — SAT | 68 624 | 72 625 |
| `AG[0,10](AF[1,2] q) & AG>=13 !q` — SAT | 3 143 | 6 782 |
| `AG[0,5](AF[1,2] q) & AG>=8 !q` — SAT | 1 483 | 2 882 |
| **total** | **77 210** | 85 100 |

Tuning the cap does not rescue it — the total is a loss at every setting, on a mix that is already
60% unsatisfiable:

| cap | 400 | 800 | 1200 | 4000 | off |
|---|---|---|---|---|---|
| total nodes | 78 493 | 79 265 | 80 865 | 85 100 | **77 210** |

The reason is a ratio, not a bug. The abstraction is only about **twice** as cheap on the
unsatisfiable instances it decides, while costing a **whole extra search** on every satisfiable one.
For a two-phase CEGAR to pay, the abstraction has to be one or two *orders* cheaper. Here it cannot
be, because the same cut points that coarsen the search are the ones that canonicalise it: taking
them away gives back much of what the coarsening saves.

## What would make it pay

- **An abstraction that drops clocks rather than cut points.** Clocks are the exponential axis
  (`M^O(k^2)`), so removing one is a quadratic-in-the-exponent cut rather than a linear one. The
  difficulty is direction: freeing a clock *enlarges* zones, and realisability is universal over the
  zone, so the abstraction becomes *harder* — it answers UNSAT, which is the useless direction. An
  abstraction that is both cheaper and one-way on clocks is the open problem.
- **Incremental refinement.** This implementation restarts with the full shift set. Proper CEGAR
  would read the spurious witness, identify the modality pair whose shift it violates, and add only
  that one. That makes each iteration cheaper but not the first one, and the measurement above says
  the first one is already too expensive relative to the full search.
