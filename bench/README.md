# TCTL satisfiability benchmark

Reproducible performance and completeness evaluation for the tableau decision
procedure. One command regenerates every figure and table the paper uses.

```bash
cmake --build build -j8            # build the solver first
python3 bench/bench.py all --solver build/tctl_sat
```

## Layout

| file | role |
|---|---|
| `families.py` | declarative instance families — what to run, and why each expected verdict holds |
| `runner.py`   | executes instances, parses verdicts/stats, writes `results/results.jsonl` |
| `analyze.py`  | reads the JSONL, writes LaTeX tables and PDF figures |
| `bench.py`    | CLI entry point (`list` / `run` / `analyze` / `all`) |

Generation, execution and analysis are separate so a finished run can be
re-analysed without re-running the solver, and so families can be reviewed as
data rather than as code paths.

## Research questions

**RQ1 — cost drivers.** Vary one structural parameter of the complexity bound
`2^{O(n)} · M^{O(n²)}` at a time: timed-nesting depth, simultaneously live
formula-clocks, the largest integer constant `M`, and propositional size. Depth
and clock count unavoidably co-vary the other two, so the flat `M`- and
size-families act as controls. Each family carries a SAT and an UNSAT variant,
separating witness cost from refutation cost.

**RQ2 — practicality.** The five canonical UPPAAL query shapes (reachability,
safety, bounded liveness, leads-to, `E[]`) as one-level TCTL, swept over query
size and time bound independently.

**RQ3 — the completeness gap.** The procedure is sound and terminating on all of
TCTL, complete over the non-punctual fragment, and complete even with punctual
intervals at nesting depth one. An UNSATISFIABLE verdict on a formula that *is*
satisfiable is therefore the one observable form of incompleteness, and
measuring it needs an oracle independent of the tool.

Three families provide one:

- `rq3_completeness` — negation-free formulas satisfied by the witness
  `W` (one location, every atom true, no invariant, one self-loop). Time
  diverges in `W` and every atom holds everywhere, so `W` satisfies every such
  formula whatever the intervals.
- `rq3_pinned` — the same shapes conjoined with a safety constraint that
  forbids the atom until the nested windows close, so the *only* models are
  those placing the atom exactly where the windows pin it. This is the shape the
  incompleteness argument is about: a persistent context re-demanding a punctual
  modality at a continuum of onsets, with one formula-clock serving them all.
- `rq3_controls` — UNSAT by construction. A zero incompleteness rate is
  meaningless unless the same pipeline detects a genuine miss; these must all
  come back UNSATISFIABLE.

Because the procedure is sound, any disagreement is classified automatically:
expected SAT + got UNSAT is an incompleteness instance, expected UNSAT + got SAT
would be a soundness violation (reported separately and loudly).

### RQ3 by search, not by hand

Three hand-written families only probe the shapes someone thought of. `oracle.py`
and `rq3_search.py` instead *search* for a miss.

`oracle.py` fixes a concrete witness structure and evaluates TCTL on it exactly.
A `Witness` is one location with a self-loop and divergent time, each atom true
on a period-`P` set of times; since the location and labelling never change,
every run carries the same atom trace, the path quantifiers collapse, and TCTL
becomes a metric logic over the timeline. Truth sets are then finite unions of
rational intervals and every operator is exact interval arithmetic --- `EF_[a,b]`
maps an interval `(lo,hi)` to `(lo-b, hi-a)`, `AG` is its dual, and the unbounded
cases are settled by periodicity. `BranchWitness` adds a second location behind a
nondeterministic switch, so that `E` and `A` genuinely differ (`EF` unions over
the two branches, `AG` intersects); it supports `EF`/`AG` only, because `EG`/`AF`
at the branching location quantify over the switch time in a way that is neither,
and approximating them would void the guarantee.

`rq3_search.py` then generates random shapes, keeps only those a witness
*provably* satisfies, and asks the solver. `--hard` discards anything the
all-true structure already satisfies (those discharge every obligation the
instant it is raised, so the punctual machinery never runs) and keeps only
formulas with a punctual window at modal depth >= 2 --- the region the
completeness argument implicates.

    python3 bench/rq3_search.py --hard      --samples 60000 --max-depth 6
    python3 bench/rq3_search.py --branching --hard --samples 40000

**What this can and cannot show.** The oracle certifies satisfiability by
exhibiting a model, and every model it can exhibit is finitely representable (a
periodic structure over at most two locations). The punctuality caveat, though,
is about formulas whose *only* models are not finitely representable: the
obligations a model carries then depend on the exact offsets of unboundedly many
pending onsets. No oracle of this kind can produce such a formula, so the search
cannot exhibit that gap however long it runs. What it does establish is that
within the class of models the procedure is designed to find, none is being
missed --- and, since the identical pipeline detects misses when pointed at a
deliberately weakened acceptance test, that this is a measurement and not a
vacuous pass.

## Outputs

`results/results.jsonl` — one self-describing record per run (verdict, median
and minimum time, tableau nodes, distinct zones, peak memory, and whether the
solver emitted its own completeness warning).

Figures and tables are written straight into the paper tree:
`../../TCTLSAT_revisited/figs/` and `.../tables/`.

## Notes

- Timing is the median of `--repeats` runs; `--timeout` bounds each instance.
- `nodes` and `distinct_zones` are deterministic and machine-independent, so
  they are the primary scaling evidence; wall-clock is reported alongside.
- `TCTL_LEGACY_LOOP=1` in the environment selects the older path-local loop
  acceptance instead of SCC acceptance, for A/B comparison.
