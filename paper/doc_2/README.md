# doc_2 — component decomposition for the TCTL tableau

This folder explains **why the TCTL satisfiability search blows up, which part of
the blow-up is avoidable, and how the avoidable part is removed**. It is not a
paper — it is the document a paper gets written *from*: every claim is traced to
the source that implements it or to the measurement that produced it, the one
theorem that is genuinely ours is stated and proved, and the ideas that were
tried and failed are recorded with the reason.

```sh
make          # -> main.pdf
make watch    # rebuild on save
make clean
```

## Layout

One file per section, in reading order.

```
main.tex               document skeleton; \input order = reading order
preamble.tex           packages, monochrome TikZ styles, theorem envs, macros
Makefile

sections/
  00-how-to-read.tex   the two audiences; code-to-mechanism trace table
  01-problem.tex       the two blow-up regimes, separated by measurement
  02-theory.tex        THE THEOREM: decomposition, and its proof
  03-algorithm.tex     the per-node test, its three side conditions, the memo
  04-evaluation.tex    measured numbers, and what they do and do not show
  05-negative.tex      what was tried and did not work, and why
  06-limits.tex        boundaries and threats to validity
```

## The one-sentence version

A node's goals often fall into groups that mention disjoint atoms; such groups
have disjoint formula-clocks, a node over their union is realisable exactly when
each group is, and deciding them separately replaces a product of state spaces
by a sum — measured, $2^{18}$ nodes become $1249$.

## What is new here

| | |
|---|---|
| **New** | Theorem 1 (decomposition), including that no zone-product condition is needed; the clock-ownership side condition; the per-node test; the measurement separating the discrete from the zone regime |
| **Ported** | The idea of component caching, from #SAT/DPLL (Bacchus–Dalmao–Pitassi; Sang et al.) |
| **Engineering** | atom bitmasks, the no-split shape memo, the shared component cache |

## Status

Both forms ship in **v2**, which is the default search. The baseline is one flag
away:

```sh
./build/tctl_sat --version v1 input.txt   # pre-decomposition baseline
./build/tctl_sat --version v2 input.txt   # default
```

Environment variables remain as per-feature overrides, so one optimisation can
be isolated for a measurement without rebuilding:

```sh
TCTL_DECOMPOSE=1      # static: split the root conjunction once
TCTL_COMPONENTS=1     # dynamic: re-partition the residual at every node
TCTL_SUBSUME_GOALS=1  # drop goals implied by other goals
```

v1 and v2 agree on all 5000 suite instances and both pass 861/861 self-test
checks. v1 is a slower search, not a wrong one: the onset split points are a
soundness fix and are in both.
