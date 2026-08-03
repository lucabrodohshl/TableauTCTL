# Eliminating the onset clock `y_mu`

Status: design + implementation notes. Ablation flag `TCTL_ONSET_CLOCK=1` restores the old
two-clock encoding for measurement.

## Why

Clocks are the only exponential axis the engine has. By Lemma 1(iii) the graph is
`2^O(n) * M^O(k^2)` in the number of clocks `k`, and the DBM is `(k+1)^2`. The redesign gives every
universal modality a *second* clock, so `k` goes from `n` to as much as `2n` — the zone count is
squared in the exponent, and every zone is a bigger matrix.

Measurement is what forced the issue. On the largest case in the suite,
`AG(EF[1,3](AG(EF[4,6](AG(EF[7,9] p)))))`:

- 70 271 nodes, of which **69 744 differ in (Γ, pursuits, inv, zone)** — nothing artificial is
  splitting them;
- only **29 distinct Γ** and 189 distinct pursuit-sets against **12 085 distinct zones**.

The graph *is* zone variety, and zone variety is clocks. Every other lever was measured and found
flat or negative: on-the-fly pruning decides only 3.5% of nodes (96.5% go through full SCC
evaluation, because every `AG` loops and a child's subtree always contains a back-edge to its
parent, so `settles` cannot fire); zone subsumption cannot fire because `(Delay)` partitions into
*disjoint* cells; coarsening the cells by dropping the onset shifts is a 2.6x **loss**, since those
cut points are a canonicaliser that makes zones from different branches coincide. Halving `k` is
the only lever that attacks the 96.5% bulk rather than the 3.5% fringe.

## The argument

`y_mu` is a *derived* quantity, not an independent one.

Because a `(Delay)` child re-imposes the demands of its cell, `y_mu = 0` at every node where the
feeding context still demands `mu`. It only starts accumulating once the demands cease. But
"the demands ceased" is already measured, by the feeding context's own clock: a release `sigma`
whose body demands `mu` stops demanding when `x_sigma` passes `sup I_sigma`, and from that moment

```
y_mu  =  x_sigma - sup I_sigma
```

So every guard that reads `y_mu` can be rewritten over clocks that already exist. Writing
`b_sigma = sup I_sigma`, and `F(mu)` for the set of releases whose body contains `mu` — a purely
syntactic set, computable once from the formula:

| reads `y_mu` | becomes |
|---|---|
| (Ustopdrop) `y_mu >= a and y_mu > 0` | `x_sigma >= b_sigma + a` for every `sigma` in `F(mu)` |
| persistent (Rlapse) `y_mu > b` | `x_sigma > b_sigma + b` for every `sigma` in `F(mu)` |

An unbounded `sigma` never ceases demanding, so the conjunction is unsatisfiable and the pursuit
never drops — exactly the behaviour of the two-clock version. The conjunction over `F(mu)` is the
right reading: the recurrence may end only once *every* context that feeds it has stopped.

`(Abs)` then resets nothing at all; it only rewrites the marker to `mu*`. That is a second,
independent win: every `y`-reset was creating a zone distinction between nodes that no guard could
afterwards tell apart.

I had rejected this formulation earlier as inelegant, because of the conjunction over several
contexts. The numbers invert that judgement: a static conjunction over clocks that already exist is
free, whereas a clock dimension is exponential.

## Proof side

Nothing breaks. The onsets a pursuit still owes an answer to become

```
Ons(mu*, nu)  =  [ max(0, x_sigma - b_sigma),  x_mu + a )
```

and the situation clauses read through unchanged, `y_mu` having only ever appeared through the two
guards above.

## Implementation notes

1. `F(mu)` is built once at setup: walk the formula, and for every release `sigma` add `sigma` to
   `F(mu)` for every modality `mu` occurring in `sigma`'s body (`children[1]`).
2. The two guards become one predicate over `F(mu)`, entailment-tested on the zone exactly as the
   `y_mu` versions were (`Z |= ...`, never a narrowing).
3. **`x_sigma` has to outlive `sigma`'s own pursuit.** `(Rlapse)` drops the pursuit and frees its
   clocks, but the cessation test still needs to read `x_sigma` afterwards — that is the whole
   point, since cessation is what it measures. So a release clock is kept live, and not freed on
   stop or lapse, while any live *persistent* pursuit it feeds is still around. Without this,
   `AG[0,5](AF[1,2] q) & AG>=8 (!q)` regresses to UNSAT: the recurrence can no longer be shown to
   have ended.
4. `ymap_` is then empty and `nc_ = 1 + |cmap_|`.

## Measured effect

Suite 1050/1050 with the clock gone, and 1050/1050 again under `TCTL_ONSET_CLOCK=1`, so the two
encodings are verdict-equivalent on everything tested.

Clock dimension, on `AG[0,5](AF[1,2] q) & AG>=8 (!q)` as reported by the extracted witness:

| | clocks |
|---|---|
| with `y_mu` | 7 |
| without | **4** |

Nodes, v1:

| formula | with `y_mu` | without |
|---|---|---|
| `AG(AF[2,4] q) & AG(q -> AG(0,1] !q)` | 9 617 | **2 674** |
| `AG[0,10](AF[1,2] q) & AG>=13 (!q)` | 3 173 | 3 143 |
| 10-formula bench, total | 88 082 | **81 112** |

The win lands exactly where the argument says it should — on universal-heavy formulas, where the
second clock existed. `AG(EF...(AG(EF...)))` is unchanged at 70 271, because its releases are
unbounded: they never cease demanding, their `y` was never live, and there was nothing to remove.

## What it cost to get right

Three things had to follow the clock, each caught by the suite (`drop_family` is the family that
exercises a recurrence *ending*, so it is the one that fails when any of them is missing):

1. `x_sigma` must not be freed by `free_pursuit_clocks` when `(Rlapse)` drops sigma's own pursuit —
   that fires at precisely the instant the clock starts carrying the information the guard wants.
2. Nor by `collapse_dead_clocks`, which frees any clock no *pursuit* reads. A feeding release's
   clock is read by the guard, not by a pursuit. (48 checks.)
3. `sup I_sigma + inf I_mu` and `sup I_sigma + sup I_mu` must be **cut points of `x_sigma`**, and
   `x_sigma` must be an **active clock** so `(Delay)` actually splits there. Otherwise the zone
   spans a range straddling the threshold, no cell entails the test, and the guard silently never
   fires. (5 checks — and this is the subtle one: the guard is not wrong, it is unreachable.)

## Related

- `not_track/PAPER_PORT.md` — the port this sits on top of.
- The suite is the gate: 1050/1050 before and after, and the families that exercise the recurrence
  ending (`drop_family`, `rate_family`, `onsets_persistent_context`) are the ones to watch.
