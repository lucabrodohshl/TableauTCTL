# The optional optimisations (v2), and one that graduated to v1

`--version v1` is the plain search. `--version v2` adds the optimisations below. All of them are
**verdict-preserving**: the two versions decide the same language and differ only in how much of the
graph they build. The gate on every one of them is the self-test, 1050/1050, run both ways.

Per-feature environment overrides exist so a single optimisation can be isolated for a measurement
without rebuilding: `TCTL_COMPONENTS`, `TCTL_SUBSUME_GOALS`, `TCTL_AG_CONTEXT`,
`TCTL_ONSET_CLOCK`, `TCTL_ONSET_SHIFTS`, `TCTL_M2_UNRESET`, `TCTL_ROLLED_DEADLINE`.

## Why any of this is needed: where the cost actually is

Measured on `AG(EF[1,3](AG(EF[4,6](AG(EF[7,9] p)))))`, the largest case in the suite:

- **92% of the nodes (64 627 of 70 271) sit in a single strongly connected component.** Every `AG`
  loops, so from any combination of clock-cells and pursuit stages you can reach any other, and the
  reachable space is one mutually-reachable blob.
- Consequently the on-the-fly pruning decides only **3.5%** of nodes; the other 96.5% wait for that
  component to close. `settles` can only fire when a child finishes while its parent is still on the
  stack, and in a cyclic graph the child's subtree contains a back-edge to the parent.
- Of the surviving nodes, **69 744 of 70 271 are genuinely distinct** in (Γ, pursuits, inv, zone).
  There are 29 distinct Γ and 189 pursuit-sets against **12 085 distinct zones**.

So the graph is *zone variety*, the zone count is `M^O(k^2)` in the number of clocks `k`, and no
amount of search-order cleverness touches it. That is the lens for everything below: an optimisation
is worth having if it removes clocks, removes cells, or removes whole independent subproblems.

## 1. Component decomposition

A node's goals, context and pursuits often fall into groups mentioning **disjoint atoms**. Two such
groups have disjoint formula-clocks as well, since a clock belongs to the modality that owns it.

*Soundness.* A node over the union of two atom-disjoint groups is realisable exactly when each group
is. (→) project the model onto one group's atoms, which the other group's formulas never mention.
(←) take the product of the two models: delays synchronise, discrete edges interleave, and the
labellings union without conflict because the atom sets are disjoint. So the verdict of the whole is
the conjunction of the verdicts of the parts, and each part is decided by its own sub-search whose
results are memoised in a shared cache.

*Why it pays.* It replaces a **product** of state spaces by their **sum**. A conjunction of `k`
independent bounded eventualities has `2^k` combinations of which are still outstanding, and the
undecomposed search visits all of them.

*Measured.*

| formula | v1 | v2 |
|---|---|---|
| `AG(EF[1,3] p) & AG(EF[2,5] q) & AG(EF[3,7] r)` | 30 991 | **268** |
| `AG(EF p) & AG(EF q) & AG(EF r)` | 891 | **104** |
| `EF[1,4]p & EF[2,6]q & EF[3,8]r & EF[4,9]s & EF[5,10]t` | 519 | **264** |

## 2. Goal subsumption

Drop a goal that another goal in the same Γ already implies: a disjunction one of whose disjuncts is
present, and the body of a release whose window opens at 0 (the release asserts its body here).

*Soundness.* Γ and Γ minus an implied goal have the same models, so they are realisable together.
Purely a key-shrinker: fewer distinct Γ, hence fewer nodes.

*Measured.* Nearly flat on the current suite — the formulas carry little redundancy. Kept because it
costs one linear scan and pays on redundant input.

## 3. The AG-context encoding — a v2-shaped optimisation, kept in v1

An untimed `AG ψ` is `A(⊥ R_[0,∞) ψ)`. As a pursuit it is pure overhead: `⊥` never releases it, the
window never closes, `(Rlapse)` can never fire, and `(Runf)` takes the same branch for ever. It is a
pursuit only because releases are handled uniformly, and it costs one live pursuit **per nesting
level** — on a tower of `AG(EF ...)` the pursuit vector ranges over the product of a per-level state
that has exactly one reachable value. In the measurement above, **61 334 of 70 271 nodes carried six
live pursuits, three of which were these stateless `AG`s**.

Its fixpoint law is `AG ψ ≡ ψ ∧ AX AG ψ`, and the calculus already carries "holds at every discrete
successor" in the context `Ctx`. So `(Cov)` puts `ψ` in `Γ` and the modality in `Ctx`, and creates no
pursuit at all.

### The soundness gap, and the fix

This is where it nearly went wrong, and the argument is worth writing down.

`(Delay)`'s `Γ'` re-imposes *"the body of every release **pursuit** in Γ∪Ctx whose window the child's
zone meets"*. Under this encoding the `AG` is **not a pursuit**, so that clause does not cover it.
One might hope its body survives anyway as a non-literal of `Γ` — it does not: `(Cov)` fires on the
body if the body is itself a modality, and **removes it from `Γ`** on both children. So a delay child
was getting no obligation from the `AG` at all, and the per-cell onsets it is supposed to raise
simply vanished.

The symptom was a 10x node collapse (70 271 → 6 686) — dropping obligations always looks like a
brilliant optimisation until you check what it dropped.

The fix is one clause in `make_delay_child`: re-impose the body of every **release modality carried
in `Ctx`**, on the same "window meets the child's zone" condition as for pursuits. `Ctx` itself
already travels to delay children on `d.X`, so the modality persists; what was missing was the
per-cell assertion of its body.

*Soundness, after the fix.* The two encodings are step-for-step equivalent:

| pursuit encoding | context encoding |
|---|---|
| `(Rstop)` asserts `φ₁ = ⊥` → child closes | no such child |
| `(Rgo)` asserts `Θ = {ψ}` at the node | `(Cov)` asserts `ψ` at the node |
| `(Rgo)` defers `μ•` to `Ctx` (universal → AX) | `(Cov)` puts `μ` in `Ctx` |
| `(Delay)` re-imposes the pursuit's body per cell | the new clause re-imposes the modality's body per cell |
| `(Rlapse)` unreachable (window `[0,∞)`) | no lapse to model |

Every position of the model is therefore labelled `ψ` under both, and the obligation reaches every
discrete successor under both. What differs is only that the context encoding stores no per-level
pursuit state — which is exactly the state that had one reachable value.

*Verification.* 1050/1050 in both encodings; plus 20 hand-built adversarial formulas aimed at the
gap (witnesses that must fall strictly inside a cell, `AG p & EF(0,1) !p` and kin) and an
onset-sensitive family (`AG(EF[1,2] p) & AG[2,3] !p` and kin, where a single doomed onset at an
integer point decides the verdict) — identical verdicts throughout.

It is kept **on in v1** because after the fix it is a strict improvement in the shapes it applies to
and never worse elsewhere.

## Where to look next

The measurements say the remaining cost is one giant SCC of zone-distinct nodes. These are the
techniques that attack that, roughly in order of how much I would expect from them here.

1. **Abstraction refinement over clocks (CEGAR).** The single most promising. Start with a coarse
   abstraction — fewer clocks, or coarser cells than the `clock_bounds_` cut points — and refine only
   where a spurious witness appears. This is the only idea that attacks `M^O(k^2)` at its root rather
   than shaving constants, and the engine already has the two ingredients: a per-clock cut-point set
   that can be *started small*, and a witness extractor to test a candidate against.
   Care: the onset-shift experiment showed cut points are also a **canonicaliser** — removing them
   wholesale cost 2.6x (70 271 → 185 362 nodes) because zones from different branches stopped
   coinciding. So refinement must add cuts back per clock, not globally.
2. **Antichain representation of the marking** (De Wulf–Doyen–Henzinger–Raskin). The fixpoint over a
   64 627-node component is computed over explicit sets. Since realisability is monotone under
   narrowing (§4.1), the marking is downward-closed in the zone order and could be stored by its
   maximal elements. This is the standard fix for exactly this shape of fixpoint and would attack the
   96.5% bulk directly.
3. **Conflict-driven learning.** When a branch closes, record *why* — the minimal literal pair or the
   deadline that emptied the zone — and reuse it to close sibling branches without expanding them.
   Tableaux for modal logics do this as "lemma caching"; the analogue of a CDCL learned clause.
   The node table is already the place to hang it.
4. **Sharing the `Ful` fixpoint across untils.** `query_until` recomputes a backward reachability per
   modality per SCC. On the giant component that is `|mus|` passes over 64 627 nodes. Speeds the
   fixpoint; does not reduce node count.

Explicitly *not* worth it, each measured:

- **Zone subsumption in the node table** — disjoint cells, essentially never fires, and zones are
  stored packed so each test would cost an unpack.
- **Goal/pursuit subsumption at equal zone.** This looked like the big one and it is worth writing
  down why it is not, because the headline number is seductive: **26 971 of 68 624 nodes are
  strictly dominated** by another node with the same zone, invariant and pursuits and a superset of
  goals (more obligations = harder, so the dominator's acceptance implies the dominated one's).
  Three ways to exploit it were measured, and all three fail:

  1. *A memo consulted at intern time.* Needs the dominator already **decided**; only **536 of the
     26 971 (2%)** were, by the time the dominated node was created. Same cause as the 3.5% prune
     rate — in one 64 627-node SCC nothing is decided until the component closes. Fires on 0.8%.
  2. *Sibling domination*, which needs no verdicts at all: in an AND a weaker child is implied by a
     harder one and can be dropped, in an OR the harder alternative is redundant. Measured: **0 of
     67 401 expansions** contain a dominating sibling pair. Siblings always differ in zone —
     `(Delay)` parts are disjoint cells — or in the pursuit set.
  3. *Anything at all*, once you look at what the pairs are. Every one of the 26 971 differs in
     **Γ only**, and the extra goals are pending modality demands. That is the signature of the
     `(Cov)` **discharge** relation: the harder node still has `μ` to cover, the weaker one has
     already discharged it. Sampling 4 000 pairs, the weaker node is reachable from the harder one
     in ≤6 steps in **89%** of cases and is a *direct child* in 30%. So the implication
     "harder ⟹ weaker" is not new information — it is already an AND-edge of the graph. And being
     an AND-edge is precisely what makes it unexploitable: the harder node *requires* the weaker one
     as a child, so the weaker one cannot be pruned away.

  The 38% is an artefact of the conjunctive fan-out, not an opportunity.
- **Conflict-driven learning, on this shape** — F1 has only 631 closed nodes out of 68 624. There is
  almost nothing to learn from; the formula is satisfiable and hardly any branch closes locally.
- **Search-order heuristics / reordering children** — pruning fires on 3.5% and cannot fire more, for
  the structural reason above.
- **Extra_LU in place of Extra_M** — coarser, but tuned to preserve reachability, an existential
  property, whereas realisability of a node is universal over its zone.
- **Hash compaction** (storing a 128-bit fingerprint instead of the key) — would cut memory further
  but makes the procedure probabilistic. Wrong trade for a decision procedure backing a paper.

## Related

- `docs/Y_CLOCK_ELIMINATION.md` — removing the second clock per universal modality, the other
  clock-count win.
