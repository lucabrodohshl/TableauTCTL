# UPPAAL "Check Satisfiability" — translator design (locked decisions)

Companion to `FINDINGS.md`. This pins the **semantics** the translator implements.
Decisions confirmed with the user:

- **Clocks → real-valued** Z3 constraints (sound). The solver gets a
  `--real-vars x,y` flag; those names are Z3 `Real`, data variables stay `Int`.
  *Not* lifted to a `[a,b]` modality (unsound — the model clock ≠ the formula
  clock; a reset before the target makes `E<>(φ & x<=5)` true while `EF[0,5]φ`
  is false). The timed fragment is reached only via an **explicit** bound the
  user writes (`E<>[a,b] φ`), never by auto-lifting a clock predicate.
- **deadlock → reject.** Our witness models are non-blocking *by construction*
  (soundness requires every state to have a non-Zeno run), i.e. deadlock-free.
  So we state: *"by default all of our models are deadlock-free; a query that
  mentions `deadlock` is not considered (yet)."* Such a query is skipped with
  that message — not translated.
- **Satisfiability scope = model-aware when the model is available, else
  pure-logic + warning.** In the plugin the model is always loaded, so we encode
  structural invariants (below). A standalone `.q`-only run, with no model to
  classify identifiers, falls back to treating predicates as free atoms and
  prints a warning that structural contradictions may be missed.

---

## 1. Property-operator mapping (UPPAAL → our syntax)

| UPPAAL | ours |
|---|---|
| `E<> φ` | `EF φ` |
| `A[] φ` | `AG φ` |
| `E[] φ` | `EG φ` |
| `A<> φ` | `AF φ` |
| `φ --> ψ` | `AG(φ -> AF ψ)` |
| `E<>[a,b] φ` (our extension) | `EF[a,b] φ` (likewise A[],E[],A<>) |

Rejected property forms (skipped with a message): `sup{}/inf{}`, `Pr[...]`,
`simulate`, `E[...]` (expected value), `strategy`/`control:`/Stratego.

## 2. State-predicate mapping

| UPPAAL | ours |
|---|---|
| `&&` / `and` | `&` |
| `\|\|` / `or` | `\|` |
| `!` / `not` | `!` |
| `imply` | `->` |
| `==` | `=` |
| `!=` | `!( = )` |
| `<= < >= >` | same |
| `+ - *` | same |
| `true` / `false` | `true` / `false` |

Rejected predicate forms (skip with message): `deadlock`; `forall`/`exists`;
function calls `f(...)`; non-constant array indices `a[i]`. Constant array
indices `a[3]` are flattened to a named atom/var.

## 3. Identifier classification (needs the model)

For each leaf identifier we decide what it is, using the parsed model:

- `Inst.Loc` where `Inst` is a **process instance** and `Loc` is a location of
  its template → **location predicate** → boolean atom `Inst_Loc`.
- `Inst.v` where `v` is a variable of that template → **typed variable**
  (`Inst_v`), Int or Real per its declaration (`clock` ⇒ Real).
- bare `v` → global variable (Int/Real/bool) or `const` (inlined).
- A name we cannot classify (no model) → opaque boolean atom + warning.

Dotted names are renamed `Inst.Loc → Inst_Loc` because our atoms are
`[A-Za-z_][A-Za-z0-9_]*` (no dots). The **instance prefix is preserved**, so the
same location name in two templates stays distinct (`t0_idle` ≠ `t1_idle`).

## 4. Structural invariants — the location handling (NOT superficial)

When the model is present we conjoin, globally, the facts every UPPAAL run obeys:
`translated_query  ∧  AG( Inv )`, where `Inv` is the conjunction of:

### 4a. Exactly-one-location — **per process instance, not per template**

The constraint "a process occupies exactly one location" is **per instance**.
Critical subtleties:

1. **Group by instance, never by template.** If `Train` is instantiated as
   `t0`,`t1`, then `t0.Cross` and `t1.Cross` are *different* atoms over
   *different* processes — both may hold at once. Exactly-one ranges over the
   locations of *one* instance: `ExactlyOne(t0.A, t0.B, …)` and separately
   `ExactlyOne(t1.A, …)`. Lumping all `*.Cross` together would be wrong.
2. **Read the `system`/instantiation line** to enumerate instances. Handle:
   `p = T(args); system p, …;` (named instance); `system T;` (one anonymous
   instance named `T`); partial application. **Process arrays**
   (`T(const id : int[0,N]); system T;` ⇒ `T(0..N)`) are enumerated when `N`
   is a constant; otherwise the instance set is unbounded → **warn** and fall
   back to per-mentioned-atom treatment (no exactly-one for that template).
3. **Minimal completion with `_other`.** We do not enumerate every location of
   an instance — only those the query mentions, plus one fresh sentinel
   `Inst_other` standing for "in some location not named in the query":
   `ExactlyOne(Inst_L1, …, Inst_Lk, Inst_other)`.
   - *Totality*: the process is always in one of {named} ∪ {other}. ✓
   - *Exclusion*: at most one holds. ✓
   This is sound and minimal: e.g. `AG(P.A) ∧ EF(P.B)` becomes UNSAT (always in
   A ⇒ never in B), while `AG(P.A | P.B)` stays SAT — your "OR is fine" point:
   exactly-one *permits* the disjunction, it only forbids the *conjunction*
   `P.A & P.B`.
4. `ExactlyOne(a1,…,an)` is emitted as
   `(a1 | … | an) & AND_{i<j} !(ai & aj)`.
5. Holds at **every** state (discrete edges are atomic; no state has a process
   "between" two locations), so wrapping in `AG[0,inf)` is correct.

### 4b. Variable range bounds

For each Int variable `int[lo,hi] v` referenced: `lo <= v & v <= hi`, under `AG`.
Bounded `bool` ⇒ `{0,1}` is implicit (boolean atom). `const` folded to its value.

### 4c. Clock non-negativity

For each clock `x` referenced: `x >= 0`, under `AG` (and `x` is Real, §clocks).

> Soundness note: every conjunct of `Inv` is true in *all* UPPAAL systems, so
> conjoining it never turns a genuinely-satisfiable query UNSAT — it only rules
> out the structurally impossible. That is exactly "satisfiable by a real UPPAAL
> system."

## 5. Output of the translator

Given `(model?, query)` it returns one of:
- **REJECTED** + reason (deadlock / unsupported form), or
- **OK**: `{ formula : <tctl_sat string>, real_vars : [clocks…], warnings : […] }`.

The driver runs `tctl_sat [--real-vars …] --stats [--model]` on `formula` and
maps `SATISFIABLE/UNSATISFIABLE`. On SAT, `--model` yields a UPPAAL `.xml`
witness (`TimedAutomaton::to_uppaal_xml`) for the "Save witness" action.
