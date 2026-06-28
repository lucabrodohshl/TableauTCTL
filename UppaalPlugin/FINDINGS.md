# UPPAAL "Check Satisfiability" plugin — feasibility findings

Pre-build investigation. Two questions: (1) can we extend the UPPAAL UI, and
(2) what UPPAAL query syntax must we support / abstract to drive our `tctl_sat`
solver. Answers below, with sources.

---

## Q1 — Can we extend the UPPAAL UI?  **YES.**

UPPAAL ships an official **Java Plugin API**. A plugin is a jar dropped into
`$UPPAAL_ROOT/plugins/` and appears as an **integrated tab** inside the GUI,
with programmatic access to the current model and traces. This is exactly the
hook we need: a *"Satisfiability"* tab with a **Check Satisfiability** button.

Evidence / precedent:
- Official docs list a Java API for "model editor, simulator and verifier
  interface"; `libs/model.jar` (create/load/save/simulate models, check
  properties), javadoc in `libs/model-javadoc.jar`, example in
  `demo/ModelDemo.java`. Plugins go in `$UPPAAL_ROOT/plugins/`.
- **UrPal** (utwente-fmt/UrPal, "UPPAAL Sanity Checker") is a *working* plugin
  with essentially our shape: it adds sanity checks over the model. Built with
  Gradle, deployed via `./gradlew deployLocal` → `$UPPAAL_ROOT/plugins/`,
  launched via `./gradlew runUppaal`. **This is the template to copy.**

Requirements / caveats:
- **Java 8** (UrPal notes Xtend/compat issues on newer JDKs), **Gradle**,
  **UPPAAL ≥ 4.1.22**.
- GUI granularity is a **tab/panel**, not (documented as) injecting a button
  into the native Verifier toolbar. A "Satisfiability" tab listing the model's
  queries each with a Check button is the realistic, proven form.
- The plugin API is thinly documented — rely on `model-javadoc.jar`,
  `demo/ModelDemo.java`, and the UrPal source as references.
- Our solver is a native C++ binary (`tctl_sat`, + Z3). The plugin (JVM) calls
  it as a subprocess (or via JNI/socket). Cleanest: bundle `tctl_sat` and shell
  out, parse its `SATISFIABLE/UNSATISFIABLE` + `Stats:` lines (same contract the
  benchmark harness already uses).
- Alternative integration if the plugin tab proves too constraining: a
  **standalone companion** that reads the `.xml` model + `.q` queries (documented
  file formats) and runs `tctl_sat` — no GUI, but zero dependence on the plugin API.

---

## Q2 — What must we support? (UPPAAL query → our solver)

### What `tctl_sat` already accepts (authoritative, from `src/lexer.cpp`,
`include/tctl/ast.hpp`, `examples/tctl_examples.txt`)

- **Propositional atoms** `[A-Za-z_][A-Za-z0-9_]*` (no dots).
- **Boolean**: `! & | -> <->`, `true/false`.
- **Temporal (untimed)**: `EF AF EG AG`, `E(.U.) A(.U.) E(.R.) A(.R.)`.
- **Temporal (timed, non-punctual)**: `EF[a,b] AF[a,b] EG[a,b] AG[a,b]`,
  `E(.U[a,b].)` etc.; intervals `[a,b] (a,b) [a,inf)`, `a<b`. **No next** (EX/AX
  rejected — matches UPPAAL, which also has no next).
- **Integer/data arithmetic as state predicates**: variables, `+ - *`,
  comparisons `<= < >= > =` — and these are **semantically reasoned** by a **Z3
  backend** (`z3_solver.cpp`): a node's conjunction of predicates is checked for
  arithmetic consistency. So `temp>0 & temp<0` is detected UNSAT, not treated as
  two opaque atoms. (Example in the suite: `AG[2,20] (temp > 0 & temp < 100)`.)

This is more than "abstract propositions" — discrete data-variable reasoning is
already there. The gap to UPPAAL is therefore mostly a **translator** plus a few
genuine semantic decisions.

### Mapping table

| UPPAAL query construct | our solver | status |
|---|---|---|
| `E<> φ` (reachability) | `EF φ` | ✅ |
| `A[] φ` (safety) | `AG φ` | ✅ |
| `E[] φ` | `EG φ` | ✅ |
| `A<> φ` (liveness) | `AF φ` | ✅ |
| `φ --> ψ` (leads-to) | `AG(φ -> AF ψ)` | ✅ |
| `&&  \|\|  !  imply  not` | `&  \|  !  ->` | ✅ syntactic remap |
| `P.Location` (process in location) | fresh atom `P_Location` | ✅ (dots not allowed → rename) |
| data-var compare `i==3`, `c>0`, `i+j<=k` | IntVar arithmetic (Z3) | ✅ (`==`→`=`, `!=`→`!(·=·)`) |
| **clock constraint** `x<=5`, `x-y<3` | — | ⚠️ **decision needed** (see below) |
| `deadlock` | — | ❌ structural; reject/warn |
| `sup{}/inf{}`, `Pr[…]`, `simulate`, `E[…]` (value / SMC / strategy) | — | ❌ out of scope (not boolean) |
| `forall (i:T) φ`, `exists (i:T) φ` over bounded ranges | finite ∧ / ∨ expansion | ⚠️ expand |
| arrays `a[i]`, function calls in predicates | const-index flatten / reject | ⚠️ |
| time-bounded operators | (classic UPPAAL CTL has none) | our timed power is **extra**; emit `[0,inf)` by default |

### The three real decisions (not just syntax)

1. **Clocks are continuous; our `IntVar` is discrete.** Encoding a clock `x` as
   a Z3 *integer* is **unsound**: `4 < x & x < 5` is SAT for a real clock but
   UNSAT over integers. Options, in order of preference:
   - give clock variables a **real sort** in Z3 (small change to `z3_solver`),
     keeping data variables integer — soundest;
   - or **abstract each clock atom** to a fresh proposition (loses arithmetic);
   - or lift clock bounds into the **timed `[a,b]` modality** where they belong.
   We must classify each variable as clock vs int (the model's declarations tell
   us which — the plugin can read them).

2. **Location mutual-exclusion / variable bounds (model invariants).** Pure
   query satisfiability over fresh atoms is *weaker* than UPPAAL semantics:
   `P.A & P.B` is UNSAT in any real model (a process is in exactly one location)
   but SAT for independent atoms. To make the check meaningful we should assert
   the structural invariants the plugin can harvest from the model:
   - **at-most-one / exactly-one** among a template's location atoms;
   - **range bounds** for declared `int[lo,hi] v` → `lo <= v <= hi`.
   Z3 already handles these once added. This is the difference between "is this
   formula satisfiable in the abstract" and "is this query satisfiable by some
   UPPAAL system" — worth deciding explicitly with the user.

3. **What "satisfiable" should mean for the user.** For UPPAAL-shaped queries
   (mostly untimed CTL over predicates) a single query is often trivially SAT
   unless (1)–(2) are encoded. The valuable defects we can catch are: arithmetic
   contradictions on data vars (✅ Z3 today), clock-timing contradictions
   (needs decision 1), and contradictions against model invariants (decision 2).

### Translator scope (the concrete deliverable)

A `query → tctl_sat` front-end that:
- parses the UPPAAL property language (operators above) + state predicates;
- reads the model declarations to classify identifiers (location / int / clock)
  and to emit invariant constraints (1)–(2);
- rewrites operators/connectives and renames dotted names to legal atoms;
- rejects with a clear message the unsupported forms (`deadlock`, SMC/value/
  strategy, unbounded quantifiers, function calls);
- pretty-prints our syntax and shells out to `tctl_sat --stats`, surfacing
  SAT / UNSAT (+ a witness model on SAT, which our solver already returns).

---

## Sources
- UPPAAL Tools & API — https://docs.uppaal.org/toolsandapi/
- UPPAAL Java API — https://docs.uppaal.org/toolsandapi/javaapi/
- UrPal (UPPAAL Sanity Checker plugin) — https://github.com/utwente-fmt/UrPal
- juppaal (Java API for UPPAAL model files) — https://github.com/ksluckow/juppaal
