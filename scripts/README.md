# Synthetic TCTL satisfiability benchmark

A clean, hypothesis-driven, verdict-controlled benchmark for the TCTL
satisfiability **tableau** (`tctl_sat`). It is designed to (i) stress the
algorithm's distinctive *double-check* mechanism, (ii) cover what a TACAS
reviewer expects (depth, constants, clocks, nesting, Zeno), and (iii) double as
a **correctness oracle**: every instance ships with a ground-truth verdict
fixed by construction, so the runner flags any disagreement.

Three small, decoupled tools:

| step | script | reads | writes |
|------|--------|-------|--------|
| generate | `bench_generate.py` | `bench_families.py` | `outputs/formulas/**`, `outputs/manifest.csv` |
| run | `bench_run.py` | `manifest.csv` + solver | `outputs/results/results.csv` |
| plot | `bench_plot.py` | `results.csv` | `outputs/plots/**`, `outputs/tables/**` |

`bench_families.py` is the single source of truth for the generator: family
definitions, generators, hypotheses, and a structural grammar self-check.

---

## Why this beats the previous (C++) benchmark

The old `--benchmark` families (A–I in `src/benchmark.cpp`) had three recurring
weaknesses, admitted in `benchmark_name_rationale.txt`:

* **No verdict control / no oracle** — runtime was recorded but the answer was
  never checked, so a regression that flips SAT↔UNSAT would pass silently.
* **Flat / non-monotone curves** — several M-sweeps had *identical*
  `nodes_generated` across all M (the code even prints a `FLAT ... WARNING`),
  because zone abstraction neutralised the parameter.
* **Diffuse hypotheses** — many families measured "something" without a single
  scaling axis or a stated, falsifiable expectation, and none specifically
  isolated the paper's *double-check* construct.

This benchmark fixes all three: one scaling axis per family, a documented
falsifiable hypothesis, a **matched SAT/UNSAT pair** whose verdict is decided by
construction (and re-checked by the runner: `verdict_match` column +
`verdict_validation.tex`), parameter ranges chosen so curves are monotone with
the hardest instances approaching the timeout, and a flagship family built
directly on `AG[0,b]( E(p U[l,u] q) )`.

---

## Families and hypotheses

Each family scales **one** parameter and (almost always) provides a SAT and an
UNSAT variant. Verdicts are fixed by construction; see `bench_families.py` for
the exact generators and the per-variant `hypothesis` strings.

| code | name | x-axis | variants (verdict) | stresses |
|------|------|--------|--------------------|----------|
| **DCN** | Double-Check, nested | nesting depth `d` | SAT, UNSAT | (a) the double check |
| **DCM** | Double-Check, constant sweep | `M` (log) | SAT, UNSAT | (a)+(b) |
| **MSC** | Max-constant staircase | `M` (log) | SAT, UNSAT | (b) large bounds |
| **OBL** | Obligation / clock pressure | conjuncts `k` | SAT, UNSAT | (c) many timed untils |
| **NUN** | Until nesting | nesting depth `d` | SAT, UNSAT | (d) until nesting |
| **NRL** | Release nesting | nesting depth `d` | SAT, UNSAT | (d) release nesting |
| **ZEN** | Zeno rejection | `M` | SAT, UNSAT×2 | (e) time-progress test |

### (a) The double check — DCN / DCM (flagship)

The distinctive construct is a **universal re-evaluation of a timed
existential-until**: `AG[0,b]( E(p U[l,u] q) )`. At every time point of a
universal band the solver must re-open and discharge an existential timed-until
obligation.

* **DCN** nests it `d` deep — `Layer(i) = AG[0,2]( E(p U[1,3] Layer(i-1)) )`,
  `Layer(0)=q`. The SAT variant is the bare nest (the `p,q`-invariant model
  satisfies every layer). The UNSAT variant conjoins `AG[0,d*3+1] !q`: a witness
  must place `q` at an absolute time in `[d, 3d]`, which is now globally
  forbidden, so the root obligation can never be discharged. **Hypothesis:**
  search size grows super-linearly with `d`; UNSAT refutation costs more than the
  SAT side.

* **DCM** keeps depth 1 but sweeps the constant magnitude — base
  `AG[0,2M]( E(p U[M,2M] q) )`. The verdict is flipped by **one constant**, the
  killer band `c` in `AG[0,c] !q`:
  * `c = M-1 < L` ⇒ the window `[M,2M]` is reachable ⇒ **SAT**;
  * `c = 2M+1 ≥ U` ⇒ the inner window `[M,2M]` is a **subset of the forbidden
    band `[0,c]`** ⇒ **UNSAT**.
  This is the textbook "window ⊆ forbidden band" UNSAT condition the paper cares
  about, isolated as a minimal pair.

### (b) Max-constant `M` — MSC

A fixed-depth (`D=3`) forced-delay staircase of `[M-1,M]` windows:
`E(true U[M-1,M] E(true U[M-1,M] E(true U[M-1,M] p)))`. A witness must elapse to
`~D*(M-1)..D*M`, forcing fine zone distinctions up to `~D*M`, which resists
constant-abstraction collapse. **SAT** = bare staircase; **UNSAT** = staircase
`& AG[0,D*M+1] !p` (the deadline is contradicted only after exploring the
bound). **Hypothesis:** runtime grows with `M`; if the solver's abstraction is
fully constant-insensitive the SAT curve flattens — a result worth reporting
either way.

### (c) Clock / obligation pressure — OBL

`k` independent existential timed-untils over fresh atoms with staggered windows
`[i,i+2]` ⇒ `k` simultaneously-live clocks (DBM dimension `k+1`, per-step zone
work `Θ(k²)`). **SAT** = the conjunction (each obligation schedulable
independently); **UNSAT** = same plus `AG[0,k+2]( !q1 & … & !qk )` forbidding
every target, so all `k` obligations must be individually refuted.
**Hypothesis:** polynomial growth in `k`, driven by zone dimension.

### (d) Until / release nesting — NUN / NRL

* **NUN** — `d` nested `E(true U[1,3] …)` (pure least-fixpoint). SAT = bare nest;
  UNSAT = `& AG[0,3d+1] !p`.
* **NRL** — `d` nested `E(false R[1,3] …)` (pure greatest-fixpoint; `E(false R …)`
  forces the target to hold throughout the band, exercising loop **acceptance**).
  SAT nests around `p`; UNSAT nests around `false` so the innermost
  `E(false R[1,3] false)` is impossible and the contradiction must be unwound
  through all `d` levels.

### (e) Zeno rejection — ZEN

Formulas whose only naive witnesses are **time-convergent**, forcing the
time-progress / anti-Zeno loop test:

* `EG p & AG[1,M] !p` — **UNSAT** (only a Zeno run could satisfy both).
* `AG[1,M] false` — **UNSAT** (vacuous only if time never enters `[1,M]`).
* `EG p & AF[1,M] q` — **SAT** control: a genuine divergent witness exists, so
  the same loop machinery must *accept* it.

---

## End-to-end commands

From `Implementation/scripts/`. Default output root is `scripts/outputs/`
(git-ignored).

### 1. Generate

```bash
python3 bench_generate.py            # full benchmark (199 instances)
python3 bench_generate.py --quick    # tiny smoke set
python3 bench_generate.py --only DCN,DCM   # selected families
```

Also run the standalone grammar self-check any time (no solver needed):

```bash
python3 bench_families.py            # prints a sample per variant, validates all
```

### 2. Run the solver

The solver command is fully configurable. The full per-instance command is:

```
<--solver tokens> [timeout -k 5 <T>] <--binary> <--stats-flag> <input file>
```

**Docker build** (the Linux binary is rebuilt in a container by another agent):

```bash
python3 bench_run.py \
    --solver "docker exec <CONTAINER_ID>" \
    --binary /work/Implementation/tctl_sat \
    --path-to /work/Implementation \
    --timeout 60
```

`--path-to` rewrites the host formula path to its in-container mount
(`--path-from` defaults to this repo's `Implementation/` dir, i.e. the formula
files written under `scripts/outputs/...` are seen at
`/work/Implementation/scripts/outputs/...`). A coreutils `timeout` is inserted
*inside* the container so the inner process is actually killed; a Python-level
hard kill (`--timeout + --grace`) is always applied as a backstop.

**Local binary** (e.g. a native build on this machine):

```bash
python3 bench_run.py --binary ../tctl_sat --local --timeout 60
```

Useful flags: `--only DCN,ZEN`, `--limit 10` (smoke), `--dry-run` (print the
commands without running), `--no-inner-timeout`, `--stats-flag --stats`.

> **Note on flags.** The solver's statistics flag is `--stats` (this is the
> default of `--stats-flag`); the engine prints
> `Stats: nodes=… open=… closed=… max_depth=… memo_hits=… loop_checks=…
> distinct_zones=… peak_mem_kb=… avg_mem_per_node=…`, and the verdict line is
> `<n>: SATISFIABLE|UNSATISFIABLE|TIMEOUT`. The file-input mode has **no**
> internal timeout, so the per-instance timeout is enforced by the runner.

### 3. Plot + tabulate

```bash
python3 bench_plot.py
```

Produces, under `outputs/`:

* `plots/{pdf,png}/<FAMILY>.{pdf,png}` — per-family two-panel curves (runtime +
  search size vs the scaling parameter), SAT vs UNSAT coloured, timeouts marked,
  log axes where appropriate, with fitted scaling laws.
* `plots/{pdf,png}/overview_cactus.{pdf,png}` — cactus/survival plot.
* `tables/family_summary.tex`, `tables/scaling_laws.tex`,
  `tables/verdict_validation.tex` (+ `scaling_laws.csv`).

---

## Results schema (`results.csv`)

Tidy, one row per instance:

```
instance_id, family, family_label, variant, variant_label,
param_name, param, log_x, x_label, mechanism,
expected_verdict, verdict, verdict_match,
time_s, timeout_s, max_constant, formula_len,
nodes, nodes_open, nodes_closed, max_depth, memo_hits, loop_checks,
distinct_zones, peak_mem_kb, avg_mem_per_node,
returncode, solver_cmd, formula
```

`verdict` ∈ {SAT, UNSAT, TIMEOUT, ERROR}; `verdict_match` ∈
{yes, no, timeout, error}. A correct tableau yields **zero** `verdict_match=no`
rows — this is the built-in correctness oracle.

## Requirements

`python3` with `pandas`, `numpy`, `matplotlib` (and optionally `scipy` for
regressions; a NumPy fallback is used otherwise). The generator and the runner
need only the standard library.
