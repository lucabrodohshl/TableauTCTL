# tctl_sat — a tableau decision procedure for TCTL satisfiability

Decides satisfiability of Timed Computation Tree Logic: given a TCTL formula, is
there a timed automaton that satisfies it?

The search is an **on-the-fly**, zone-based proof search. It builds an AND–OR
graph of symbolic nodes only as far as the search demands, expands each node at
most once, retires a strongly connected component the moment it closes, and
stops at the first witness — so it explores only the relevant part of the
symbolic state space, never the whole graph. Clock valuations are kept
symbolically as zones, and Zeno witnesses are excluded explicitly.

Implements the calculus of L. Brodo, G. Scalora and S. Henkler, *A Tableau for
TCTL*.

**Guarantees.** Sound and terminating for all of TCTL. Complete over the
non-punctual fragment, and — by the depth-one corollary — complete even with
punctual intervals `[a,a]` when no timed modality is nested inside another. A
punctual interval at nesting depth greater than one is accepted and produces a
warning: `SATISFIABLE` remains reliable there (a witness exists),
`UNSATISFIABLE` may be a false negative.

## Building

Requires a C++20 compiler, CMake ≥ 3.20, [Z3](https://github.com/Z3Prover/z3),
and `git`.

```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j
```

That is the whole process. The zone layer,
[HDBM](https://github.com/horaverify/HDBM), is header-only and **cloned
automatically** on the first configure if `HDBM/` is not already present;
nothing else is fetched or compiled. Z3 is the one external library and is
expected from the system: Homebrew on macOS (`brew install z3`), the distro
package on Linux (`apt install z3 libz3-dev`).

`make` is a thin wrapper over the same commands (`make`, `make test`,
`make clean`).

To pin or relocate the zone layer:

```bash
cmake -S . -B build -DHDBM_DIR=/path/to/HDBM          # use an existing checkout
cmake -S . -B build -DHDBM_TAG=v1.2                   # clone a specific tag
```

## Usage

```bash
./build/tctl_sat 'AG[0,2] p'          # a formula given directly
./build/tctl_sat formulas.txt         # a file, one formula per line
./build/tctl_sat --selftest           # the built-in semantic test suite
```

Each formula is answered with `SATISFIABLE`, `UNSATISFIABLE` or `TIMEOUT`.

| option | meaning |
|---|---|
| `--stats` | print the engine's node count for each formula |
| `--model` | extract a witness automaton and write `witness_<n>.{dot,json,xml}` |
| `--tot`, `--all` | conjoin every input formula and decide the conjunction |
| `--real-vars a,b` | treat the named arithmetic variables as reals rather than integers |
| `--output <dir>` | directory for extracted models |
| `--selftest` | run the semantic test suite (60 tests, 829 checks) |
| `--benchmark` | the legacy in-binary benchmark; see *Benchmarking* below |
| `--help` | full option list |

In an input file, blank lines and everything after `#` are ignored.

### Witness automata

A `SATISFIABLE` verdict claims a model exists; `--model` hands it over.

```bash
./build/tctl_sat --model 'EF[1,2] p'
#   1: SATISFIABLE
#   Witness: 5 locations, 6 transitions, 2 clocks
#   wrote witness_1.{dot,json,xml}
```

The automaton is read off the successful marking (paper Theorem 2): locations
are the marked nodes labelled by the atoms they assert, invariants are the
deadlines a universal until registers, transitions are the retained discrete
successors guarded by the target's zone, and a formula-clock is reset exactly
where its modality is launched. Delay contributes no transition — time advances
within a location.

Each automaton is validated before it is written: non-blocking, no location
asserting both a proposition and its negation, guards reading only declared
clocks. Failures are reported as `[INVALID]` with the reason.

Extraction is a property of the SCC acceptance engine, which is the default, so
it works out of the box. It is the *legacy* engine that cannot do it:
`TCTL_LEGACY_LOOP=1` returns a bare verdict and never builds a marking, so there
is nothing to read an automaton off.

### Environment flags

| variable | effect |
|---|---|
| `TCTL_DEBUG=1` | trace every node the search expands, to stderr |
| `TCTL_LEGACY_LOOP=1` | use the earlier path-local loop acceptance instead of SCC acceptance |

`TCTL_LEGACY_LOOP` exists for A/B comparison only. That acceptance test decides
one back-edge at a time, so it rejects a node that sits on a Zeno loop but
reaches an accepting one by another route; it fails two cases of the test suite
that the default engine decides correctly.

## Syntax

Atoms are identifiers (`p`, `q`, `p1`); `true` and `false` are constants.

- Boolean: `!` `&` `|` `->` `<->`
- Untimed: `EF` `AF` `EG` `AG`, `E(φ U ψ)`, `A(φ U ψ)`, `E(φ R ψ)`, `A(φ R ψ)`
- Timed: the same with an interval, e.g. `EF[1,5] p`, `E(p U[2,inf) q)`,
  `A(p R(0,3] q)`
- Intervals: `[a,b]`, `(a,b)`, `[a,b)`, `(a,b]`, `[a,inf)`. Punctual `[a,a]` is
  allowed; empty intervals are rejected.
- Arithmetic leaves in braces: `{x <= 5} & {x > 10}` — discharged by Z3

There is **no next operator**: TCTL has none, and `EX`/`AX` are rejected by the
parser. They exist only as internal proof-theoretic markers.

See `examples/tctl_examples.txt` for a tour of the accepted syntax, and
`docs/manual/` for a typeset user manual (`latexmk -pdf main.tex`) covering the
grammar, the options, worked examples and the witness format.

## Testing

```bash
./build/tctl_sat --selftest
```

60 tests, 829 checks. The suite includes the worked examples of the paper's
Fig. 1 as a permanent oracle, punctual-boundary discriminators, and regression
cases for loop acceptance.

The expected verdicts in `src/test.cpp` are **not** a trusted oracle: each is
justified from TCTL semantics (does a witness automaton exist?), not from what
the engine happens to answer.

## Benchmarking

The evaluation harness lives in `bench/` and is separate from the solver:

```bash
python3 bench/bench.py all --solver build/tctl_sat
```

It covers three research questions — which structural parameters drive the cost,
whether the procedure is practical on UPPAAL-shaped queries, and what the
completeness gap actually costs — and writes figures and LaTeX tables. Instance
families, the runner and the analysis are separate modules so a finished run can
be re-analysed without re-running the solver. See `bench/README.md`.

`--benchmark` inside the binary is an older, self-contained harness that writes
CSVs; `bench/` supersedes it.

## Layout

| path | contents |
|---|---|
| `src/`, `include/tctl/` | the solver: lexer, parser, normalisation, zones, satisfaction sets, tableau |
| `HDBM/` | zone layer (DBMs, federations, minimal-graph storage); cloned automatically |
| `bench/` | evaluation harness and its independent satisfiability oracle |
| `docs/manual/` | typeset user manual (LaTeX) |
| `docs/api/` | generated API reference with UML diagrams (`doxygen Doxyfile`) |
| `examples/` | sample formula files |
| `UppaalPlugin/` | UPPAAL query translator and plugin |

The engine core is `src/tableau.cpp`: node model, the cover rule against the
satisfaction set `S_X(μ)`, the pursuit rules, the delay/EX successor rules, and
the SCC-based acceptance test.
