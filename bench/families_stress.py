"""Adversarial families: written to make v2 fail, not to make it look good.

Every family here targets a specific way the decomposition, the abstraction or
the acceptance machinery could break down. Where the shape has a verdict that
is forced by construction, it is attached, so a wrong answer is caught and not
merely a slow one.

The families fall into four groups.

*Decomposition should not fire.* ``almost``, ``chain``, ``onevar`` are one
symbol away from decomposing, so the partition runs at every node and answers
no. These measure the tax, and ``onevar`` also checks that data variables
couple their constraints --- grouping by propositions alone made
``{x<=5} & {x>=10}`` satisfiable.

*Decomposition fires but should not help.* ``deepsplit`` buries independence
under a nest, ``recursive`` decomposes into components that decompose again.

*Nothing to do with decomposition.* ``tower``, ``bigM``, ``punct`` and
``manyclocks`` push nesting depth, constant magnitude, punctual intervals and
clock count, the four drivers of the bound.

*Answers that are hard to get right.* ``unsatwin`` is a window-arithmetic family
whose verdict is decided by an inequality, so a soundness slip shows up as a
disagreement with the oracle rather than as a timeout.
"""

from __future__ import annotations

import random
from typing import Iterator, List, Optional

from families import Instance

PER_FAMILY = 220


def _rng(family: str, i: int) -> random.Random:
    return random.Random(f"stress/{family}/{i}")


def _mk(family: str, i: int, formula: str, params: dict,
        expected: Optional[str] = None, witness: Optional[str] = None) -> Instance:
    return Instance(rq="STRESS", family=family, name=f"{family}-{i:03d}",
                    formula=formula, params=params, expected=expected,
                    witness=witness)


# ── 1. almost — k conjuncts that all share one atom ─────────────────────────

def f_almost() -> Iterator[Instance]:
    """The worst case for the split test: it runs at every node and fails.

    k independent-looking eventualities, each conjoined with the *same* atom s,
    so the whole formula is one component. SAT: one run visiting each p_j in
    its window with s held throughout.
    """
    for i in range(PER_FAMILY):
        k = 4 + i % 12
        parts = [f"(EF[{2+j},{4+j}] ((p{j}) & (s)))" for j in range(k)]
        yield _mk("almost", i, " & ".join(parts), {"k": k}, expected="SAT",
                  witness="hold s everywhere, visit p_j inside its window")


# ── 2. chain — components linked in a line ──────────────────────────────────

def f_chain() -> Iterator[Instance]:
    """p0-p1, p1-p2, p2-p3, ...: union-find must collapse the whole chain.

    Every conjunct shares an atom with its neighbour, so the transitive closure
    is one component even though no two non-adjacent conjuncts touch.
    """
    for i in range(PER_FAMILY):
        k = 3 + i % 12
        parts = [f"(EF[{1+j},{3+j}] ((p{j}) | (p{j+1})))" for j in range(k)]
        yield _mk("chain", i, " & ".join(parts), {"k": k}, expected="SAT",
                  witness="each disjunct can be met by its own witness")


# ── 3. onevar — data variables, which the 5000-suite had none of ────────────

def f_onevar() -> Iterator[Instance]:
    """Constraints over one shared variable, half of them contradictory.

    Grouping by propositions alone puts {x>a} and {x<b} in different
    components, each satisfiable on its own; the conjunction is not.
    """
    for i in range(PER_FAMILY):
        rng = _rng("onevar", i)
        lo = rng.randint(0, 20)
        hi = rng.randint(0, 20)
        unsat = lo > hi                      # x >= lo and x <= hi
        extra = f" & (EF[1,3] (p{i % 4}))" if i % 3 else ""
        phi = f"({{x >= {lo}}}) & ({{x <= {hi}}}){extra}"
        yield _mk("onevar", i, phi, {"lo": lo, "hi": hi},
                  expected="UNSAT" if unsat else "SAT",
                  witness="empty interval" if unsat else "pick x in [lo,hi]")


# ── 4. deepsplit — independence buried under a nest ─────────────────────────

def f_deepsplit() -> Iterator[Instance]:
    """The static split cannot see this; only the per-node one can."""
    for i in range(PER_FAMILY):
        d = 1 + i % 4
        k = 3 + i % 8
        inner = " & ".join(f"(EF[{2+j},{4+j}] (p{j}))" for j in range(k))
        phi = inner
        for lvl in range(d):
            phi = f"EF[0,{1+lvl}] ({phi})"
        yield _mk("deepsplit", i, phi, {"depth": d, "k": k}, expected="SAT",
                  witness="delay into the nest, then serve each window")


# ── 5. recursive — components that decompose again ──────────────────────────

def f_recursive() -> Iterator[Instance]:
    """Two groups, each itself a conjunction of independent eventualities."""
    for i in range(PER_FAMILY):
        k = 2 + i % 6
        g1 = " & ".join(f"(EF[{2+j},{4+j}] (a{j}))" for j in range(k))
        g2 = " & ".join(f"(AG (EF[{1+j},{3+j}] (b{j})))" for j in range(k))
        yield _mk("recursive", i, f"({g1}) & ({g2})", {"k": k}, expected="SAT",
                  witness="each conjunct is independently realisable")


# ── 6. tower — nesting depth, the driver decomposition cannot touch ─────────

def f_tower() -> Iterator[Instance]:
    for i in range(PER_FAMILY):
        rng = _rng("tower", i)
        d = 3 + i % 8
        phi = "p"
        for _ in range(d):
            a = rng.randint(0, 2)
            phi = f"AG (EF[{a},{a + rng.randint(1, 3)}] ({phi}))"
        yield _mk("tower", i, phi, {"depth": d}, expected="SAT",
                  witness="p everywhere")


# ── 7. bigM — constant magnitude, which must not drive the search ───────────

def f_bigM() -> Iterator[Instance]:
    """Node counts must stay flat as the constants grow by six orders."""
    for i in range(PER_FAMILY):
        M = 10 ** (1 + i % 6)
        variant = i % 3
        if variant == 0:
            phi = f"AG[0,{2*M}] (E((p) U[{M},{2*M}] (q))) & AG[0,{2*M+1}] (!q)"
            exp = "UNSAT"
        elif variant == 1:
            phi = f"AG[0,{2*M}] (E((p) U[{M},{2*M}] (q))) & AG[0,{M-1}] (!q)"
            exp = "SAT"
        else:
            phi = f"EF[{M},{2*M}] (p) & AG[0,{M-1}] (!p)"
            exp = "SAT"
        yield _mk("bigM", i, phi, {"M": M, "variant": variant}, expected=exp)


# ── 8. punct — punctual intervals, the completeness boundary ────────────────

def f_punct() -> Iterator[Instance]:
    """[a,a] windows. Verdicts are not asserted: this family is where the
    calculus is known not to promise completeness, so it is run to see whether
    it answers at all, and whether the two versions agree."""
    for i in range(PER_FAMILY):
        rng = _rng("punct", i)
        a = rng.randint(1, 6)
        shape = i % 4
        if shape == 0:   phi = f"EF[{a},{a}] (p)"
        elif shape == 1: phi = f"AG (EF[{a},{a}] (p))"
        elif shape == 2: phi = f"(EF[{a},{a}] (p)) & (AG[{a},{a}] (!p))"
        else:            phi = f"(AF[{a},{a}] (p)) & (EF[{a},{a}] (q))"
        yield _mk("punct", i, phi, {"a": a, "shape": shape})


# ── 9. manyclocks — clock count, near the 64-atom bitmask limit ─────────────

def f_manyclocks() -> Iterator[Instance]:
    """Wide conjunctions right up to and past where the atom bitmask gives up.

    Decomposition disables itself above 64 atoms, so the k>64 rows are a check
    that the fallback is the plain search and not a wrong answer.
    """
    for i in range(PER_FAMILY):
        k = [8, 16, 32, 48, 60, 64, 66, 80][i % 8]
        parts = [f"(EF[{2+(j%7)},{5+(j%7)}] (p{j}))" for j in range(k)]
        yield _mk("manyclocks", i, " & ".join(parts), {"k": k}, expected="SAT",
                  witness="independent eventualities, one witness each")


# ── 10. unsatwin — verdict decided by window arithmetic ─────────────────────

def f_unsatwin() -> Iterator[Instance]:
    """AG(EF[a,b] p) & AG[c,d] !p, whose verdict is an inequality.

    UNSAT iff some onset t >= 0 has [t+a, t+b] inside [c,d], i.e.
    d-b >= max(0, c-a). This is the family that caught the onset-shift
    soundness bug, run here at a wider range and with a second obligation
    attached so decomposition has something to consider.
    """
    for i in range(PER_FAMILY):
        rng = _rng("unsatwin", i)
        a = rng.randint(0, 6); b = a + rng.randint(1, 6)
        c = rng.randint(0, 8); d = c + rng.randint(1, 8)
        unsat = (d - b) >= max(0, c - a)
        tail = " & (EF[1,4] (z))" if i % 2 else ""
        phi = f"(AG (EF[{a},{b}] (p))) & (AG[{c},{d}] (!p)){tail}"
        yield _mk("unsatwin", i, phi, {"a": a, "b": b, "c": c, "d": d},
                  expected="UNSAT" if unsat else "SAT",
                  witness="an onset's window sits inside the ban" if unsat
                          else "every window escapes the ban")


FAMILIES = [f_almost, f_chain, f_onevar, f_deepsplit, f_recursive,
            f_tower, f_bigM, f_punct, f_manyclocks, f_unsatwin]


def all_instances() -> List[Instance]:
    out: List[Instance] = []
    for f in FAMILIES:
        out.extend(f())
    return out
