"""Ten structural families, 500 instances each, for the 5000-formula sweep.

Each family fixes one *shape* and draws its parameters from a seeded RNG, so
the sweep covers a spread of window placements, depths and widths rather than
one curve per family.  Instances are deterministic: family name + index seed
the generator, so a run can be reproduced or resumed.

Expected verdicts are attached only where they are airtight by construction
(window-containment arguments spelled out at each site); everything else runs
unlabelled and contributes timing data alone.
"""

from __future__ import annotations

import random
from typing import Iterator, List, Optional

from families import Instance, af, ag, ar, conj, ef, eg, eu, iv

PER_FAMILY = 500

# Atoms the lexer accepts.
ATOMS = ["p", "q", "r"]


def _rng(family: str, i: int) -> random.Random:
    return random.Random(f"{family}/{i}")


def _window(rng: random.Random, lo_max: int = 5, len_max: int = 5):
    """A non-punctual bounded window [a,b] with small constants."""
    a = rng.randint(0, lo_max)
    b = a + rng.randint(1, len_max)
    return a, b


def _mk(family: str, i: int, formula: str, params: dict,
        expected: Optional[str] = None, witness: Optional[str] = None) -> Instance:
    return Instance(rq="STRUCT", family=family, name=f"{family}-{i:03d}",
                    formula=formula, params=params, expected=expected,
                    witness=witness)


# ── 1. unest — nested existential untils ────────────────────────────────────

def f_unest() -> Iterator[Instance]:
    """E(a U E(a U ... z)) with a fresh window per layer.

    Always SAT: a single run that satisfies every left-hand atom and reaches
    each witness inside its window realises the nest, and the windows never
    conflict because each layer restarts its clock at the layer's onset.
    """
    for i in range(PER_FAMILY):
        rng = _rng("unest", i)
        d = 1 + i % 8
        phi = "r"
        for k in range(d):
            a, b = _window(rng)
            phi = eu(ATOMS[k % 2], phi, a, b)
        yield _mk("unest", i, phi, {"depth": d}, expected="SAT",
                  witness="stack the witnesses left to right; windows are "
                          "measured from their own onsets and never conflict")


# ── 2. anest — nested universal untils ──────────────────────────────────────

def f_anest() -> Iterator[Instance]:
    """A(true U A(true U ... p)) — universal nesting, SAT by p-everywhere."""
    for i in range(PER_FAMILY):
        rng = _rng("anest", i)
        d = 1 + i % 8
        phi = "p"
        for _ in range(d):
            a, b = _window(rng)
            phi = f"A((true) U{iv(a, b)} ({phi}))"
        yield _mk("anest", i, phi, {"depth": d}, expected="SAT",
                  witness="the one-location model with p always satisfies "
                          "every layer at every position of its window")


# ── 3. persist — re-demanded eventuality against a ban ──────────────────────

def f_persist() -> Iterator[Instance]:
    """AG(EF[a,b] p) & AG[c,d] !p.

    UNSAT iff some onset's window [t+a, t+b] fits inside the ban, i.e.
    exists t >= 0 with c <= t+a and t+b <= d, i.e. d-b >= max(0, c-a).
    Otherwise every window keeps a point outside the ban and placing p on
    those points yields a model.
    """
    for i in range(PER_FAMILY):
        rng = _rng("persist", i)
        a, b = _window(rng, lo_max=4, len_max=4)
        c = rng.randint(0, 6)
        d = c + rng.randint(1, 6)
        unsat = (d - b) >= max(0, c - a)
        phi = conj([ag(ef("p", a, b)), ag("!p", c, d)])
        yield _mk("persist", i, phi,
                  {"a": a, "b": b, "c": c, "d": d},
                  expected="UNSAT" if unsat else "SAT",
                  witness="window slides inside the ban" if unsat else
                          "every window exits the ban; put p there")


# ── 4. carry — persistent universal until ───────────────────────────────────

def f_carry() -> Iterator[Instance]:
    """AG A(true U[a,b] p), optionally banned.

    Exercises the carry rule, including the rollover windows 2a > b.  The
    plain form is SAT (p everywhere); conjoined with AG !p it is UNSAT, since
    the first onset already demands a p and none exists.
    """
    for i in range(PER_FAMILY):
        rng = _rng("carry", i)
        a, b = _window(rng, lo_max=5, len_max=5)
        banned = i % 3 == 2
        core = ag(f"A((true) U{iv(a, b)} (p))")
        phi = conj([core, "AG (!p)"]) if banned else core
        yield _mk("carry", i, phi,
                  {"a": a, "b": b, "rollover": 2 * a > b, "banned": banned},
                  expected="UNSAT" if banned else "SAT",
                  witness="no p at all" if banned else "p everywhere")


# ── 5. release — nested timed releases ──────────────────────────────────────

def f_release() -> Iterator[Instance]:
    """Nested A(q R ...) / EG layers — the dual shape to unest, unlabelled."""
    for i in range(PER_FAMILY):
        rng = _rng("release", i)
        d = 1 + i % 6
        phi = "p"
        for k in range(d):
            a, b = _window(rng, lo_max=3, len_max=4)
            phi = ar("q", phi, a, b) if k % 2 == 0 else eg(phi, a, b)
        yield _mk("release", i, phi, {"depth": d})


# ── 6. wide — concurrent staggered windows ──────────────────────────────────

def f_wide() -> Iterator[Instance]:
    """Conjunction of k staggered EF[a_j, b_j] p_j — clock dimensionality.

    SAT: the obligations are independent eventualities from time 0, so one
    run visiting each atom inside its window realises all of them.
    """
    for i in range(PER_FAMILY):
        rng = _rng("wide", i)
        k = 2 + i % 10
        parts, offs = [], []
        for j in range(k):
            a = rng.randint(0, 3) + j
            w = rng.randint(1, 3)
            parts.append(f"EF{iv(a, a + w)} (p{j})")
            offs.append(a)
        yield _mk("wide", i, conj(parts), {"k": k, "max_off": max(offs)},
                  expected="SAT",
                  witness="visit p_j at its window's midpoint, one at a time")


# ── 7. boolmix — random boolean trees over timed leaves ─────────────────────

def f_boolmix() -> Iterator[Instance]:
    """Random &/| trees over EF/AF/EG/AG leaves with small windows."""
    def leaf(rng: random.Random) -> str:
        a, b = _window(rng, lo_max=3, len_max=3)
        atom = rng.choice(ATOMS)
        if rng.random() < 0.3:
            atom = "!" + atom
        op = rng.choice([ef, af, eg, ag])
        return op(atom, a, b)

    def tree(rng: random.Random, n: int) -> str:
        if n <= 1:
            return leaf(rng)
        left = rng.randint(1, n - 1)
        op = "&" if rng.random() < 0.5 else "|"
        return f"({tree(rng, left)}) {op} ({tree(rng, n - left)})"

    for i in range(PER_FAMILY):
        rng = _rng("boolmix", i)
        n = 2 + i % 8
        yield _mk("boolmix", i, tree(rng, n), {"leaves": n})


# ── 8. altern — alternating AG/EF layers ────────────────────────────────────

def f_altern() -> Iterator[Instance]:
    """AG(EF(AG(EF ... p))) with windows — the re-demand tower."""
    for i in range(PER_FAMILY):
        rng = _rng("altern", i)
        d = 1 + i % 4                        # layers of AG(EF ...)
        phi = "p"
        for _ in range(d):
            a, b = _window(rng, lo_max=2, len_max=3)
            phi = ag(ef(phi, a, b))
        yield _mk("altern", i, phi, {"layers": d}, expected="SAT",
                  witness="p everywhere satisfies every EF at every onset")


# ── 9. deadline — bounded eventuality against a ban ─────────────────────────

def f_deadline() -> Iterator[Instance]:
    """AF[a,b] p & AG[c,d] !p.

    A single onset at time 0: UNSAT iff [a,b] is contained in [c,d],
    otherwise p placed at a point of [a,b] \\ [c,d] gives a model.
    """
    for i in range(PER_FAMILY):
        rng = _rng("deadline", i)
        a, b = _window(rng, lo_max=5, len_max=5)
        c = rng.randint(0, 6)
        d = c + rng.randint(1, 6)
        unsat = c <= a and b <= d
        phi = conj([af("p", a, b), ag("!p", c, d)])
        yield _mk("deadline", i, phi, {"a": a, "b": b, "c": c, "d": d},
                  expected="UNSAT" if unsat else "SAT",
                  witness="ban covers the window" if unsat else
                          "a point of the window escapes the ban")


# ── 10. untimed — pure CTL shapes as a baseline ─────────────────────────────

def f_untimed() -> Iterator[Instance]:
    """Untimed nests (all windows [0,inf)) — no clocks, no zones.

    Even indices: AG EF towers, SAT by p-everywhere.  Odd indices: the same
    tower conjoined with AG !p, UNSAT since the innermost EF p needs a p.
    """
    for i in range(PER_FAMILY):
        rng = _rng("untimed", i)
        d = 1 + i % 10
        phi = "p"
        for k in range(d):
            phi = f"EF ({phi})" if k % 2 == 0 else f"AG ({phi})"
        banned = i % 2 == 1
        if banned:
            phi = conj([phi, "AG (!p)"])
        yield _mk("untimed", i, phi, {"depth": d, "banned": banned},
                  expected="UNSAT" if banned else "SAT",
                  witness="EF p is reached but p is banned" if banned else
                          "p everywhere")


FAMILIES = [f_unest, f_anest, f_persist, f_carry, f_release,
            f_wide, f_boolmix, f_altern, f_deadline, f_untimed]


def all_instances() -> List[Instance]:
    out: List[Instance] = []
    for f in FAMILIES:
        out.extend(f())
    return out
