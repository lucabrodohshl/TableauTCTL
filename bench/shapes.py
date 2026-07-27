"""Random TCTL shape generation for the RQ3 search.

A shape is produced once as an AST -- which :mod:`oracle` evaluates exactly on a
witness structure -- and once as concrete syntax for the solver, so the two can
never drift apart.  The generator is parameterised by everything the
completeness argument implicates: nesting depth, how often a window is punctual,
whether windows are aligned with one another, and the magnitude of the bounds.
"""

from __future__ import annotations

import random
from fractions import Fraction as F
from typing import List, Optional, Tuple

ATOMS = ["p", "q", "r"]
MODALS = ["EF", "AG", "AF", "EG"]


def render(node) -> str:
    """Concrete syntax, matching src/lexer.cpp."""
    k = node[0]
    if k == "atom":
        return node[1]
    if k == "not":
        return f"!({render(node[1])})"
    if k == "and":
        return f"(({render(node[1])}) & ({render(node[2])}))"
    if k == "or":
        return f"(({render(node[1])}) | ({render(node[2])}))"
    a, b, sub = node[1], node[2], node[3]
    win = f"[{a},inf)" if b is None else f"[{a},{b}]"
    return f"{k}{win} ({render(sub)})"


def gen(rng: random.Random, depth: int, p_punctual: float,
        max_const: int = 6, p_unbounded: float = 0.15,
        p_bool: float = 0.35, modals: Optional[List[str]] = None) -> tuple:
    """One random formula of modal nesting depth exactly ``depth``."""
    modals = modals or MODALS
    if depth == 0:
        a = rng.choice(ATOMS)
        return ("not", ("atom", a)) if rng.random() < 0.25 else ("atom", a)

    if rng.random() < p_bool:
        op = rng.choice(["and", "or"])
        # split the remaining depth so the deeper side still reaches `depth`
        left = gen(rng, depth - 1, p_punctual, max_const, p_unbounded, p_bool, modals)
        right = gen(rng, rng.randint(0, depth - 1), p_punctual, max_const,
                    p_unbounded, p_bool, modals)
        return (op, left, right) if rng.random() < 0.5 else (op, right, left)

    mod = rng.choice(modals)
    if rng.random() < p_unbounded:
        a, b = rng.randint(0, 2), None
    elif rng.random() < p_punctual:
        a = rng.randint(1, max_const)
        b = a                                  # punctual [a,a]
    else:
        a = rng.randint(0, max_const - 1)
        b = rng.randint(a + 1, max_const)
    return (mod, a, b, gen(rng, depth - 1, p_punctual, max_const,
                           p_unbounded, p_bool, modals))


def branch_witnesses():
    """Two-location structures, so that `E` and `A` genuinely differ.

    The atom patterns are chosen so no location dominates the other: each holds
    atoms the other lacks, which is what forces `AG` to consult both branches
    and lets `EF` profit from choosing one.
    """
    from oracle import BranchWitness, PSet

    def mk(P, l0, l1, label):
        P = F(P)

        def sets(spec):
            d = {}
            for name, ivs in spec.items():
                d[name] = PSet.of(P, [(F(lo), True, F(hi), False) for lo, hi in ivs])
            for a in ATOMS:
                d.setdefault(a, PSet.empty(P))
            return d

        return BranchWitness(P, sets(l0), sets(l1), label)

    return [
        mk(2, {"p": [(0, 1)], "q": [(0, 2)]}, {"q": [(0, 2)], "r": [(0, 2)]},
           "br-unit"),
        mk(3, {"p": [(F(1, 2), F(3, 2))], "q": [(0, 3)]},
              {"q": [(0, 3)], "r": [(1, 2)]}, "br-half"),
        mk(5, {"p": [(F(1, 3), F(4, 3))], "r": [(0, 5)]},
              {"q": [(F(7, 3), 3)], "r": [(0, 5)]}, "br-third"),
        mk(4, {"p": [(0, 1), (2, 3)], "q": [(0, 4)]},
              {"q": [(0, 4)], "r": [(F(1, 2), F(7, 2))]}, "br-bursts"),
    ]


def punctual_count(node) -> int:
    k = node[0]
    if k == "atom":
        return 0
    if k == "not":
        return punctual_count(node[1])
    if k in ("and", "or"):
        return punctual_count(node[1]) + punctual_count(node[2])
    return (1 if node[2] == node[1] else 0) + punctual_count(node[3])


def modal_depth(node) -> int:
    k = node[0]
    if k == "atom":
        return 0
    if k == "not":
        return modal_depth(node[1])
    if k in ("and", "or"):
        return max(modal_depth(node[1]), modal_depth(node[2]))
    return 1 + modal_depth(node[3])


def size(node) -> int:
    k = node[0]
    if k == "atom":
        return 1
    if k == "not":
        return 1 + size(node[1])
    if k in ("and", "or"):
        return 1 + size(node[1]) + size(node[2])
    return 1 + size(node[3])


# ── Witness structures ──────────────────────────────────────────────────────
# Deliberately varied, and deliberately including fractional atom boundaries:
# the completeness argument turns on whether one formula-clock can serve onsets
# whose pending obligations sit at distinct offsets, so a model whose atom
# changes never line up with the integer window endpoints is the adversarial
# case.

def witnesses():
    from oracle import PSet, Witness
    out = []

    def W(P, spec, label):
        P = F(P)
        atoms = {}
        for name, ivs in spec.items():
            atoms[name] = PSet.of(P, [(F(lo), True, F(hi), False) for lo, hi in ivs])
        for a in ATOMS:
            atoms.setdefault(a, PSet.empty(P))
        out.append(Witness(P, atoms, label))

    W(1, {"p": [(0, 1)], "q": [(0, 1)], "r": [(0, 1)]}, "all-true")
    W(2, {"p": [(0, 1)], "q": [(1, 2)], "r": [(0, 2)]}, "alternating-unit")
    W(3, {"p": [(F(1, 2), F(3, 2))], "q": [(2, 3)], "r": [(0, 3)]}, "half-offset")
    W(5, {"p": [(F(1, 3), F(4, 3))], "q": [(F(7, 3), 3)], "r": [(0, 5)]},
      "third-offset")
    W(4, {"p": [(0, 1), (2, 3)], "q": [(1, 2)], "r": [(F(1, 2), F(7, 2))]},
      "two-bursts")
    W(7, {"p": [(F(1, 2), 1)], "q": [(3, F(7, 2))], "r": [(0, 7)]}, "sparse-prime")
    return out
