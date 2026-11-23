"""Goodstein sequences and their ordinal descent (a resource of the parent, not the child).

Goodstein's theorem (every Goodstein sequence reaches 0) is true, is a Π2
statement of arithmetic, and is NOT provable in PA (Kirby & Paris 1982); it is
provable with induction along ε0.  Here the parent only *computes*: sequences
for small seeds and, at every step, the strict decrease of the associated
ordinal below ε0 (Cantor normal form).  For seed 4 the sequence has length
3·2^402653211 − 2 (Kirby-Paris), far beyond any computation: an example of a
true, PA-provable-instance statement that is computationally out of reach.
"""
from __future__ import annotations

from functools import cmp_to_key
from typing import List, Tuple

# ordinals below ε0 in Cantor normal form: tuple of (exponent, coefficient), exponents decreasing
Ord = Tuple[Tuple["Ord", int], ...]
ZERO_ORD: Ord = ()


def ord_cmp(a: Ord, b: Ord) -> int:
    for (ea, ca), (eb, cb) in zip(a, b):
        c = ord_cmp(ea, eb)
        if c:
            return c
        if ca != cb:
            return -1 if ca < cb else 1
    if len(a) == len(b):
        return 0
    return -1 if len(a) < len(b) else 1


def hereditary(n: int, b: int) -> List[Tuple["object", int]]:
    """Hereditary base-b representation: list of (exponent-representation, coefficient)."""
    out = []
    e = 0
    terms = []
    while n:
        n, d = divmod(n, b)
        if d:
            terms.append((e, d))
        e += 1
    return [(hereditary(e, b), d) for e, d in reversed(terms)]


def evaluate(rep, b: int) -> int:
    return sum(d * b ** evaluate(e, b) for e, d in rep)


def to_ordinal(rep) -> Ord:
    return tuple((to_ordinal(e), d) for e, d in rep)


def goodstein(seed: int, max_steps: int = 10 ** 5):
    """Returns (terminated, steps, max_value_digits, ordinal_strictly_decreasing)."""
    n, b = seed, 2
    steps = 0
    prev = None
    decreasing = True
    max_digits = len(str(n))
    while n > 0 and steps < max_steps:
        rep = hereditary(n, b)
        o = to_ordinal(rep)
        if prev is not None and ord_cmp(o, prev) >= 0:
            decreasing = False
        prev = o
        n = evaluate(rep, b + 1) - 1
        b += 1
        steps += 1
        max_digits = max(max_digits, len(str(n)))
    return n == 0, steps, max_digits, decreasing
