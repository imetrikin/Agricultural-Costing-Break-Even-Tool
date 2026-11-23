"""General metamathematical tools (uniform: they mention no particular theory).

  * Gödel numbering of a first-order language by Cantor-pairing tree codes
  * enumeration of modal schemas A(p) with p modalized (self-reference patterns)
  * fixed-point analysis of such schemas via GL
"""
from __future__ import annotations

import itertools
from typing import Dict, Iterable, List, Optional, Tuple

from ..logic.syntax import (
    Atom, Bot, And, Exists, Fn, Forall, Formula, Imp, Num, Or, Term, Var,
)
from ..modal import gl as G

# ---------------------------------------------------------------------------
# Gödel numbering
# ---------------------------------------------------------------------------


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(z: int) -> Tuple[int, int]:
    import math
    w = (math.isqrt(8 * z + 1) - 1) // 2
    t = w * (w + 1) // 2
    b = z - t
    return w - b, b


TAGS = {"var": 0, "0": 1, "num": 2, "S": 3, "+": 4, "*": 5, "=": 6, "<": 7, "bot": 8,
        "imp": 9, "and": 10, "or": 11, "all": 12, "ex": 13}


def var_index(name: str) -> int:
    # deterministic injective map from variable names to ℕ
    return int.from_bytes(name.encode(), "big")


def code_term(t: Term) -> int:
    if isinstance(t, Var):
        return pair(TAGS["var"], var_index(t.name))
    if isinstance(t, Num):
        return pair(TAGS["num"], t.value)
    if t.name == "0":
        return pair(TAGS["0"], 0)
    if t.name == "S":
        return pair(TAGS["S"], code_term(t.args[0]))
    return pair(TAGS[t.name], pair(code_term(t.args[0]), code_term(t.args[1])))


def code(f: Formula) -> int:
    if isinstance(f, Bot):
        return pair(TAGS["bot"], 0)
    if isinstance(f, Atom):
        return pair(TAGS[f.pred], pair(code_term(f.args[0]), code_term(f.args[1])))
    if isinstance(f, Imp):
        return pair(TAGS["imp"], pair(code(f.a), code(f.b)))
    if isinstance(f, And):
        return pair(TAGS["and"], pair(code(f.a), code(f.b)))
    if isinstance(f, Or):
        return pair(TAGS["or"], pair(code(f.a), code(f.b)))
    if isinstance(f, Forall):
        return pair(TAGS["all"], pair(var_index(f.var), code(f.body)))
    if isinstance(f, Exists):
        return pair(TAGS["ex"], pair(var_index(f.var), code(f.body)))
    raise TypeError(f)


def negation_code(c: int) -> int:
    """code(¬φ) as a function of code(φ): a quadratic polynomial in c."""
    return pair(TAGS["imp"], pair(c, pair(TAGS["bot"], 0)))


# ---------------------------------------------------------------------------
# Modal schemas
# ---------------------------------------------------------------------------


def enumerate_schemas(max_size: int, p: str = "p") -> List[tuple]:
    """All modal formulas over {p, ⊥} with ¬, ∧, ∨, →, □ up to `max_size`, deduplicated."""
    by_size: Dict[int, List[tuple]] = {1: [G.V(p), G.BOT]}
    for s in range(2, max_size + 1):
        out = []
        for a in by_size.get(s - 1, []):
            out.append(G.Box(a))
            out.append(G.Not(a))
        for ls in range(1, s - 1):
            rs = s - 1 - ls
            for a in by_size.get(ls, []):
                for b in by_size.get(rs, []):
                    out.append(G.Imp(a, b))
                    out.append(G.And(a, b))
                    out.append(G.Or(a, b))
        by_size[s] = out
    seen = set()
    res = []
    for s in sorted(by_size):
        for f in by_size[s]:
            if f not in seen:
                seen.add(f)
                res.append(f)
    return res


def schema_name(A, p="p") -> str:
    return G.show(A)


def simplest_equivalent(H) -> tuple:
    """A short letterless formula with the same trace (hence GL-equivalent)."""
    tr = G.trace(H, G.modal_depth(H) + 3)
    d = G.modal_depth(H) + 2
    cands = [G.TOP, G.BOT]
    for a in range(1, d + 1):
        cands += [G.boxes(a, G.BOT), G.con(a)]
    for a in range(1, d + 1):
        for b in range(1, d + 1):
            cands += [G.And(G.boxes(a, G.BOT), G.con(b)), G.Or(G.boxes(a, G.BOT), G.con(b))]
    for c in cands:
        if G.trace(c, len(tr)) == tr and G.modal_depth(c) <= len(tr) - 2:
            return c
    return H


def classify_fixed_point(H) -> Dict:
    """Status of a self-referential sentence σ with T ⊢ σ ↔ H (letterless)."""
    tr = G.trace(H, G.modal_depth(H) + 3)
    provable = all(tr)
    refutable = not any(tr)
    info = {"trace": tr, "gl_provable": provable, "gl_refutable": refutable}
    if not provable:
        info["unprovable_given_con"] = G.min_consistency_for(H, True)
    if not refutable:
        info["unrefutable_given_con"] = G.min_consistency_for(H, False)
    return info
