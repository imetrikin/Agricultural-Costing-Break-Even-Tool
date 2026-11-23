"""Cooper's quantifier-elimination procedure for Presburger arithmetic over ℕ.

Input formulas are kernel formulas of the language {0, S, +, <, =} (plus
numeral literals).  Every variable ranges over ℕ.  The procedure returns an
equivalent quantifier-free formula built from atoms

    ('lt', L)       0 < L
    ('eq', L)       L = 0
    ('dvd', d, L)   d | L          ('ndvd', d, L)  not d | L

where L is an integer linear combination of variables plus a constant.  For
sentences the result is ground and therefore *decides* the sentence.

Correctness of the method: Cooper (1972); Presburger (1929) for completeness
of the axiomatization.  Our implementation is cross-checked against Z3 and
against brute force on bounded formulas (see tests and experiments).
"""
from __future__ import annotations

from functools import reduce
from math import gcd
from typing import Dict, FrozenSet, List, Optional, Tuple

from ..logic.syntax import (
    Atom, Bot, And, Exists, Fn, Forall, Formula, Imp, Num, Or, Term, Var,
)

# ---------------------------------------------------------------------------
# Linear terms
# ---------------------------------------------------------------------------


class Lin:
    __slots__ = ("c", "k", "_h")

    def __init__(self, coeffs: Dict[str, int], const: int = 0):
        self.c = tuple(sorted((v, a) for v, a in coeffs.items() if a != 0))
        self.k = const
        self._h = hash((self.c, self.k))

    def __eq__(self, o):
        return isinstance(o, Lin) and self.c == o.c and self.k == o.k

    def __hash__(self):
        return self._h

    def coeff(self, v: str) -> int:
        for (w, a) in self.c:
            if w == v:
                return a
        return 0

    def vars(self) -> FrozenSet[str]:
        return frozenset(v for v, _ in self.c)

    def d(self):
        return dict(self.c)

    def __add__(self, o: "Lin") -> "Lin":
        d = self.d()
        for v, a in o.c:
            d[v] = d.get(v, 0) + a
        return Lin(d, self.k + o.k)

    def scale(self, m: int) -> "Lin":
        return Lin({v: a * m for v, a in self.c}, self.k * m)

    def neg(self) -> "Lin":
        return self.scale(-1)

    def add_const(self, n: int) -> "Lin":
        return Lin(self.d(), self.k + n)

    def drop(self, v: str) -> "Lin":
        d = self.d()
        d.pop(v, None)
        return Lin(d, self.k)

    def subst(self, v: str, e: "Lin") -> "Lin":
        a = self.coeff(v)
        if a == 0:
            return self
        return self.drop(v) + e.scale(a)

    def is_const(self) -> bool:
        return not self.c

    def __repr__(self):
        parts = [f"{a}*{v}" for v, a in self.c]
        if self.k or not parts:
            parts.append(str(self.k))
        return " + ".join(parts)


def lin_var(v: str) -> Lin:
    return Lin({v: 1})


def lin_const(n: int) -> Lin:
    return Lin({}, n)


def lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)


# ---------------------------------------------------------------------------
# QE formula AST
# ---------------------------------------------------------------------------

TRUE = ("true",)
FALSE = ("false",)


def term_to_lin(t: Term) -> Lin:
    tt = type(t)
    if tt is Var:
        return lin_var(t.name)
    if tt is Num:
        return lin_const(t.value)
    if t.name == "0":
        return lin_const(0)
    if t.name == "S":
        return term_to_lin(t.args[0]).add_const(1)
    if t.name == "+":
        return term_to_lin(t.args[0]) + term_to_lin(t.args[1])
    raise ValueError(f"symbol {t.name!r} is not Presburger-expressible")


def from_formula(f: Formula):
    tf = type(f)
    if tf is Bot:
        return FALSE
    if tf is Atom:
        s, t = f.args
        ls, lt = term_to_lin(s), term_to_lin(t)
        if f.pred == "=":
            return ("eq", ls + lt.neg())
        if f.pred == "<":
            return ("lt", lt + ls.neg())
        raise ValueError(f.pred)
    if tf is Imp:
        return ("or", [("not", from_formula(f.a)), from_formula(f.b)])
    if tf is And:
        return ("and", [from_formula(f.a), from_formula(f.b)])
    if tf is Or:
        return ("or", [from_formula(f.a), from_formula(f.b)])
    if tf is Exists:
        return ("ex", f.var, from_formula(f.body))
    if tf is Forall:
        return ("all", f.var, from_formula(f.body))
    raise TypeError(f)


# ---------------------------------------------------------------------------
# Simplification
# ---------------------------------------------------------------------------


def norm_atom(a):
    tag = a[0]
    if tag == "lt":
        L = a[1]
        if L.is_const():
            return TRUE if L.k > 0 else FALSE
        g = reduce(gcd, [abs(c) for _, c in L.c])
        if g > 1:
            # 0 < g*M + k  <=>  0 < M + floor((k-1)/g) + 1   (integers)
            k = L.k
            newk = (k - 1) // g + 1
            L = Lin({v: c // g for v, c in L.c}, newk)
        return ("lt", L)
    if tag == "eq":
        L = a[1]
        if L.is_const():
            return TRUE if L.k == 0 else FALSE
        g = reduce(gcd, [abs(c) for _, c in L.c])
        if L.k % g != 0:
            return FALSE
        if g > 1:
            L = Lin({v: c // g for v, c in L.c}, L.k // g)
        # canonical sign: first coefficient positive
        if L.c[0][1] < 0:
            L = L.neg()
        return ("eq", L)
    if tag in ("dvd", "ndvd"):
        d, L = a[1], a[2]
        d = abs(d)
        L = Lin({v: c % d for v, c in L.c}, L.k % d) if d else L
        if d == 1:
            return TRUE if tag == "dvd" else FALSE
        if L.is_const():
            ok = (L.k % d == 0)
            return TRUE if ok == (tag == "dvd") else FALSE
        return (tag, d, L)
    return a


def mk_and(xs):
    out = []
    seen = set()
    for x in xs:
        if x == FALSE:
            return FALSE
        if x == TRUE:
            continue
        if x[0] == "and":
            for y in x[1]:
                if y not in seen:
                    seen.add(y)
                    out.append(y)
            continue
        if x not in seen:
            seen.add(x)
            out.append(x)
    if not out:
        return TRUE
    if len(out) == 1:
        return out[0]
    return ("and", tuple(out))


def mk_or(xs):
    out = []
    seen = set()
    for x in xs:
        if x == TRUE:
            return TRUE
        if x == FALSE:
            continue
        if x[0] == "or":
            for y in x[1]:
                if y not in seen:
                    seen.add(y)
                    out.append(y)
            continue
        if x not in seen:
            seen.add(x)
            out.append(x)
    if not out:
        return FALSE
    if len(out) == 1:
        return out[0]
    return ("or", tuple(out))


def nnf(f, neg=False):
    tag = f[0]
    if tag == "true":
        return FALSE if neg else TRUE
    if tag == "false":
        return TRUE if neg else FALSE
    if tag == "not":
        return nnf(f[1], not neg)
    if tag == "and":
        parts = [nnf(g, neg) for g in f[1]]
        return mk_or(parts) if neg else mk_and(parts)
    if tag == "or":
        parts = [nnf(g, neg) for g in f[1]]
        return mk_and(parts) if neg else mk_or(parts)
    if tag in ("ex", "all"):
        raise ValueError("nnf expects quantifier-free input")
    if not neg:
        return norm_atom(f)
    if tag == "lt":       # not 0 < L   <=>  0 < 1 - L
        return norm_atom(("lt", lin_const(1) + f[1].neg()))
    if tag == "eq":       # L != 0  <=>  0 < L or 0 < -L
        return mk_or([norm_atom(("lt", f[1])), norm_atom(("lt", f[1].neg()))])
    if tag == "dvd":
        return norm_atom(("ndvd", f[1], f[2]))
    if tag == "ndvd":
        return norm_atom(("dvd", f[1], f[2]))
    raise ValueError(tag)


# ---------------------------------------------------------------------------
# Cooper elimination
# ---------------------------------------------------------------------------


def atoms(f):
    tag = f[0]
    if tag in ("and", "or"):
        for g in f[1]:
            yield from atoms(g)
    elif tag in ("lt", "eq", "dvd", "ndvd"):
        yield f


def atom_lin(a):
    return a[1] if a[0] in ("lt", "eq") else a[2]


def map_atoms(f, fn):
    tag = f[0]
    if tag == "and":
        return mk_and([map_atoms(g, fn) for g in f[1]])
    if tag == "or":
        return mk_or([map_atoms(g, fn) for g in f[1]])
    if tag in ("lt", "eq", "dvd", "ndvd"):
        return fn(f)
    return f


def subst_formula(f, x: str, e: Lin):
    def fn(a):
        if a[0] in ("lt", "eq"):
            return norm_atom((a[0], a[1].subst(x, e)))
        return norm_atom((a[0], a[1], a[2].subst(x, e)))
    return map_atoms(f, fn)


class QEStats:
    def __init__(self):
        self.eliminations = 0
        self.max_disjuncts = 0


def cooper_exists(x: str, phi, stats: Optional[QEStats] = None):
    """Eliminate ∃x ∈ ℤ from a quantifier-free NNF formula."""
    coeffs = [atom_lin(a).coeff(x) for a in atoms(phi)]
    coeffs = [abs(c) for c in coeffs if c != 0]
    if not coeffs:
        return phi
    l = reduce(lcm, coeffs, 1)

    def scale(a):
        c = atom_lin(a).coeff(x)
        if c == 0:
            return a
        m = l // abs(c)
        if a[0] == "lt":
            L = a[1].scale(m)
        elif a[0] == "eq":
            L = a[1].scale(m)
        else:
            L = a[2].scale(m)
        # replace l*x by x (coefficient becomes ±1)
        d = L.d()
        d[x] = 1 if d[x] > 0 else -1
        L = Lin(d, L.k)
        if a[0] in ("lt", "eq"):
            return (a[0], L)
        return (a[0], a[1] * m, L)

    phi1 = map_atoms(phi, scale)
    if l > 1:
        phi1 = mk_and([phi1, ("dvd", l, lin_var(x))])
    # φ_{-∞}
    def minf(a):
        c = atom_lin(a).coeff(x)
        if c == 0 or a[0] in ("dvd", "ndvd"):
            return a
        if a[0] == "lt":
            return TRUE if c < 0 else FALSE
        return FALSE  # eq
    phi_minf = map_atoms(phi1, minf)
    delta = 1
    for a in atoms(phi1):
        if a[0] in ("dvd", "ndvd") and a[2].coeff(x) != 0:
            delta = lcm(delta, a[1])
    bset = []
    for a in atoms(phi1):
        if a[0] == "lt":
            c = a[1].coeff(x)
            if c == 1:          # 0 < x + t  <=>  x > -t
                bset.append(a[1].drop(x).neg())
        elif a[0] == "eq":
            c = a[1].coeff(x)
            t = a[1].drop(x)
            if c == 1:          # x + t = 0  <=>  x = -t
                bset.append(t.neg().add_const(-1))
            elif c == -1:       # -x + t = 0 <=>  x = t
                bset.append(t.add_const(-1))
    bset = list(dict.fromkeys(bset))
    disj = []
    for j in range(1, delta + 1):
        disj.append(subst_formula(phi_minf, x, lin_const(j)))
        for b in bset:
            disj.append(subst_formula(phi1, x, b.add_const(j)))
    out = mk_or(disj)
    if stats is not None:
        stats.eliminations += 1
        stats.max_disjuncts = max(stats.max_disjuncts, len(disj))
    return out


def qe(f, stats: Optional[QEStats] = None, naturals: bool = True):
    """Quantifier elimination; returns a quantifier-free NNF formula."""
    tag = f[0]
    if tag in ("true", "false", "lt", "eq", "dvd", "ndvd"):
        return nnf(f)
    if tag == "not":
        return nnf(qe(f[1], stats, naturals), True)
    if tag == "and":
        return mk_and([qe(g, stats, naturals) for g in f[1]])
    if tag == "or":
        return mk_or([qe(g, stats, naturals) for g in f[1]])
    if tag == "ex":
        x, body = f[1], f[2]
        b = qe(body, stats, naturals)
        if naturals:
            b = mk_and([("lt", lin_var(x).add_const(1)), b])  # x >= 0
        return cooper_exists(x, nnf(b), stats)
    if tag == "all":
        return nnf(qe(("ex", f[1], ("not", f[2])), stats, naturals), True)
    raise ValueError(tag)


def eval_qf(f, env: Dict[str, int]) -> bool:
    tag = f[0]
    if tag == "true":
        return True
    if tag == "false":
        return False
    if tag == "and":
        return all(eval_qf(g, env) for g in f[1])
    if tag == "or":
        return any(eval_qf(g, env) for g in f[1])
    if tag == "not":
        return not eval_qf(f[1], env)

    def ev(L: Lin):
        return L.k + sum(a * env[v] for v, a in L.c)
    if tag == "lt":
        return ev(f[1]) > 0
    if tag == "eq":
        return ev(f[1]) == 0
    if tag == "dvd":
        return ev(f[2]) % f[1] == 0
    if tag == "ndvd":
        return ev(f[2]) % f[1] != 0
    raise ValueError(tag)


def decide(f: Formula, stats: Optional[QEStats] = None) -> bool:
    """Decide a Presburger sentence (variables over ℕ)."""
    if f.fv():
        raise ValueError("decide expects a sentence")
    q = qe(from_formula(f), stats)
    return eval_qf(q, {})


def qe_formula(f: Formula, stats: Optional[QEStats] = None):
    return qe(from_formula(f), stats)


def qf_size(f) -> int:
    tag = f[0]
    if tag in ("and", "or"):
        return 1 + sum(qf_size(g) for g in f[1])
    if tag == "not":
        return 1 + qf_size(f[1])
    return 1
