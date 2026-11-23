"""An independent re-implementation of the proof checker.

Purpose (two roles):
  1. Verification: every proof accepted by kernel.py can be re-checked here.
     This file deliberately does NOT use the substitution / alpha-equivalence /
     free-variable code of syntax.py; it converts input to its own locally
     nameless (de Bruijn) representation and implements every rule anew.
  2. Experiment control "two different parents implementing the same child":
     it evaluates closed terms with decimal *string* arithmetic instead of
     machine integers, i.e. a radically different arithmetic substrate.

Only the input data classes (Var, Fn, Num, Atom, ...) are shared.
"""
from __future__ import annotations

from typing import Dict, List, Optional, Tuple

from . import syntax as S_

# ---------------------------------------------------------------------------
# Locally nameless representation
#   terms:    ('v', name) | ('b', i) | ('f', name, args) | ('n', digits-string)
#   formulas: ('A', pred, args) | ('F',) | ('I', a, b) | ('C', a, b) | ('D', a, b)
#             | ('all', body) | ('ex', body)
# ---------------------------------------------------------------------------


class Reject(Exception):
    pass


def _dt(t, env: List[str]):
    if isinstance(t, S_.Var):
        for i, n in enumerate(env):
            if n == t.name:
                return ("b", i)
        return ("v", t.name)
    if isinstance(t, S_.Num):
        return ("n", str(t.value))
    if isinstance(t, S_.Fn):
        return ("f", t.name, tuple(_dt(a, env) for a in t.args))
    raise Reject("bad term")


def _df(f, env: List[str]):
    if isinstance(f, S_.Bot):
        return ("F",)
    if isinstance(f, S_.Atom):
        return ("A", f.pred, tuple(_dt(a, env) for a in f.args))
    if isinstance(f, S_.Imp):
        return ("I", _df(f.a, env), _df(f.b, env))
    if isinstance(f, S_.And):
        return ("C", _df(f.a, env), _df(f.b, env))
    if isinstance(f, S_.Or):
        return ("D", _df(f.a, env), _df(f.b, env))
    if isinstance(f, S_.Forall):
        return ("all", _df(f.body, [f.var] + env))
    if isinstance(f, S_.Exists):
        return ("ex", _df(f.body, [f.var] + env))
    raise Reject("bad formula")


def db_term(t):
    return _dt(t, [])


def db(f):
    return _df(f, [])


def t_free(t, acc):
    if t[0] == "v":
        acc.add(t[1])
    elif t[0] == "f":
        for a in t[2]:
            t_free(a, acc)
    return acc


def f_free(f, acc=None):
    acc = set() if acc is None else acc
    k = f[0]
    if k == "A":
        for a in f[2]:
            t_free(a, acc)
    elif k in ("I", "C", "D"):
        f_free(f[1], acc)
        f_free(f[2], acc)
    elif k in ("all", "ex"):
        f_free(f[1], acc)
    return acc


def t_inst(t, depth: int, u):
    """Replace bound index `depth` by u (u has no bound indices)."""
    k = t[0]
    if k == "b":
        return u if t[1] == depth else t
    if k == "f":
        return ("f", t[1], tuple(t_inst(a, depth, u) for a in t[2]))
    return t


def f_inst(f, depth: int, u):
    k = f[0]
    if k == "A":
        return ("A", f[1], tuple(t_inst(a, depth, u) for a in f[2]))
    if k == "F":
        return f
    if k in ("I", "C", "D"):
        return (k, f_inst(f[1], depth, u), f_inst(f[2], depth, u))
    return (k, f_inst(f[1], depth + 1, u))


def instantiate(q, u):
    """For q = ('all'|'ex', body): body[u/0]."""
    return f_inst(q[1], 0, u)


def t_abs(t, name, depth):
    k = t[0]
    if k == "v":
        return ("b", depth) if t[1] == name else t
    if k == "f":
        return ("f", t[1], tuple(t_abs(a, name, depth) for a in t[2]))
    return t


def f_abs(f, name, depth=0):
    k = f[0]
    if k == "A":
        return ("A", f[1], tuple(t_abs(a, name, depth) for a in f[2]))
    if k == "F":
        return f
    if k in ("I", "C", "D"):
        return (k, f_abs(f[1], name, depth), f_abs(f[2], name, depth))
    return (k, f_abs(f[1], name, depth + 1))


def subst_free(f, name, u):
    """f[u/name] for a free variable name (u locally closed)."""
    return f_inst(f_abs(f, name, 0), 0, u) if True else f


NOT = lambda a: ("I", a, ("F",))
ZERO_T = ("f", "0", ())


def numeral(n: int):
    return ZERO_T if n == 0 else ("n", str(n))


# ---------------------------------------------------------------------------
# Decimal string arithmetic (the "different substrate")
# ---------------------------------------------------------------------------


def s_add(a: str, b: str) -> str:
    a, b = a[::-1], b[::-1]
    out, carry = [], 0
    for i in range(max(len(a), len(b))):
        d = carry + (ord(a[i]) - 48 if i < len(a) else 0) + (ord(b[i]) - 48 if i < len(b) else 0)
        out.append(chr(48 + d % 10))
        carry = d // 10
    if carry:
        out.append(chr(48 + carry))
    s = "".join(reversed(out)).lstrip("0")
    return s or "0"


def s_mul(a: str, b: str) -> str:
    if a == "0" or b == "0":
        return "0"
    res = [0] * (len(a) + len(b))
    for i, x in enumerate(reversed(a)):
        for j, y in enumerate(reversed(b)):
            res[i + j] += (ord(x) - 48) * (ord(y) - 48)
    for k in range(len(res) - 1):
        res[k + 1] += res[k] // 10
        res[k] %= 10
    s = "".join(chr(48 + d) for d in reversed(res)).lstrip("0")
    return s or "0"


def s_eval(t) -> str:
    k = t[0]
    if k == "n":
        return t[1]
    if k == "f":
        name, args = t[1], t[2]
        if name == "0":
            return "0"
        if name == "S":
            return s_add(s_eval(args[0]), "1")
        if name == "+":
            return s_add(s_eval(args[0]), s_eval(args[1]))
        if name == "*":
            return s_mul(s_eval(args[0]), s_eval(args[1]))
    raise Reject("cannot evaluate")


# ---------------------------------------------------------------------------
# Checker
# ---------------------------------------------------------------------------


class Checker2:
    def __init__(self, theory, allow_compute: bool = False):
        self.funcs = dict(theory.funcs)
        self.preds = dict(theory.preds)
        self.numerals = theory.numerals
        self.axioms = {k: db(v) for k, v in theory.axioms.items()}
        self.schema_names = set(theory.schemas)
        self.allow_compute = allow_compute
        self.lemmas: Dict[str, tuple] = {}

    # language -------------------------------------------------------------
    def _t_ok(self, t):
        k = t[0]
        if k == "n":
            return self.numerals and t[1] != "0"
        if k == "f":
            return self.funcs.get(t[1]) == len(t[2]) and all(self._t_ok(a) for a in t[2])
        return True

    def _f_ok(self, f):
        k = f[0]
        if k == "A":
            return self.preds.get(f[1]) == len(f[2]) and all(self._t_ok(a) for a in f[2])
        if k == "F":
            return True
        if k in ("I", "C", "D"):
            return self._f_ok(f[1]) and self._f_ok(f[2])
        return self._f_ok(f[1])

    def T(self, t):
        d = db_term(t)
        if not self._t_ok(d):
            raise Reject("term outside language")
        return d

    def Fm(self, f):
        d = db(f)
        if not self._f_ok(d):
            raise Reject("formula outside language")
        return d

    # schemas (independently reconstructed) ---------------------------------
    def _schema(self, name, params):
        if name not in self.schema_names:
            raise Reject("unknown schema")
        if name == "IND":
            x, phi = params
            body = f_abs(self.Fm(phi), x)                 # φ with x as bound index 0
            base = f_inst(body, 0, ZERO_T)
            xv = ("v", "__ind__")
            if "__ind__" in f_free(self.Fm(phi)):
                raise Reject("reserved name")
            step_body = ("I", f_inst(body, 0, xv), f_inst(body, 0, ("f", "S", (xv,))))
            step = ("all", f_abs(step_body, "__ind__"))
            return ("I", ("C", base, step), ("all", body))
        if name == "NUM":
            (n,) = params
            if not isinstance(n, int) or n < 0:
                raise Reject("bad NUM")
            return ("A", "=", (numeral(n + 1), ("f", "S", (numeral(n),))))
        raise Reject("unknown schema")

    # main -------------------------------------------------------------------
    def check(self, proof) -> Tuple[frozenset, tuple]:
        memo: Dict[int, Tuple[frozenset, tuple]] = {}
        order = []
        stack = [(proof, 0)]
        while stack:
            node, state = stack.pop()
            if id(node) in memo:
                continue
            if state == 0:
                stack.append((node, 1))
                for q in node.prems:
                    stack.append((q, 0))
            else:
                memo[id(node)] = self._step(node, [memo[id(q)] for q in node.prems])
                order.append(node)
        return memo[id(proof)]

    def _step(self, n, P):
        r, a = n.rule, n.args
        if r == "hyp":
            f = self.Fm(a[0])
            return frozenset([f]), f
        if r == "ax":
            name, ts = a
            if name not in self.axioms:
                raise Reject("unknown axiom")
            f = self.axioms[name]
            for t in ts:
                if f[0] != "all":
                    raise Reject("too many terms")
                f = instantiate(f, self.T(t))
            return frozenset(), f
        if r == "schema":
            return frozenset(), self._schema(a[0], a[1])
        if r == "lemma":
            name, ts = a
            if name not in self.lemmas:
                raise Reject("unknown lemma")
            f = self.lemmas[name]
            for t in ts:
                if f[0] != "all":
                    raise Reject("too many terms")
                f = instantiate(f, self.T(t))
            return frozenset(), f
        if r == "refl":
            t = self.T(a[0])
            return frozenset(), ("A", "=", (t, t))
        if r == "compute":
            if not self.allow_compute:
                raise Reject("compute disabled")
            t = self.T(a[0])
            if t_free(t, set()):
                raise Reject("open term")
            v = s_eval(t)
            return frozenset(), ("A", "=", (t, ("f", "0", ()) if v == "0" else ("n", v)))
        if r == "impI":
            (h, c) = P[0]
            f = self.Fm(a[0])
            return h - {f}, ("I", f, c)
        if r == "impE":
            (h1, c1), (h2, c2) = P
            if c1[0] != "I" or c1[1] != c2:
                raise Reject("impE")
            return h1 | h2, c1[2]
        if r == "andI":
            (h1, c1), (h2, c2) = P
            return h1 | h2, ("C", c1, c2)
        if r in ("andE1", "andE2"):
            (h, c) = P[0]
            if c[0] != "C":
                raise Reject(r)
            return h, c[1] if r == "andE1" else c[2]
        if r == "orI1":
            (h, c) = P[0]
            return h, ("D", c, self.Fm(a[0]))
        if r == "orI2":
            (h, c) = P[0]
            return h, ("D", self.Fm(a[0]), c)
        if r == "orE":
            (h, c), (hl, cl), (hr, cr) = P
            if c[0] != "D" or cl != cr:
                raise Reject("orE")
            return h | (hl - {c[1]}) | (hr - {c[2]}), cl
        if r == "botE":
            (h, c) = P[0]
            if c != ("F",):
                raise Reject("botE")
            return h, self.Fm(a[0])
        if r == "raa":
            (h, c) = P[0]
            if c != ("F",):
                raise Reject("raa")
            f = self.Fm(a[0])
            return h - {NOT(f)}, f
        if r == "allI":
            (h, c) = P[0]
            y = a[0]
            for g in h:
                if y in f_free(g):
                    raise Reject("allI eigenvariable")
            return h, ("all", f_abs(c, y))
        if r == "allE":
            (h, c) = P[0]
            if c[0] != "all":
                raise Reject("allE")
            return h, instantiate(c, self.T(a[0]))
        if r == "exI":
            (h, c) = P[0]
            x, phi, t = a
            body = f_abs(self.Fm(phi), x)
            if f_inst(body, 0, self.T(t)) != c:
                raise Reject("exI")
            return h, ("ex", body)
        if r == "exE":
            (h1, c1), (h2, c2) = P
            if c1[0] != "ex":
                raise Reject("exE")
            y = a[0]
            inst = instantiate(c1, ("v", y))
            rest = h2 - {inst}
            if y in f_free(c2) or y in f_free(c1) or any(y in f_free(g) for g in rest):
                raise Reject("exE eigenvariable")
            return h1 | rest, c2
        if r == "subst":
            (h1, c1), (h2, c2) = P
            x, phi = a
            if not (c1[0] == "A" and c1[1] == "=" and len(c1[2]) == 2):
                raise Reject("subst")
            s, t = c1[2]
            body = f_abs(self.Fm(phi), x)
            if f_inst(body, 0, s) != c2:
                raise Reject("subst premise")
            return h1 | h2, f_inst(body, 0, t)
        raise Reject(f"unknown rule {r}")

    def check_theorem(self, proof, expected=None):
        h, c = self.check(proof)
        if h:
            raise Reject("open assumptions")
        if expected is not None and db(expected) != c:
            raise Reject("conclusion mismatch")
        return c

    def add_lemma(self, name, proof, statement):
        c = self.check_theorem(proof, statement)
        if f_free(c):
            raise Reject("lemmas must be closed")
        self.lemmas[name] = c
