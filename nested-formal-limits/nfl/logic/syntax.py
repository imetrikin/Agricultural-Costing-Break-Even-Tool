"""First-order syntax shared by every environment.

Terms
    Var(name)            variable
    Fn(name, args)       function application; constants are 0-ary (e.g. Fn('0', ()))
    Num(n)               numeral literal; the theories contain the defining schema
                         NUM: Num(n+1) = S(Num(n)) and NUM0: Num(0) = 0, so a literal
                         is only notation for S(S(...S(0)...)).

Formulas (primitive connectives only; the rest are abbreviations)
    Atom(pred, args)     atomic formula, pred in {'=', '<'}
    Bot()                falsum
    Imp(a, b), And(a, b), Or(a, b)
    Forall(x, body), Exists(x, body)

    Not(a)  := Imp(a, Bot())
    Top()   := Imp(Bot(), Bot())
    Iff(a,b):= And(Imp(a, b), Imp(b, a))

Everything here is pure data manipulation.  Nothing in this module decides
whether a formula is *provable*; that is the job of ``kernel.py``.
"""
from __future__ import annotations

import itertools
import re
from typing import Dict, FrozenSet, Iterable, Optional, Tuple

# ---------------------------------------------------------------------------
# Terms
# ---------------------------------------------------------------------------


class Term:
    __slots__ = ()

    def fv(self) -> FrozenSet[str]:
        raise NotImplementedError


class Var(Term):
    __slots__ = ("name", "_h")

    def __init__(self, name: str):
        self.name = name
        self._h = hash(("V", name))

    def __eq__(self, o):
        return self is o or (type(o) is Var and o.name == self.name)

    def __hash__(self):
        return self._h

    def fv(self):
        return frozenset((self.name,))

    def __repr__(self):
        return self.name


class Num(Term):
    __slots__ = ("value", "_h")

    def __init__(self, value: int):
        if value < 1:
            raise ValueError("numeral literals denote positive integers; use ZERO for 0")
        self.value = int(value)
        self._h = hash(("N", self.value))

    def __eq__(self, o):
        return self is o or (type(o) is Num and o.value == self.value)

    def __hash__(self):
        return self._h

    def fv(self):
        return frozenset()

    def __repr__(self):
        return str(self.value)


class Fn(Term):
    __slots__ = ("name", "args", "_h", "_fv")

    def __init__(self, name: str, args: Tuple[Term, ...] = ()):
        self.name = name
        self.args = tuple(args)
        self._h = hash(("F", name, self.args))
        self._fv = None

    def __eq__(self, o):
        if self is o:
            return True
        return type(o) is Fn and o._h == self._h and o.name == self.name and o.args == self.args

    def __hash__(self):
        return self._h

    def fv(self):
        if self._fv is None:
            s = frozenset()
            for a in self.args:
                s |= a.fv()
            self._fv = s
        return self._fv

    def __repr__(self):
        return term_str(self)


ZERO = Fn("0", ())


def S(t: Term) -> Term:
    return Fn("S", (t,))


def Add(a: Term, b: Term) -> Term:
    return Fn("+", (a, b))


def Mul(a: Term, b: Term) -> Term:
    return Fn("*", (a, b))


def num(n: int) -> Term:
    """Canonical numeral: the constant 0 for n = 0, the literal Num(n) otherwise."""
    return ZERO if n == 0 else Num(n)


def numeral_unary(n: int) -> Term:
    """S^n(0) without literals (used only for small n)."""
    t: Term = ZERO
    for _ in range(n):
        t = S(t)
    return t


# ---------------------------------------------------------------------------
# Formulas
# ---------------------------------------------------------------------------


class Formula:
    __slots__ = ()

    def fv(self) -> FrozenSet[str]:
        raise NotImplementedError

    def __repr__(self):
        return formula_str(self)


class Bot(Formula):
    __slots__ = ()
    _inst = None

    def __new__(cls):
        if cls._inst is None:
            cls._inst = super().__new__(cls)
        return cls._inst

    def __eq__(self, o):
        return type(o) is Bot

    def __hash__(self):
        return 7

    def fv(self):
        return frozenset()


class Atom(Formula):
    __slots__ = ("pred", "args", "_h", "_fv")

    def __init__(self, pred: str, args: Tuple[Term, ...]):
        self.pred = pred
        self.args = tuple(args)
        self._h = hash(("A", pred, self.args))
        self._fv = None

    def __eq__(self, o):
        return self is o or (type(o) is Atom and o._h == self._h and o.pred == self.pred and o.args == self.args)

    def __hash__(self):
        return self._h

    def fv(self):
        if self._fv is None:
            s = frozenset()
            for a in self.args:
                s |= a.fv()
            self._fv = s
        return self._fv


class _Bin(Formula):
    __slots__ = ("a", "b", "_h", "_fv")
    TAG = "?"

    def __init__(self, a: Formula, b: Formula):
        self.a = a
        self.b = b
        self._h = hash((self.TAG, a, b))
        self._fv = None

    def __eq__(self, o):
        return self is o or (type(o) is type(self) and o._h == self._h and o.a == self.a and o.b == self.b)

    def __hash__(self):
        return self._h

    def fv(self):
        if self._fv is None:
            self._fv = self.a.fv() | self.b.fv()
        return self._fv


class Imp(_Bin):
    __slots__ = ()
    TAG = "->"


class And(_Bin):
    __slots__ = ()
    TAG = "&"


class Or(_Bin):
    __slots__ = ()
    TAG = "|"


class _Quant(Formula):
    __slots__ = ("var", "body", "_h", "_fv")
    TAG = "?"

    def __init__(self, var: str, body: Formula):
        self.var = var
        self.body = body
        self._h = hash((self.TAG, var, body))
        self._fv = None

    def __eq__(self, o):
        return self is o or (
            type(o) is type(self) and o._h == self._h and o.var == self.var and o.body == self.body
        )

    def __hash__(self):
        return self._h

    def fv(self):
        if self._fv is None:
            self._fv = self.body.fv() - {self.var}
        return self._fv


class Forall(_Quant):
    __slots__ = ()
    TAG = "forall"


class Exists(_Quant):
    __slots__ = ()
    TAG = "exists"


BOT = Bot()


def Eq(a: Term, b: Term) -> Atom:
    return Atom("=", (a, b))


def Lt(a: Term, b: Term) -> Atom:
    return Atom("<", (a, b))


def Not(a: Formula) -> Formula:
    return Imp(a, BOT)


def Top() -> Formula:
    return Imp(BOT, BOT)


def Iff(a: Formula, b: Formula) -> Formula:
    return And(Imp(a, b), Imp(b, a))


def is_not(f: Formula) -> bool:
    return type(f) is Imp and type(f.b) is Bot


def forall_many(vs: Iterable[str], body: Formula) -> Formula:
    for v in reversed(list(vs)):
        body = Forall(v, body)
    return body


def exists_many(vs: Iterable[str], body: Formula) -> Formula:
    for v in reversed(list(vs)):
        body = Exists(v, body)
    return body


def conj(fs) -> Formula:
    fs = list(fs)
    if not fs:
        return Top()
    out = fs[-1]
    for f in reversed(fs[:-1]):
        out = And(f, out)
    return out


def disj(fs) -> Formula:
    fs = list(fs)
    if not fs:
        return BOT
    out = fs[-1]
    for f in reversed(fs[:-1]):
        out = Or(f, out)
    return out


def universal_closure(f: Formula) -> Formula:
    return forall_many(sorted(f.fv()), f)


# ---------------------------------------------------------------------------
# Substitution (simultaneous, capture-avoiding)
# ---------------------------------------------------------------------------

_fresh_counter = itertools.count()


def fresh_var(base: str, avoid: Iterable[str]) -> str:
    avoid = set(avoid)
    base = re.sub(r"_\d+$", "", base) or "v"
    if base not in avoid:
        return base
    for i in itertools.count(1):
        cand = f"{base}_{i}"
        if cand not in avoid:
            return cand
    raise AssertionError


def subst_term(t: Term, sigma: Dict[str, Term]) -> Term:
    if not sigma:
        return t
    tt = type(t)
    if tt is Var:
        return sigma.get(t.name, t)
    if tt is Num:
        return t
    if not (t.fv() & sigma.keys()):
        return t
    return Fn(t.name, tuple(subst_term(a, sigma) for a in t.args))


def subst(f: Formula, sigma: Dict[str, Term]) -> Formula:
    """Simultaneous capture-avoiding substitution f[sigma]."""
    if not sigma:
        return f
    relevant = {k: v for k, v in sigma.items() if k in f.fv()}
    if not relevant:
        return f
    return _subst(f, relevant)


def _subst(f: Formula, sigma: Dict[str, Term]) -> Formula:
    tf = type(f)
    if tf is Atom:
        return Atom(f.pred, tuple(subst_term(a, sigma) for a in f.args))
    if tf is Bot:
        return f
    if tf in (Imp, And, Or):
        return tf(subst(f.a, sigma), subst(f.b, sigma))
    if tf in (Forall, Exists):
        x = f.var
        inner = {k: v for k, v in sigma.items() if k != x and k in f.body.fv()}
        if not inner:
            return f
        range_fv = set()
        for v in inner.values():
            range_fv |= v.fv()
        if x in range_fv:
            nx = fresh_var(x, range_fv | f.body.fv() | set(inner.keys()))
            inner = dict(inner)
            inner[x] = Var(nx)
            return tf(nx, subst(f.body, inner))
        return tf(x, subst(f.body, inner))
    raise TypeError(f)


def subst1(f: Formula, x: str, t: Term) -> Formula:
    return subst(f, {x: t})


# ---------------------------------------------------------------------------
# Alpha-equivalence via canonical (de Bruijn) keys
# ---------------------------------------------------------------------------


def _term_key(t: Term, env: Dict[str, int], depth: int):
    tt = type(t)
    if tt is Var:
        lvl = env.get(t.name)
        if lvl is None:
            return ("v", t.name)
        return ("b", depth - lvl)
    if tt is Num:
        return ("n", t.value)
    return ("f", t.name) + tuple(_term_key(a, env, depth) for a in t.args)


def _formula_key(f: Formula, env: Dict[str, int], depth: int):
    tf = type(f)
    if tf is Atom:
        return ("A", f.pred) + tuple(_term_key(a, env, depth) for a in f.args)
    if tf is Bot:
        return ("B",)
    if tf in (Imp, And, Or):
        return (tf.TAG, _formula_key(f.a, env, depth), _formula_key(f.b, env, depth))
    if tf in (Forall, Exists):
        old = env.get(f.var)
        env[f.var] = depth + 1
        k = (tf.TAG, _formula_key(f.body, env, depth + 1))
        if old is None:
            del env[f.var]
        else:
            env[f.var] = old
        return k
    raise TypeError(f)


_KEY_CACHE: Dict[int, tuple] = {}


def alpha_key(f: Formula):
    """Canonical representative of the alpha-equivalence class of f."""
    return _formula_key(f, {}, 0)


def alpha_eq(f: Formula, g: Formula) -> bool:
    if f is g or f == g:
        return True
    return alpha_key(f) == alpha_key(g)


# ---------------------------------------------------------------------------
# Symbols used (for language checking)
# ---------------------------------------------------------------------------


def term_symbols(t: Term, acc=None):
    acc = set() if acc is None else acc
    tt = type(t)
    if tt is Fn:
        acc.add((t.name, len(t.args)))
        for a in t.args:
            term_symbols(a, acc)
    elif tt is Num:
        acc.add(("#num", 0))
    return acc


def formula_symbols(f: Formula, acc=None):
    """Returns (function symbols with arity, predicate symbols with arity)."""
    funcs, preds = (set(), set()) if acc is None else acc
    tf = type(f)
    if tf is Atom:
        preds.add((f.pred, len(f.args)))
        for a in f.args:
            term_symbols(a, funcs)
    elif tf in (Imp, And, Or):
        formula_symbols(f.a, (funcs, preds))
        formula_symbols(f.b, (funcs, preds))
    elif tf in (Forall, Exists):
        formula_symbols(f.body, (funcs, preds))
    return funcs, preds


def formula_size(f: Formula) -> int:
    tf = type(f)
    if tf is Atom:
        return 1 + sum(term_size(a) for a in f.args)
    if tf is Bot:
        return 1
    if tf in (Imp, And, Or):
        return 1 + formula_size(f.a) + formula_size(f.b)
    return 1 + formula_size(f.body)


def term_size(t: Term) -> int:
    if type(t) is Fn:
        return 1 + sum(term_size(a) for a in t.args)
    return 1


def quantifier_depth(f: Formula) -> int:
    tf = type(f)
    if tf in (Atom, Bot):
        return 0
    if tf in (Imp, And, Or):
        return max(quantifier_depth(f.a), quantifier_depth(f.b))
    return 1 + quantifier_depth(f.body)


# ---------------------------------------------------------------------------
# Printing
# ---------------------------------------------------------------------------

_PREC = {"+": 1, "*": 2}


def term_str(t: Term, prec: int = 0) -> str:
    tt = type(t)
    if tt is Var:
        return t.name
    if tt is Num:
        return str(t.value)
    if t.name == "0" and not t.args:
        return "0"
    if t.name == "S" and len(t.args) == 1:
        return f"S({term_str(t.args[0])})"
    if t.name in _PREC and len(t.args) == 2:
        p = _PREC[t.name]
        s = f"{term_str(t.args[0], p)} {t.name} {term_str(t.args[1], p + 1)}"
        return f"({s})" if p < prec else s
    return f"{t.name}({', '.join(term_str(a) for a in t.args)})"


def formula_str(f: Formula, prec: int = 0) -> str:
    tf = type(f)
    if tf is Bot:
        return "False"
    if tf is Atom:
        if len(f.args) == 2:
            return f"{term_str(f.args[0])} {f.pred} {term_str(f.args[1])}"
        return f"{f.pred}({', '.join(term_str(a) for a in f.args)})"
    if tf is Imp and type(f.b) is Bot:
        if type(f.a) is Bot:
            return "True"
        if type(f.a) is Atom and f.a.pred == "=":
            return f"{term_str(f.a.args[0])} != {term_str(f.a.args[1])}"
        return "~" + formula_str(f.a, 4)
    if tf is And and type(f.a) is Imp and type(f.b) is Imp and f.a.a == f.b.b and f.a.b == f.b.a:
        s = f"{formula_str(f.a.a, 1)} <-> {formula_str(f.a.b, 1)}"
        return f"({s})" if prec > 0 else s
    if tf is Imp:
        s = f"{formula_str(f.a, 2)} -> {formula_str(f.b, 1)}"
        return f"({s})" if prec > 1 else s
    if tf is Or:
        s = f"{formula_str(f.a, 2)} | {formula_str(f.b, 2)}"
        return f"({s})" if prec > 2 else s
    if tf is And:
        s = f"{formula_str(f.a, 3)} & {formula_str(f.b, 3)}"
        return f"({s})" if prec > 3 else s
    if tf in (Forall, Exists):
        q = "forall" if tf is Forall else "exists"
        vs = [f.var]
        body = f.body
        while type(body) is tf:
            vs.append(body.var)
            body = body.body
        s = f"{q} {' '.join(vs)}. {formula_str(body, 0)}"
        return f"({s})" if prec > 0 else s
    raise TypeError(f)


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

_TOKEN_RE = re.compile(
    r"\s*(?:(<->|->|!=|<=|>=|[()=<>+*.,~&|])|(\d+)|([A-Za-z_][A-Za-z0-9_']*))"
)


class ParseError(ValueError):
    pass


def _tokenize(s: str):
    pos = 0
    out = []
    s = s.rstrip()
    while pos < len(s):
        m = _TOKEN_RE.match(s, pos)
        if not m or m.end() == pos:
            raise ParseError(f"bad token at {pos}: {s[pos:pos+10]!r}")
        pos = m.end()
        if m.group(1):
            out.append(("op", m.group(1)))
        elif m.group(2):
            out.append(("num", int(m.group(2))))
        else:
            out.append(("id", m.group(3)))
    out.append(("eof", None))
    return out


class _Parser:
    def __init__(self, s: str):
        self.toks = _tokenize(s)
        self.i = 0

    def peek(self):
        return self.toks[self.i]

    def next(self):
        t = self.toks[self.i]
        self.i += 1
        return t

    def expect(self, kind, val=None):
        t = self.next()
        if t[0] != kind or (val is not None and t[1] != val):
            raise ParseError(f"expected {val or kind}, got {t}")
        return t

    def at(self, kind, val=None):
        t = self.peek()
        return t[0] == kind and (val is None or t[1] == val)

    # formulas
    def formula(self):
        lhs = self.imp()
        if self.at("op", "<->"):
            self.next()
            rhs = self.imp()
            return Iff(lhs, rhs)
        return lhs

    def imp(self):
        lhs = self.disj()
        if self.at("op", "->"):
            self.next()
            return Imp(lhs, self.imp())
        return lhs

    def disj(self):
        f = self.conj()
        while self.at("op", "|"):
            self.next()
            f = Or(f, self.conj())
        return f

    def conj(self):
        f = self.unary()
        while self.at("op", "&"):
            self.next()
            f = And(f, self.unary())
        return f

    def unary(self):
        if self.at("op", "~"):
            self.next()
            return Not(self.unary())
        if self.at("id", "forall") or self.at("id", "exists"):
            q = self.next()[1]
            vs = []
            while self.at("id"):
                vs.append(self.next()[1])
            bound = None
            if self.at("op", "<"):
                self.next()
                bound = self.term()
            self.expect("op", ".")
            body = self.formula()
            for v in reversed(vs):
                if q == "forall":
                    body = Forall(v, Imp(Lt(Var(v), bound), body) if bound is not None else body)
                else:
                    body = Exists(v, And(Lt(Var(v), bound), body) if bound is not None else body)
            return body
        if self.at("id", "False"):
            self.next()
            return BOT
        if self.at("id", "True"):
            self.next()
            return Top()
        if self.at("op", "("):
            save = self.i
            self.next()
            try:
                f = self.formula()
                self.expect("op", ")")
                if self.at("op") and self.peek()[1] in ("=", "<", "!=", "<=", ">", ">=", "+", "*"):
                    raise ParseError("term")
                return f
            except ParseError:
                self.i = save
        return self.atom()

    def atom(self):
        lhs = self.term()
        t = self.next()
        if t[0] != "op" or t[1] not in ("=", "<", "!=", "<=", ">", ">="):
            raise ParseError(f"expected relation, got {t}")
        rhs = self.term()
        op = t[1]
        if op == "=":
            return Eq(lhs, rhs)
        if op == "<":
            return Lt(lhs, rhs)
        if op == "!=":
            return Not(Eq(lhs, rhs))
        if op == "<=":
            return Or(Lt(lhs, rhs), Eq(lhs, rhs))
        if op == ">":
            return Lt(rhs, lhs)
        return Or(Lt(rhs, lhs), Eq(rhs, lhs))

    # terms
    def term(self):
        t = self.prod()
        while self.at("op", "+"):
            self.next()
            t = Add(t, self.prod())
        return t

    def prod(self):
        t = self.post()
        while self.at("op", "*"):
            self.next()
            t = Mul(t, self.post())
        return t

    def post(self):
        tok = self.next()
        if tok[0] == "num":
            return num(tok[1])
        if tok[0] == "id":
            if tok[1] == "S":
                if self.at("op", "("):
                    self.next()
                    a = self.term()
                    self.expect("op", ")")
                    return S(a)
                return S(self.post())
            if tok[1] == "Z":
                return ZERO
            return Var(tok[1])
        if tok == ("op", "("):
            t = self.term()
            self.expect("op", ")")
            return t
        raise ParseError(f"unexpected {tok}")


def parse(s: str) -> Formula:
    """Parse a formula.  0 denotes the constant 0, other numerals are Num literals.

    Sugar:  a != b, a <= b, a > b, a >= b, ~f, f <-> g,
            forall x < t. f   (bounded),  exists x < t. f.
    """
    p = _Parser(s)
    f = p.formula()
    p.expect("eof")
    return f


def parse_term(s: str) -> Term:
    p = _Parser(s)
    t = p.term()
    p.expect("eof")
    return t
