"""Provability logic GL: decision procedure with independently checkable certificates.

GL = K + □(□A → A) → □A (Löb).  By Segerberg (1971) GL is sound and complete
for finite transitive irreflexive Kripke frames.  By Solovay (1976) GL is
exactly the set of modal formulas A such that PA ⊢ A* for every arithmetical
realization * that maps □ to PA's standard provability predicate.

Decision procedure: signed tableau with the GL modal rule

    Γ  saturated, F□A ∈ Γ   ⟹   {T B, T □B : T □B ∈ Γ} ∪ {F A, T □A}

(the T □A in the successor encodes converse well-foundedness).  Output:

  * provable     -> a closed tableau (certificate checked by `check_closed_tableau`)
  * not provable -> a finite strict-partial-order countermodel (checked by
                    `check_countermodel`, a 20-line evaluator independent of the tableau)

Formulas are tuples: ('var', name) ('bot',) ('imp', a, b) ('and', a, b) ('or', a, b) ('box', a).
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from functools import lru_cache
from typing import Dict, FrozenSet, List, Optional, Sequence, Set, Tuple

BOT = ("bot",)


def V(name):
    return ("var", name)


def Imp(a, b):
    return ("imp", a, b)


def And(a, b):
    return ("and", a, b)


def Or(a, b):
    return ("or", a, b)


def Box(a):
    return ("box", a)


def Not(a):
    return ("imp", a, BOT)


TOP = Not(BOT)


def Iff(a, b):
    return And(Imp(a, b), Imp(b, a))


def Dia(a):
    return Not(Box(Not(a)))


def boxes(n, a):
    for _ in range(n):
        a = Box(a)
    return a


def con(n=1):
    """Con^n := ¬□^n⊥ (n-fold iterated consistency; Con^1 = Con)."""
    return Not(boxes(n, BOT))


def dbox(a):
    """⊡a := a ∧ □a."""
    return And(a, Box(a))


def show(f) -> str:
    t = f[0]
    if t == "var":
        return f[1]
    if t == "bot":
        return "⊥"
    if t == "imp":
        if f[2] == BOT:
            if f[1] == BOT:
                return "⊤"
            return "¬" + show_atomic(f[1])
        return f"({show(f[1])} → {show(f[2])})"
    if t == "and":
        if f[1][0] == "imp" and f[2][0] == "imp" and f[1][1] == f[2][2] and f[1][2] == f[2][1]:
            return f"({show(f[1][1])} ↔ {show(f[1][2])})"
        return f"({show(f[1])} ∧ {show(f[2])})"
    if t == "or":
        return f"({show(f[1])} ∨ {show(f[2])})"
    if t == "box":
        return "□" + show_atomic(f[1])
    raise ValueError(f)


def show_atomic(f):
    s = show(f)
    return s


def size(f) -> int:
    t = f[0]
    if t in ("var", "bot"):
        return 1
    if t == "box":
        return 1 + size(f[1])
    return 1 + size(f[1]) + size(f[2])


def modal_depth(f) -> int:
    t = f[0]
    if t in ("var", "bot"):
        return 0
    if t == "box":
        return 1 + modal_depth(f[1])
    return max(modal_depth(f[1]), modal_depth(f[2]))


def variables(f) -> Set[str]:
    t = f[0]
    if t == "var":
        return {f[1]}
    if t == "bot":
        return set()
    if t == "box":
        return variables(f[1])
    return variables(f[1]) | variables(f[2])


def substitute(f, p: str, g):
    t = f[0]
    if t == "var":
        return g if f[1] == p else f
    if t == "bot":
        return f
    if t == "box":
        return Box(substitute(f[1], p, g))
    return (t, substitute(f[1], p, g), substitute(f[2], p, g))


def modalized_in(f, p: str, under_box=False) -> bool:
    """Every occurrence of p in f lies within the scope of a □."""
    t = f[0]
    if t == "var":
        return f[1] != p or under_box
    if t == "bot":
        return True
    if t == "box":
        return modalized_in(f[1], p, True)
    return modalized_in(f[1], p, under_box) and modalized_in(f[2], p, under_box)


# ---------------------------------------------------------------------------
# Kripke semantics (independent evaluator)
# ---------------------------------------------------------------------------


@dataclass
class Model:
    worlds: List[int]
    R: Dict[int, FrozenSet[int]]          # successors
    val: Dict[int, FrozenSet[str]]        # true variables
    root: int

    def to_json(self):
        return {"worlds": self.worlds, "R": {w: sorted(s) for w, s in self.R.items()},
                "val": {w: sorted(s) for w, s in self.val.items()}, "root": self.root}


def holds(m: Model, w: int, f) -> bool:
    t = f[0]
    if t == "var":
        return f[1] in m.val[w]
    if t == "bot":
        return False
    if t == "imp":
        return (not holds(m, w, f[1])) or holds(m, w, f[2])
    if t == "and":
        return holds(m, w, f[1]) and holds(m, w, f[2])
    if t == "or":
        return holds(m, w, f[1]) or holds(m, w, f[2])
    if t == "box":
        return all(holds(m, v, f[1]) for v in m.R[w])
    raise ValueError(f)


def check_countermodel(f, m: Model) -> bool:
    """Independent check: m is a finite strict partial order (GL frame) and f fails at the root."""
    ws = set(m.worlds)
    for w in ws:
        if w in m.R[w]:
            return False                     # irreflexive
        if not m.R[w] <= ws:
            return False
        for v in m.R[w]:
            if not m.R[v] <= m.R[w]:
                return False                 # transitive
    return not holds(m, m.root, f)


# ---------------------------------------------------------------------------
# Tableau
# ---------------------------------------------------------------------------

T_, F_ = True, False


@dataclass
class Node:
    gamma: FrozenSet[Tuple[bool, tuple]]
    rule: str                     # 'clash' | 'alpha' | 'beta' | 'gl' | 'open'
    info: tuple = ()
    children: Tuple["Node", ...] = ()


class GL:
    def __init__(self, node_limit: int = 2_000_000):
        self.memo: Dict[FrozenSet, Tuple[bool, object]] = {}
        self.node_limit = node_limit
        self.nodes = 0

    # returns (sat, payload); payload = Model-builder data if sat, closed Node if unsat
    def sat(self, gamma: FrozenSet) -> Tuple[bool, object]:
        if gamma in self.memo:
            return self.memo[gamma]
        self.nodes += 1
        if self.nodes > self.node_limit:
            raise RuntimeError("GL tableau node limit exceeded")
        res = self._sat(gamma)
        self.memo[gamma] = res
        return res

    def _sat(self, g: FrozenSet):
        if (T_, BOT) in g:
            return False, Node(g, "clash", ((T_, BOT),))
        for (s, f) in g:
            if s and (F_, f) in g:
                return False, Node(g, "clash", ((T_, f), (F_, f)))
        # propositional decomposition (deterministic order)
        for sf in sorted(g, key=repr):
            s, f = sf
            t = f[0]
            rest = g - {sf}
            if t == "bot" and not s:
                return self._alpha(g, sf, rest)
            if s and t == "and":
                return self._alpha(g, sf, rest | {(T_, f[1]), (T_, f[2])})
            if not s and t == "or":
                return self._alpha(g, sf, rest | {(F_, f[1]), (F_, f[2])})
            if not s and t == "imp":
                return self._alpha(g, sf, rest | {(T_, f[1]), (F_, f[2])})
            if s and t == "or":
                return self._beta(g, sf, rest | {(T_, f[1])}, rest | {(T_, f[2])})
            if not s and t == "and":
                return self._beta(g, sf, rest | {(F_, f[1])}, rest | {(F_, f[2])})
            if s and t == "imp":
                return self._beta(g, sf, rest | {(F_, f[1])}, rest | {(T_, f[2])})
        # saturated: literals and boxes only
        boxed = [f[1] for (s, f) in g if s and f[0] == "box"]
        succ_models = []
        for (s, f) in sorted(g, key=repr):
            if not s and f[0] == "box":
                a = f[1]
                delta = frozenset([(T_, b) for b in boxed] + [(T_, Box(b)) for b in boxed]
                                  + [(F_, a), (T_, Box(a))])
                ok, payload = self.sat(delta)
                if not ok:
                    return False, Node(g, "gl", ((F_, f),), (payload,))
                succ_models.append(payload)
        return True, ("world", frozenset(f[1] for (s, f) in g if s and f[0] == "var"), tuple(succ_models))

    def _alpha(self, g, sf, new):
        ok, payload = self.sat(frozenset(new))
        if ok:
            return True, payload
        return False, Node(g, "alpha", (sf,), (payload,))

    def _beta(self, g, sf, left, right):
        ok1, p1 = self.sat(frozenset(left))
        if ok1:
            return True, p1
        ok2, p2 = self.sat(frozenset(right))
        if ok2:
            return True, p2
        return False, Node(g, "beta", (sf,), (p1, p2))

    # -- public API -------------------------------------------------------------
    def prove(self, f) -> "GLResult":
        ok, payload = self.sat(frozenset([(F_, f)]))
        if ok:
            return GLResult(f, False, countermodel=build_model(payload))
        return GLResult(f, True, tableau=payload)


def build_model(payload) -> Model:
    worlds: List[int] = []
    R: Dict[int, Set[int]] = {}
    val: Dict[int, FrozenSet[str]] = {}
    counter = itertools.count()

    def mk(p):
        _, v, succs = p
        w = next(counter)
        worlds.append(w)
        val[w] = v
        R[w] = set()
        for s in succs:
            c = mk(s)
            R[w].add(c)
            R[w] |= R[c]
        return w
    root = mk(payload)
    return Model(worlds, {w: frozenset(s) for w, s in R.items()}, val, root)


@dataclass
class GLResult:
    formula: tuple
    provable: bool
    tableau: Optional[Node] = None
    countermodel: Optional[Model] = None

    def verify(self) -> bool:
        if self.provable:
            return check_closed_tableau(self.tableau, frozenset([(F_, self.formula)]))
        return check_countermodel(self.formula, self.countermodel)


def check_closed_tableau(node: Node, expected_root: FrozenSet) -> bool:
    """Independent checker for closed GL tableaux (proof certificates)."""
    if node.gamma != expected_root:
        return False
    seen: Dict[int, bool] = {}

    def ok(n: Node) -> bool:
        if id(n) in seen:
            return seen[id(n)]
        g = n.gamma
        r = False
        if n.rule == "clash":
            if n.info == ((T_, BOT),):
                r = (T_, BOT) in g
            elif len(n.info) == 2:
                (s1, f1), (s2, f2) = n.info
                r = s1 and not s2 and f1 == f2 and (T_, f1) in g and (F_, f1) in g
        elif n.rule in ("alpha", "beta"):
            (sf,) = n.info
            if sf in g:
                s, f = sf
                rest = g - {sf}
                t = f[0]
                if n.rule == "alpha":
                    exp = None
                    if t == "bot" and not s:
                        exp = rest
                    elif s and t == "and":
                        exp = rest | {(T_, f[1]), (T_, f[2])}
                    elif not s and t == "or":
                        exp = rest | {(F_, f[1]), (F_, f[2])}
                    elif not s and t == "imp":
                        exp = rest | {(T_, f[1]), (F_, f[2])}
                    r = exp is not None and len(n.children) == 1 and n.children[0].gamma == exp and ok(n.children[0])
                else:
                    exps = None
                    if s and t == "or":
                        exps = (rest | {(T_, f[1])}, rest | {(T_, f[2])})
                    elif not s and t == "and":
                        exps = (rest | {(F_, f[1])}, rest | {(F_, f[2])})
                    elif s and t == "imp":
                        exps = (rest | {(F_, f[1])}, rest | {(T_, f[2])})
                    r = (exps is not None and len(n.children) == 2
                         and n.children[0].gamma == exps[0] and n.children[1].gamma == exps[1]
                         and ok(n.children[0]) and ok(n.children[1]))
        elif n.rule == "gl":
            ((s, f),) = n.info
            if not s and f[0] == "box" and (F_, f) in g and len(n.children) == 1:
                boxed = [h[1] for (sg, h) in g if sg and h[0] == "box"]
                delta = frozenset([(T_, b) for b in boxed] + [(T_, Box(b)) for b in boxed]
                                  + [(F_, f[1]), (T_, f)])
                r = n.children[0].gamma == delta and ok(n.children[0])
        seen[id(n)] = r
        return r
    return ok(node)


def tableau_size(node: Node) -> int:
    seen = set()
    stack = [node]
    while stack:
        n = stack.pop()
        if id(n) in seen:
            continue
        seen.add(id(n))
        stack.extend(n.children)
    return len(seen)


_ENGINE = GL()


def provable(f) -> bool:
    return _ENGINE.prove(f).provable


def prove(f) -> GLResult:
    return _ENGINE.prove(f)


# ---------------------------------------------------------------------------
# Letterless formulas: traces, normal forms, fixed points
# ---------------------------------------------------------------------------


def letterless_value(f, height: int, memo=None) -> bool:
    """Truth value of a letterless formula at a world of the given height
    (height = length of the longest R-chain above it)."""
    memo = {} if memo is None else memo
    key = (f, height)
    if key in memo:
        return memo[key]
    t = f[0]
    if t == "bot":
        r = False
    elif t == "var":
        raise ValueError("not letterless")
    elif t == "imp":
        r = (not letterless_value(f[1], height, memo)) or letterless_value(f[2], height, memo)
    elif t == "and":
        r = letterless_value(f[1], height, memo) and letterless_value(f[2], height, memo)
    elif t == "or":
        r = letterless_value(f[1], height, memo) or letterless_value(f[2], height, memo)
    elif t == "box":
        r = all(letterless_value(f[1], h, memo) for h in range(height))
    memo[key] = r
    return r


def trace(f, length: Optional[int] = None) -> Tuple[bool, ...]:
    """Truth values at heights 0..length-1; constant from height modal_depth(f) on."""
    n = (modal_depth(f) + 2) if length is None else length
    memo = {}
    return tuple(letterless_value(f, h, memo) for h in range(n))


def value_if_sound(f) -> bool:
    """Arithmetical truth of a letterless sentence under the assumption that the
    theory is sound (then every □^n⊥ is false): the eventual value of the trace."""
    return letterless_value(f, modal_depth(f) + 1)


def height_exactly(h: int):
    # □^{h+1}⊥ ∧ ¬□^h⊥   (□^0⊥ = ⊥)
    return And(boxes(h + 1, BOT), Not(boxes(h, BOT)))


def from_trace(tr: Sequence[bool], tail: bool):
    """Letterless formula with the given values at heights 0..len(tr)-1 and `tail` above."""
    parts = [height_exactly(h) for h, v in enumerate(tr) if v]
    if tail:
        parts.append(Not(boxes(len(tr), BOT)))
    if not parts:
        return BOT
    out = parts[-1]
    for p in reversed(parts[:-1]):
        out = Or(p, out)
    return out


def letterless_fixed_point(A, p: str = "p", max_height: Optional[int] = None):
    """For A(p) with p modalized and no other letters, compute the (unique up to GL-equivalence)
    letterless H with GL ⊢ H ↔ A(H), by induction on height: the value of A(H) at height n only
    depends on H at heights < n.  Returns (H, trace)."""
    if variables(A) - {p}:
        raise ValueError("only p may occur")
    if not modalized_in(A, p):
        raise ValueError("p must be modalized in A")
    d = modal_depth(A) + 2 if max_height is None else max_height
    vals: List[bool] = []
    # evaluate A at height n with p interpreted by vals (heights < n)
    for n in range(d + 1):
        def ev(f, h):
            t = f[0]
            if t == "var":
                return vals[h]          # only reached under a box, so h < n
            if t == "bot":
                return False
            if t == "imp":
                return (not ev(f[1], h)) or ev(f[2], h)
            if t == "and":
                return ev(f[1], h) and ev(f[2], h)
            if t == "or":
                return ev(f[1], h) or ev(f[2], h)
            if t == "box":
                return all(ev(f[1], k) for k in range(h))
            raise ValueError(f)
        vals.append(ev(A, n))
    tail = vals[-1]
    H = from_trace(vals[:-1], tail)
    return H, tuple(vals)


def fixed_point_certificates(A, H, p: str = "p") -> Dict[str, GLResult]:
    """GL certificates that H is a fixed point of A and that it is the unique one."""
    fp = prove(Iff(H, substitute(A, p, H)))
    uniq = prove(Imp(dbox(Iff(V(p), A)), Iff(V(p), H)))
    return {"fixed_point": fp, "uniqueness": uniq}


def min_consistency_for(H, provability: bool) -> Optional[int]:
    """Least n such that GL ⊢ Con^n → ¬□H (provability=True) or Con^n → ¬□¬H.
    None if no such n exists (i.e. the claim is refutable at every height)."""
    target = H if provability else Not(H)
    tr = trace(target, modal_depth(target) + 3)
    for h, v in enumerate(tr):
        if not v:
            return h + 1
    return None
