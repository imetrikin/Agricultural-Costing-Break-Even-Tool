"""Trusted proof checker (the *kernel*).

A deterministic checker for classical first-order natural deduction with
equality, parameterised by a ``Theory`` (language + axioms + axiom schemas).
Proof search code (tactics, agents) only ever *proposes* ``Proof`` objects; a
statement counts as proved only when ``check`` accepts the proof.

Rules (Γ = open assumptions, computed bottom-up; contexts are sets of
formulas up to alpha-equivalence):

    hyp(φ)                          {φ} ⊢ φ
    ax(name, ts)                    ⊢ axiom `name` with its leading ∀s instantiated by ts
    schema(name, params)            ⊢ instance of axiom schema `name`
    lemma(name, ts)                 ⊢ previously *checked* closed theorem, instantiated
    impI(p; φ)                      Γ∖{φ} ⊢ φ → ψ           (p : Γ ⊢ ψ)
    impE(p, q)                      p : φ → ψ, q : φ  ⊢ ψ
    andI(p, q), andE1(p), andE2(p)
    orI1(p; ψ)   : φ ⊢ φ ∨ ψ        orI2(p; φ) : ψ ⊢ φ ∨ ψ
    orE(p, q, r)                    p : φ ∨ ψ, q : χ (discharging φ), r : χ (discharging ψ)
    botE(p; φ)                      p : ⊥  ⊢ φ
    raa(p; φ)                       p : ⊥ (discharging ¬φ) ⊢ φ            (classical)
    allI(p; y)                      p : ψ, y not free in Γ  ⊢ ∀y ψ
    allE(p; t)                      p : ∀x φ  ⊢ φ[t/x]
    exI(p; x, φ, t)                 p : φ[t/x]  ⊢ ∃x φ
    exE(p, q; y)                    p : ∃x φ, q : χ (discharging φ[y/x]); y fresh  ⊢ χ
    refl(t)                         ⊢ t = t
    subst(p, q; x, φ)               p : s = t, q : φ[s/x]  ⊢ φ[t/x]
    compute(t)                      ⊢ t = n   where n is the value of the closed term t
                                    as evaluated by the *implementation* (only if the
                                    implementation enables it; it is an admissible rule
                                    for PA when the evaluator is correct).

The checker is ~250 lines and is the only code whose correctness the
experiment's "VERIFIED" labels depend on (besides the syntax module).  It is
re-implemented independently in ``kernel2.py`` and, for exported proofs,
re-checked by Lean (see lean/).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Dict, Iterable, List, Optional, Tuple

from .syntax import (
    BOT, Atom, Bot, Eq, Exists, Fn, Forall, Formula, Imp, And, Or, Num, Term, Var,
    alpha_eq, alpha_key, formula_symbols, formula_str, num, subst1, term_symbols,
)


class ProofError(Exception):
    """Raised by the kernel when a proof is invalid."""


# ---------------------------------------------------------------------------
# Proof objects
# ---------------------------------------------------------------------------


class Proof:
    __slots__ = ("rule", "prems", "args")

    def __init__(self, rule: str, prems: Tuple["Proof", ...] = (), args: tuple = ()):
        self.rule = rule
        self.prems = tuple(prems)
        self.args = tuple(args)

    def __repr__(self):
        return f"Proof({self.rule}, {len(self.prems)} prems)"


def hyp(f):
    return Proof("hyp", (), (f,))


def ax(name, ts=()):
    return Proof("ax", (), (name, tuple(ts)))


def schema(name, params):
    return Proof("schema", (), (name, tuple(params)))


def lemma(name, ts=()):
    return Proof("lemma", (), (name, tuple(ts)))


def impI(p, f):
    return Proof("impI", (p,), (f,))


def impE(p, q):
    return Proof("impE", (p, q))


def andI(p, q):
    return Proof("andI", (p, q))


def andE1(p):
    return Proof("andE1", (p,))


def andE2(p):
    return Proof("andE2", (p,))


def orI1(p, right):
    return Proof("orI1", (p,), (right,))


def orI2(p, left):
    return Proof("orI2", (p,), (left,))


def orE(p, q, r):
    return Proof("orE", (p, q, r))


def botE(p, f):
    return Proof("botE", (p,), (f,))


def raa(p, f):
    return Proof("raa", (p,), (f,))


def allI(p, y):
    return Proof("allI", (p,), (y,))


def allE(p, t):
    return Proof("allE", (p,), (t,))


def exI(p, x, f, t):
    return Proof("exI", (p,), (x, f, t))


def exE(p, q, y):
    return Proof("exE", (p, q), (y,))


def refl(t):
    return Proof("refl", (), (t,))


def esubst(p, q, x, f):
    return Proof("subst", (p, q), (x, f))


def compute(t):
    return Proof("compute", (), (t,))


# ---------------------------------------------------------------------------
# Theories
# ---------------------------------------------------------------------------


SchemaFn = Callable[["Theory", tuple], Formula]


@dataclass
class Theory:
    name: str
    funcs: Dict[str, int]
    preds: Dict[str, int]
    numerals: bool = True
    axioms: Dict[str, Formula] = field(default_factory=dict)
    schemas: Dict[str, SchemaFn] = field(default_factory=dict)
    description: str = ""

    # -- language -----------------------------------------------------------
    def term_ok(self, t: Term) -> bool:
        for (name, ar) in term_symbols(t):
            if name == "#num":
                if not self.numerals:
                    return False
                continue
            if self.funcs.get(name) != ar:
                return False
        return _no_num0(t)

    def formula_ok(self, f: Formula) -> bool:
        funcs, preds = formula_symbols(f)
        for (name, ar) in funcs:
            if name == "#num":
                if not self.numerals:
                    return False
                continue
            if self.funcs.get(name) != ar:
                return False
        for (name, ar) in preds:
            if self.preds.get(name) != ar:
                return False
        return True

    def require_term(self, t: Term):
        if not self.term_ok(t):
            raise ProofError(f"term {t!r} is not in the language of {self.name}")

    def require_formula(self, f: Formula):
        if not self.formula_ok(f):
            raise ProofError(f"formula {formula_str(f)} is not in the language of {self.name}")

    # -- extension ------------------------------------------------------------
    def extend(self, name: str, new_axioms: Dict[str, Formula], description: str = "") -> "Theory":
        ax = dict(self.axioms)
        for k, v in new_axioms.items():
            if v.fv():
                raise ValueError("axioms must be closed")
            ax[k] = v
        t = Theory(name, dict(self.funcs), dict(self.preds), self.numerals, ax, dict(self.schemas),
                   description or self.description)
        for v in new_axioms.values():
            t.require_formula(v)
        return t

    def axiom_list(self) -> List[Tuple[str, Formula]]:
        return list(self.axioms.items())


def _no_num0(t: Term) -> bool:
    return True  # Num(0) cannot be constructed (see syntax.Num)


# ---------------------------------------------------------------------------
# Library of checked theorems
# ---------------------------------------------------------------------------


class Library:
    """Closed theorems that the kernel has already accepted (by name)."""

    def __init__(self, theory: Theory):
        self.theory = theory
        self.thms: Dict[str, Formula] = {}
        self.proofs: Dict[str, Proof] = {}
        self.order: List[str] = []

    def __contains__(self, name):
        return name in self.thms

    def get(self, name) -> Formula:
        return self.thms[name]


# ---------------------------------------------------------------------------
# Checker
# ---------------------------------------------------------------------------


class Judgment:
    __slots__ = ("hyps", "concl")

    def __init__(self, hyps: Dict[tuple, Formula], concl: Formula):
        self.hyps = hyps
        self.concl = concl


def _instantiate(f: Formula, ts) -> Formula:
    for t in ts:
        if type(f) is not Forall:
            raise ProofError("too many instantiation terms")
        f = subst1(f.body, f.var, t)
    return f


def _union(*ds):
    if len(ds) == 1:
        return ds[0]
    out = {}
    for d in ds:
        out.update(d)
    return out


def _without(d, f):
    k = alpha_key(f)
    if k not in d:
        return d
    d = dict(d)
    del d[k]
    return d


class Checker:
    """Checks proofs against a theory.

    ``evaluator`` (optional) is the implementation's evaluator for closed terms,
    used only by the ``compute`` rule.  ``step_limit`` bounds total work.
    """

    def __init__(self, theory: Theory, library: Optional[Library] = None,
                 evaluator: Optional[Callable[[Term], int]] = None, step_limit: int = 10_000_000):
        self.theory = theory
        self.library = library
        self.evaluator = evaluator
        self.step_limit = step_limit
        self.steps = 0

    def check(self, p: Proof) -> Judgment:
        memo: Dict[int, Judgment] = {}
        # iterative post-order traversal to avoid recursion limits
        stack = [(p, False)]
        keep = []  # keep proof objects alive so ids stay unique
        while stack:
            node, done = stack.pop()
            if id(node) in memo:
                continue
            if not isinstance(node, Proof):
                raise ProofError(f"not a proof object: {node!r}")
            if not done:
                stack.append((node, True))
                for q in node.prems:
                    if id(q) not in memo:
                        stack.append((q, False))
                continue
            self.steps += 1
            if self.steps > self.step_limit:
                raise ProofError("step limit exceeded")
            prem_j = [memo[id(q)] for q in node.prems]
            memo[id(node)] = self._rule(node, prem_j)
            keep.append(node)
        self.last_memo = memo
        return memo[id(p)]

    def check_theorem(self, p: Proof, expected: Optional[Formula] = None) -> Formula:
        j = self.check(p)
        if j.hyps:
            raise ProofError("proof has open assumptions: " +
                             "; ".join(formula_str(f) for f in j.hyps.values()))
        if expected is not None and not alpha_eq(j.concl, expected):
            raise ProofError(f"proof proves {formula_str(j.concl)}, expected {formula_str(expected)}")
        return j.concl

    # -- individual rules ------------------------------------------------------
    def _rule(self, node: Proof, P: List[Judgment]) -> Judgment:
        r = node.rule
        a = node.args
        T = self.theory
        n_prem = {"hyp": 0, "ax": 0, "schema": 0, "lemma": 0, "refl": 0, "compute": 0,
                  "impI": 1, "andE1": 1, "andE2": 1, "orI1": 1, "orI2": 1, "botE": 1, "raa": 1,
                  "allI": 1, "allE": 1, "exI": 1, "impE": 2, "andI": 2, "exE": 2, "subst": 2,
                  "orE": 3}
        if r not in n_prem:
            raise ProofError(f"unknown rule {r}")
        if len(P) != n_prem[r]:
            raise ProofError(f"rule {r} expects {n_prem[r]} premises")

        if r == "hyp":
            (f,) = a
            T.require_formula(f)
            return Judgment({alpha_key(f): f}, f)

        if r == "ax":
            name, ts = a
            if name not in T.axioms:
                raise ProofError(f"{name} is not an axiom of {T.name}")
            for t in ts:
                T.require_term(t)
            return Judgment({}, _instantiate(T.axioms[name], ts))

        if r == "schema":
            name, params = a
            if name not in T.schemas:
                raise ProofError(f"{name} is not an axiom schema of {T.name}")
            f = T.schemas[name](T, params)  # schema functions raise ProofError when invalid
            T.require_formula(f)
            return Judgment({}, f)

        if r == "lemma":
            name, ts = a
            if self.library is None or name not in self.library:
                raise ProofError(f"unknown lemma {name}")
            for t in ts:
                T.require_term(t)
            return Judgment({}, _instantiate(self.library.get(name), ts))

        if r == "refl":
            (t,) = a
            T.require_term(t)
            return Judgment({}, Eq(t, t))

        if r == "compute":
            (t,) = a
            if self.evaluator is None:
                raise ProofError("compute rule disabled in this implementation")
            T.require_term(t)
            if t.fv():
                raise ProofError("compute needs a closed term")
            v = self.evaluator(t)
            return Judgment({}, Eq(t, num(v)))

        if r == "impI":
            (f,) = a
            T.require_formula(f)
            (j,) = P
            return Judgment(_without(j.hyps, f), Imp(f, j.concl))

        if r == "impE":
            j1, j2 = P
            if type(j1.concl) is not Imp:
                raise ProofError("impE: major premise is not an implication")
            if not alpha_eq(j1.concl.a, j2.concl):
                raise ProofError(f"impE: antecedent mismatch {formula_str(j1.concl.a)} vs {formula_str(j2.concl)}")
            return Judgment(_union(j1.hyps, j2.hyps), j1.concl.b)

        if r == "andI":
            j1, j2 = P
            return Judgment(_union(j1.hyps, j2.hyps), And(j1.concl, j2.concl))

        if r in ("andE1", "andE2"):
            (j,) = P
            if type(j.concl) is not And:
                raise ProofError(f"{r}: premise is not a conjunction")
            return Judgment(j.hyps, j.concl.a if r == "andE1" else j.concl.b)

        if r == "orI1":
            (g,) = a
            T.require_formula(g)
            (j,) = P
            return Judgment(j.hyps, Or(j.concl, g))

        if r == "orI2":
            (g,) = a
            T.require_formula(g)
            (j,) = P
            return Judgment(j.hyps, Or(g, j.concl))

        if r == "orE":
            j, jl, jr = P
            if type(j.concl) is not Or:
                raise ProofError("orE: major premise is not a disjunction")
            if not alpha_eq(jl.concl, jr.concl):
                raise ProofError("orE: branches prove different formulas")
            hy = _union(j.hyps, _without(jl.hyps, j.concl.a), _without(jr.hyps, j.concl.b))
            return Judgment(hy, jl.concl)

        if r == "botE":
            (g,) = a
            T.require_formula(g)
            (j,) = P
            if type(j.concl) is not Bot:
                raise ProofError("botE: premise is not falsum")
            return Judgment(j.hyps, g)

        if r == "raa":
            (g,) = a
            T.require_formula(g)
            (j,) = P
            if type(j.concl) is not Bot:
                raise ProofError("raa: premise is not falsum")
            return Judgment(_without(j.hyps, Imp(g, BOT)), g)

        if r == "allI":
            (y,) = a
            (j,) = P
            for h in j.hyps.values():
                if y in h.fv():
                    raise ProofError(f"allI: eigenvariable {y} free in assumption {formula_str(h)}")
            return Judgment(j.hyps, Forall(y, j.concl))

        if r == "allE":
            (t,) = a
            T.require_term(t)
            (j,) = P
            if type(j.concl) is not Forall:
                raise ProofError("allE: premise is not universal")
            return Judgment(j.hyps, subst1(j.concl.body, j.concl.var, t))

        if r == "exI":
            x, f, t = a
            T.require_formula(f)
            T.require_term(t)
            (j,) = P
            if not alpha_eq(j.concl, subst1(f, x, t)):
                raise ProofError(f"exI: premise {formula_str(j.concl)} is not {formula_str(subst1(f, x, t))}")
            return Judgment(j.hyps, Exists(x, f))

        if r == "exE":
            (y,) = a
            j1, j2 = P
            if type(j1.concl) is not Exists:
                raise ProofError("exE: major premise is not existential")
            inst = subst1(j1.concl.body, j1.concl.var, Var(y))
            rest = _without(j2.hyps, inst)
            if y in j2.concl.fv() or y in j1.concl.fv():
                raise ProofError("exE: eigenvariable occurs in conclusion or major premise")
            for h in rest.values():
                if y in h.fv():
                    raise ProofError(f"exE: eigenvariable {y} free in assumption {formula_str(h)}")
            return Judgment(_union(j1.hyps, rest), j2.concl)

        if r == "subst":
            x, f = a
            T.require_formula(f)
            j1, j2 = P
            e = j1.concl
            if not (type(e) is Atom and e.pred == "=" and len(e.args) == 2):
                raise ProofError("subst: first premise is not an equation")
            s, t = e.args
            if not alpha_eq(j2.concl, subst1(f, x, s)):
                raise ProofError(f"subst: second premise {formula_str(j2.concl)} is not {formula_str(subst1(f, x, s))}")
            return Judgment(_union(j1.hyps, j2.hyps), subst1(f, x, t))

        raise ProofError(f"unhandled rule {r}")  # pragma: no cover


def proof_size(p: Proof) -> int:
    seen = set()
    stack = [p]
    while stack:
        n = stack.pop()
        if id(n) in seen:
            continue
        seen.add(id(n))
        stack.extend(n.prems)
    return len(seen)
