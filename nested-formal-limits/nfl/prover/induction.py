"""Rewriting + structural induction prover for universal equations.

A small Boyer-Moore-style prover: terms are normalised with oriented
equations (axioms, previously proved lemmas, induction hypotheses), using the
lexicographic path ordering (LPO) to orient rules and *ordered rewriting* for
permutative rules such as commutativity.  Goals that do not normalise to the
same term are attacked by induction on a variable; stuck subgoals are offered
as lemma candidates.  Every success yields a kernel proof (never trusted
until the kernel accepts it).
"""
from __future__ import annotations

import itertools
import random
from dataclasses import dataclass, field
from typing import Callable, Dict, List, Optional, Sequence, Tuple

from ..logic import kernel as K
from ..logic.syntax import (
    ZERO, Atom, Eq, Fn, Forall, Formula, Num, S, Term, Var, forall_many, fresh_var, num, subst1,
    subst_term, term_size,
)
from .arith import EqTools, PF, closed_value

PREC = {"*": 4, "+": 3, "S": 2, "#num": 1, "0": 0}


class SearchFailure(Exception):
    def __init__(self, msg, stuck=None):
        super().__init__(msg)
        self.stuck = stuck or []


class Budget:
    def __init__(self, steps: int):
        self.left = steps
        self.used = 0

    def spend(self, n=1):
        self.left -= n
        self.used += n
        if self.left < 0:
            raise SearchFailure("budget exhausted")


# ---------------------------------------------------------------------------
# Orderings and matching
# ---------------------------------------------------------------------------


def _sym(t: Term):
    if type(t) is Num:
        return "#num"
    return t.name


def _args(t: Term):
    return t.args if type(t) is Fn else ()


def occurs(v: Var, t: Term) -> bool:
    return v.name in t.fv()


def lpo_gt(s: Term, t: Term, ground: bool = False) -> bool:
    """s >_lpo t.  With ground=True variables are treated as minimal constants
    ordered by name (a total order used for ordered rewriting)."""
    if s == t:
        return False
    if type(t) is Var:
        if type(s) is Var:
            return ground and s.name > t.name
        return True if ground else occurs(t, s)
    if type(s) is Var:
        return False
    if type(s) is Num and type(t) is Num:
        return s.value > t.value
    sa, ta = _args(s), _args(t)
    if any(si == t or lpo_gt(si, t, ground) for si in sa):
        return True
    fs, ft = _sym(s), _sym(t)
    ps, pt = PREC.get(fs, 5), PREC.get(ft, 5)
    if ps > pt or (fs == "#num" and ft != "#num" and type(t) is not Num and ft in ("S", "0")):
        return all(lpo_gt(s, tj, ground) for tj in ta)
    if fs == ft and len(sa) == len(ta):
        for i, (si, ti) in enumerate(zip(sa, ta)):
            if si != ti:
                return lpo_gt(si, ti, ground) and all(lpo_gt(s, tj, ground) for tj in ta[i + 1:])
        return False
    return False


def match(pat: Term, t: Term, pvars: frozenset, sigma: Dict[str, Term]) -> Optional[Dict[str, Term]]:
    tp = type(pat)
    if tp is Var and pat.name in pvars:
        if pat.name in sigma:
            return sigma if sigma[pat.name] == t else None
        sigma = dict(sigma)
        sigma[pat.name] = t
        return sigma
    if tp is Var or tp is Num:
        return sigma if pat == t else None
    if type(t) is not Fn or t.name != pat.name or len(t.args) != len(pat.args):
        return None
    for pa, ta in zip(pat.args, t.args):
        sigma = match(pa, ta, pvars, sigma)
        if sigma is None:
            return None
    return sigma


# ---------------------------------------------------------------------------
# Rules
# ---------------------------------------------------------------------------


@dataclass
class Rule:
    name: str
    pvars: Tuple[str, ...]           # pattern variables, in quantifier order
    lhs: Term
    rhs: Term
    instance: Callable[[Dict[str, Term]], PF]   # proof of lhs[σ] = rhs[σ]
    ordered: bool = False            # apply only if the instance decreases (ground LPO)


def rules_from_equation(name: str, formula: Formula, proof_of: Callable[[Sequence[Term]], K.Proof],
                        tools: EqTools) -> List[Rule]:
    """Turn a closed theorem ∀v̄ (a = b) into rewrite rules (oriented by LPO)."""
    vs = []
    f = formula
    while type(f) is Forall:
        vs.append(f.var)
        f = f.body
    if not (type(f) is Atom and f.pred == "="):
        return []
    a, b = f.args
    pv = frozenset(vs)

    def fwd(sig, vs=vs, a=a, b=b):
        ts = [sig.get(v, Var(v)) for v in vs]
        return proof_of(ts), Eq(subst_term(a, sig), subst_term(b, sig))

    def bwd(sig):
        return tools.symm(fwd(sig))

    out = []
    if lpo_gt(a, b) and b.fv() <= a.fv():
        out.append(Rule(name, tuple(vs), a, b, fwd))
    elif lpo_gt(b, a) and a.fv() <= b.fv():
        out.append(Rule(name + "^-1", tuple(vs), b, a, bwd))
    elif a.fv() == b.fv() and type(a) is Fn:
        out.append(Rule(name, tuple(vs), a, b, fwd, ordered=True))
        if type(b) is Fn:
            out.append(Rule(name + "^-1", tuple(vs), b, a, bwd, ordered=True))
    return out


# ---------------------------------------------------------------------------
# Normaliser
# ---------------------------------------------------------------------------


class Normalizer:
    def __init__(self, rules: List[Rule], tools: EqTools, budget: Budget, unfold_numerals: bool = True):
        self.rules = rules
        self.tools = tools
        self.budget = budget
        self.unfold = unfold_numerals
        self.cache: Dict[Term, Tuple[Term, Optional[PF]]] = {}
        self.by_head: Dict[str, List[Rule]] = {}
        for r in rules:
            self.by_head.setdefault(_sym(r.lhs) if type(r.lhs) is not Var else "*var*", []).append(r)

    def _chain(self, p: Optional[PF], q: Optional[PF]) -> Optional[PF]:
        if p is None:
            return q
        if q is None:
            return p
        return self.tools.trans(p, q)

    def norm(self, t: Term) -> Tuple[Term, Optional[PF]]:
        """Returns (normal form, proof of t = nf or None if unchanged)."""
        if t in self.cache:
            return self.cache[t]
        self.budget.spend()
        res = self._norm(t)
        self.cache[t] = res
        return res

    def _norm(self, t: Term):
        tt = type(t)
        if tt is Var:
            return t, None
        if tt is Num:
            if self.unfold and t.value <= 64:
                n = t.value - 1
                step = (K.schema("NUM", (n,)), Eq(t, S(num(n))))
                t2, p2 = self.norm(S(num(n)))
                return t2, self._chain(step, p2)
            return t, None
        # normalise arguments
        args = list(t.args)
        proof = None
        cur = t
        for i in range(len(args)):
            ai, pi = self.norm(args[i])
            if pi is not None:
                fixed = list(args)

                def ctx(u, i=i, fixed=fixed, name=t.name):
                    a2 = list(fixed)
                    a2[i] = u
                    return Fn(name, tuple(a2))
                proof = self._chain(proof, self.tools.congr(pi, ctx))
                args[i] = ai
                cur = Fn(t.name, tuple(args))
        # rewrite at root
        for r in self.by_head.get(t.name, []):
            sig = match(r.lhs, cur, frozenset(r.pvars), {})
            if sig is None:
                continue
            rhs = subst_term(r.rhs, sig)
            if r.ordered and not lpo_gt(cur, rhs, ground=True):
                continue
            step = r.instance(sig)
            assert step[1].args[0] == cur, (r.name, step[1], cur)
            t2, p2 = self.norm(rhs)
            return t2, self._chain(self._chain(proof, step), p2)
        return cur, proof


# ---------------------------------------------------------------------------
# Induction prover
# ---------------------------------------------------------------------------


def recursion_positions(t: Term, acc=None) -> Dict[str, int]:
    """Count occurrences of variables in recursive (second) argument positions."""
    acc = {} if acc is None else acc
    if type(t) is Fn:
        if t.name in ("+", "*") and type(t.args[1]) is Var:
            acc[t.args[1].name] = acc.get(t.args[1].name, 0) + 1
        for a in t.args:
            recursion_positions(a, acc)
    return acc


@dataclass
class Attempt:
    goal: str
    success: bool
    steps: int
    reason: str = ""
    stuck: List[str] = field(default_factory=list)


class InductionProver(EqTools):
    def __init__(self, theory, library: K.Library, max_depth: int = 2):
        self.T = theory
        self.lib = library
        self.max_depth = max_depth
        self.base_rules: List[Rule] = []
        for name in ("Q3_add_zero", "Q4_add_succ", "Q5_mul_zero", "Q6_mul_succ"):
            if name in theory.axioms:
                self.base_rules += rules_from_equation(
                    name, theory.axioms[name], lambda ts, name=name: K.ax(name, ts), self)
        self.lemma_rules: List[Rule] = []

    def add_lemma_rules(self, name: str):
        f = self.lib.get(name)
        self.lemma_rules += rules_from_equation(name, f, lambda ts, name=name: K.lemma(name, ts), self)

    # -- main entry -----------------------------------------------------------------
    def prove(self, lhs: Term, rhs: Term, vars_order: Sequence[str], budget: Budget) -> PF:
        """Prove ∀vars_order (lhs = rhs)."""
        pf = self._prove(lhs, rhs, list(vars_order), [], budget, 0)
        return pf

    def _rules(self, extra):
        # induction hypotheses first, then axioms, then lemmas (oriented ones before permutative)
        lem = [r for r in self.lemma_rules if not r.ordered] + [r for r in self.lemma_rules if r.ordered]
        return extra + self.base_rules + lem

    def _prove(self, lhs, rhs, vs, extra_rules, budget, depth) -> PF:
        # 1. normalisation
        nm = Normalizer(self._rules(extra_rules), self, budget)
        nl, pl = nm.norm(lhs)
        nr, pr = nm.norm(rhs)
        if nl == nr:
            eq = self._join(lhs, rhs, pl, pr)
            return self._generalize(eq, vs)
        if depth >= self.max_depth:
            raise SearchFailure("stuck", stuck=[(nl, nr)])
        # 2. induction
        rp = recursion_positions(Fn("+", (nl, nr)))
        cands = sorted(vs, key=lambda v: -rp.get(v, 0))
        cands = [v for v in cands if rp.get(v, 0) > 0] or list(vs)
        stuck = [(nl, nr)]
        for x in cands:
            try:
                ind = self._induct(nl, nr, vs, x, extra_rules, budget, depth)
            except SearchFailure as e:
                stuck += e.stuck
                if budget.left <= 0:
                    break
                continue
            # connect: lhs = nl = nr = rhs
            p, f = ind
            for v in vs:
                p = K.allE(p, Var(v))
                f = subst1(f.body, f.var, Var(v))
            mid = (p, f)
            eq = mid
            if pl is not None:
                eq = self.trans(pl, eq)
            if pr is not None:
                eq = self.trans(eq, self.symm(pr))
            return self._generalize(eq, vs)
        raise SearchFailure("no induction succeeded", stuck=stuck)

    def _join(self, lhs, rhs, pl, pr) -> PF:
        if pl is None and pr is None:
            return self.refl(lhs)
        if pr is None:
            return pl
        if pl is None:
            return self.symm(pr)
        return self.trans(pl, self.symm(pr))

    def _generalize(self, eq: PF, vs: Sequence[str]) -> PF:
        p, f = eq
        for v in reversed(vs):
            p = K.allI(p, v)
            f = Forall(v, f)
        return p, f

    def _induct(self, lhs, rhs, vs, x, extra_rules, budget, depth) -> PF:
        others = [v for v in vs if v != x]
        phi = forall_many(others, Eq(lhs, rhs))
        xv = Var(x)
        # base case
        l0, r0 = subst_term(lhs, {x: ZERO}), subst_term(rhs, {x: ZERO})
        base = self._prove(l0, r0, others, extra_rules, budget, depth + 1)
        # step case with IH
        ih_hyp = K.hyp(phi)

        def ih_inst(sig, others=others, ih_hyp=ih_hyp, phi=phi):
            p = ih_hyp
            f = phi
            for v in others:
                t = sig.get(v, Var(v))
                p = K.allE(p, t)
                f = subst1(f.body, f.var, t)
            return p, f

        ih_rules = []
        if lpo_gt(lhs, rhs, ground=True):
            ih_rules.append(Rule("IH", tuple(others), lhs, rhs, ih_inst, ordered=True))
        else:
            ih_rules.append(Rule("IH^-1", tuple(others), rhs, lhs, lambda s: self.symm(ih_inst(s)),
                                 ordered=True))
        ls, rs = subst_term(lhs, {x: S(xv)}), subst_term(rhs, {x: S(xv)})
        step_eq = self._prove(ls, rs, others, extra_rules + ih_rules, budget, depth + 1)
        step = K.allI(K.impI(step_eq[0], phi), x)
        ind = K.schema("IND", (x, phi))
        proof = K.impE(ind, K.andI(base[0], step))
        concl = Forall(x, phi)
        return self._reorder((proof, concl), [x] + others, vs)

    def _reorder(self, pf: PF, have: Sequence[str], want: Sequence[str]) -> PF:
        if list(have) == list(want):
            return pf
        p, f = pf
        for v in have:
            p = K.allE(p, Var(v))
            f = subst1(f.body, f.var, Var(v))
        return self._generalize((p, f), want)


# ---------------------------------------------------------------------------
# Empirical testing
# ---------------------------------------------------------------------------


def holds_on_samples(lhs: Term, rhs: Term, vs: Sequence[str], n_max: int = 6, samples: int = 0,
                     rng: Optional[random.Random] = None) -> bool:
    if samples and rng is not None:
        assigns = [{v: num(rng.randint(0, 30)) for v in vs} for _ in range(samples)]
    else:
        assigns = [dict(zip(vs, map(num, vals))) for vals in itertools.product(range(n_max), repeat=len(vs))]
    for sig in assigns:
        if closed_value(subst_term(lhs, sig)) != closed_value(subst_term(rhs, sig)):
            return False
    return True
