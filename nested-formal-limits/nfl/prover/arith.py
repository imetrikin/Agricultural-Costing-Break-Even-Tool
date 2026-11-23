"""Proof-producing arithmetic tactics.

Everything here *builds* kernel proofs; nothing here is trusted.  The main
facility is a constructive Σ1-completeness procedure: every true closed Δ0
sentence gets a kernel proof, every false one gets a kernel refutation, and a
true Σ1 sentence ∃x φ(x) (φ Δ0) gets a proof once a witness is found.

Tactics return pairs (Proof, Formula) where the formula is the *claimed*
conclusion; the claim is only trusted after kernel checking.
"""
from __future__ import annotations

import sys
from typing import Callable, Dict, List, Optional, Tuple

from ..logic import kernel as K
from ..logic.syntax import (
    BOT, ZERO, And, Atom, Bot, Eq, Exists, Fn, Forall, Formula, Imp, Lt, Not, Num, Or, S, Term, Var,
    fresh_var, num, subst1, is_not,
)

sys.setrecursionlimit(max(sys.getrecursionlimit(), 50000))

PF = Tuple[K.Proof, Formula]


class Undecided(Exception):
    pass


# ---------------------------------------------------------------------------
# term utilities
# ---------------------------------------------------------------------------


def replace_term(t: Term, old: Term, new: Term) -> Term:
    if t == old:
        return new
    if type(t) is Fn and t.args:
        return Fn(t.name, tuple(replace_term(a, old, new) for a in t.args))
    return t


def abstract(f: Formula, old: Term, z: str) -> Formula:
    """Replace free occurrences of term `old` in f by Var(z)."""
    tf = type(f)
    if tf is Atom:
        return Atom(f.pred, tuple(replace_term(a, old, Var(z)) for a in f.args))
    if tf is Bot:
        return f
    if tf in (Imp, And, Or):
        return tf(abstract(f.a, old, z), abstract(f.b, old, z))
    if f.var in old.fv():
        return f
    return tf(f.var, abstract(f.body, old, z))


def closed_value(t: Term) -> int:
    """Standard-model value of a closed term (used only to *guide* proof search)."""
    tt = type(t)
    if tt is Num:
        return t.value
    if tt is Var:
        raise ValueError("open term")
    if t.name == "0":
        return 0
    if t.name == "S":
        return closed_value(t.args[0]) + 1
    if t.name == "+":
        return closed_value(t.args[0]) + closed_value(t.args[1])
    if t.name == "*":
        return closed_value(t.args[0]) * closed_value(t.args[1])
    raise ValueError(t.name)


def bounded_forall(f: Formula):
    """Recognise ∀x (x < t → φ) with x not in t; returns (x, t, φ) or None."""
    if type(f) is Forall and type(f.body) is Imp:
        g = f.body.a
        if type(g) is Atom and g.pred == "<" and g.args[0] == Var(f.var) and f.var not in g.args[1].fv():
            return f.var, g.args[1], f.body.b
    return None


def bounded_exists(f: Formula):
    if type(f) is Exists and type(f.body) is And:
        g = f.body.a
        if type(g) is Atom and g.pred == "<" and g.args[0] == Var(f.var) and f.var not in g.args[1].fv():
            return f.var, g.args[1], f.body.b
    return None


def is_delta0(f: Formula) -> bool:
    tf = type(f)
    if tf in (Atom, Bot):
        return True
    if tf in (Imp, And, Or):
        return is_delta0(f.a) and is_delta0(f.b)
    b = bounded_forall(f) or bounded_exists(f)
    if b is None:
        return False
    return is_delta0(b[2])


def classify(f: Formula) -> str:
    """Coarse arithmetical-hierarchy classification of a sentence (syntactic)."""
    if is_delta0(f):
        return "Delta0"
    g = f
    if type(g) is Exists:
        while type(g) is Exists and bounded_exists(g) is None:
            g = g.body
        if is_delta0(g):
            return "Sigma1"
    g = f
    if type(g) is Forall:
        while type(g) is Forall and bounded_forall(g) is None:
            g = g.body
        if is_delta0(g):
            return "Pi1"
        h = g
        while type(h) is Exists and bounded_exists(h) is None:
            h = h.body
        if is_delta0(h):
            return "Pi2"
    return "other"


# ---------------------------------------------------------------------------
# Equality reasoning
# ---------------------------------------------------------------------------


class EqTools:
    Z = "z__"

    def refl(self, t: Term) -> PF:
        return K.refl(t), Eq(t, t)

    def symm(self, pf: PF) -> PF:
        p, e = pf
        s, t = e.args
        z = fresh_var(self.Z, s.fv() | t.fv())
        return K.esubst(p, K.refl(s), z, Eq(Var(z), s)), Eq(t, s)

    def trans(self, pf1: PF, pf2: PF) -> PF:
        (p, e1), (q, e2) = pf1, pf2
        s, t = e1.args
        t2, u = e2.args
        assert t == t2, f"trans mismatch {t} vs {t2}"
        z = fresh_var(self.Z, s.fv() | t.fv() | u.fv())
        return K.esubst(q, p, z, Eq(s, Var(z))), Eq(s, u)

    def chain(self, *pfs: PF) -> PF:
        out = pfs[0]
        for pf in pfs[1:]:
            out = self.trans(out, pf)
        return out

    def congr(self, pf: PF, ctx: Callable[[Term], Term]) -> PF:
        p, e = pf
        s, t = e.args
        avoid = s.fv() | t.fv() | ctx(Var("q__probe")).fv()
        z = fresh_var(self.Z, avoid)
        cs = ctx(s)
        return K.esubst(p, K.refl(cs), z, Eq(cs, ctx(Var(z)))), Eq(cs, ctx(t))

    def rewrite_arg(self, pf_atom: PF, idx: int, pf_eq: PF) -> PF:
        """Rewrite argument `idx` of a proved atom R(t0, t1) using t_idx = u."""
        (p, f), (q, e) = pf_atom, pf_eq
        s, t = e.args
        if s == t:
            return pf_atom
        assert f.args[idx] == s, "rewrite_arg: argument mismatch"
        z = fresh_var(self.Z, f.fv() | s.fv() | t.fv())
        args = list(f.args)
        args[idx] = Var(z)
        phi = Atom(f.pred, tuple(args))
        args[idx] = t
        return K.esubst(q, p, z, phi), Atom(f.pred, tuple(args))

    def transport(self, pf_f: PF, pf_eq: PF) -> PF:
        """From a proof of f[s] and s = t, prove f[t] (all free occurrences of s)."""
        (p, f), (q, e) = pf_f, pf_eq
        s, t = e.args
        z = fresh_var(self.Z, f.fv() | s.fv() | t.fv())
        phi = abstract(f, s, z)
        return K.esubst(q, p, z, phi), subst1(phi, z, t)


# ---------------------------------------------------------------------------
# Ground arithmetic and Δ0 decision with proofs
# ---------------------------------------------------------------------------


class ArithProver(EqTools):
    """Constructive Σ1-completeness for a theory containing Q's axioms and L1, L2.

    If ``use_compute`` the evaluator delegates closed-term evaluation to the
    implementation's ``compute`` rule instead of deriving it from the axioms.
    """

    def __init__(self, theory, use_compute: bool = False):
        self.T = theory
        self.has_mul = "*" in theory.funcs
        self.use_compute = use_compute
        self._add: Dict[Tuple[int, int], PF] = {}
        self._mul: Dict[Tuple[int, int], PF] = {}
        self._neq: Dict[Tuple[int, int], PF] = {}
        self._lt: Dict[Tuple[int, int], PF] = {}
        self._nlt: Dict[Tuple[int, int], PF] = {}

    # -- axioms as PFs --------------------------------------------------------
    def ax(self, name, *ts) -> PF:
        f = self.T.axioms[name]
        for t in ts:
            f = subst1(f.body, f.var, t)
        return K.ax(name, ts), f

    def NUM(self, n: int) -> PF:  # num(n+1) = S(num(n))
        return K.schema("NUM", (n,)), Eq(num(n + 1), S(num(n)))

    def NUMs(self, n: int) -> PF:  # S(num(n)) = num(n+1)
        return self.symm(self.NUM(n))

    # -- closed term evaluation ---------------------------------------------
    def add_num(self, a: int, b: int) -> PF:
        key = (a, b)
        if key in self._add:
            return self._add[key]
        # iterative construction b = 0..b
        start = 0
        for c in range(b, -1, -1):
            if (a, c) in self._add:
                start = c + 1
                break
        for c in range(start, b + 1):
            if c == 0:
                pf = self.ax("Q3_add_zero", num(a))
            else:
                d = c - 1
                e1 = self.congr(self.NUM(d), lambda u, a=a: Fn("+", (num(a), u)))
                e2 = self.ax("Q4_add_succ", num(a), num(d))
                e3 = self.congr(self._add[(a, d)], lambda u: S(u))
                e4 = self.NUMs(a + d)
                pf = self.chain(e1, e2, e3, e4)
            self._add[(a, c)] = pf
        return self._add[key]

    def mul_num(self, a: int, b: int) -> PF:
        key = (a, b)
        if key in self._mul:
            return self._mul[key]
        start = 0
        for c in range(b, -1, -1):
            if (a, c) in self._mul:
                start = c + 1
                break
        for c in range(start, b + 1):
            if c == 0:
                pf = self.ax("Q5_mul_zero", num(a))
            else:
                d = c - 1
                e1 = self.congr(self.NUM(d), lambda u, a=a: Fn("*", (num(a), u)))
                e2 = self.ax("Q6_mul_succ", num(a), num(d))
                e3 = self.congr(self._mul[(a, d)], lambda u, a=a: Fn("+", (u, num(a))))
                e4 = self.add_num(a * d, a)
                pf = self.chain(e1, e2, e3, e4)
            self._mul[(a, c)] = pf
        return self._mul[key]

    def eval_term(self, t: Term) -> Tuple[int, PF]:
        """Returns (n, proof of t = num(n)) for a closed term t."""
        if t.fv():
            raise Undecided("open term")
        if self.use_compute:
            v = closed_value(t)
            return v, (K.compute(t), Eq(t, num(v)))
        tt = type(t)
        if tt is Num:
            return t.value, self.refl(t)
        if t.name == "0":
            return 0, self.refl(t)
        if t.name == "S":
            k, p = self.eval_term(t.args[0])
            return k + 1, self.trans(self.congr(p, lambda u: S(u)), self.NUMs(k))
        if t.name in ("+", "*"):
            a, pa = self.eval_term(t.args[0])
            b, pb = self.eval_term(t.args[1])
            op = t.name
            r = t.args[1]
            e1 = self.congr(pa, lambda u: Fn(op, (u, r)))
            e2 = self.congr(pb, lambda u: Fn(op, (num(a), u)))
            e3 = self.add_num(a, b) if op == "+" else self.mul_num(a, b)
            return (a + b if op == "+" else a * b), self.chain(e1, e2, e3)
        raise Undecided(f"unknown function {t.name}")

    # -- numeral atoms ----------------------------------------------------------
    def neq_num(self, a: int, b: int) -> PF:
        """Proof of ¬(num(a) = num(b)) for a ≠ b."""
        assert a != b
        key = (a, b)
        if key in self._neq:
            return self._neq[key]
        if a > b:
            p_ba = self.neq_num(b, a)
            h = (K.hyp(Eq(num(a), num(b))), Eq(num(a), num(b)))
            hs = self.symm(h)
            res = K.impI(K.impE(p_ba[0], hs[0]), h[1]), Not(h[1])
            self._neq[key] = res
            return res
        # a < b, iterate from (0, b-a) upward
        base_b = b - a
        for i in range(0, a + 1):
            aa, bb = i, base_b + i
            if (aa, bb) in self._neq:
                continue
            h = (K.hyp(Eq(num(aa), num(bb))), Eq(num(aa), num(bb)))
            if aa == 0:
                e = self.trans(h, self.NUM(bb - 1))           # 0 = S(num(bb-1))
                es = self.symm(e)                              # S(num(bb-1)) = 0
                q1 = self.ax("Q1_succ_ne_zero", num(bb - 1))   # ¬(S(num(bb-1)) = 0)
                bot = K.impE(q1[0], es[0])
            else:
                e = self.chain(self.NUMs(aa - 1), h, self.NUM(bb - 1))  # S(aa-1) = S(bb-1)
                q2 = self.ax("Q2_succ_inj", num(aa - 1), num(bb - 1))
                inner = K.impE(q2[0], e[0])                   # num(aa-1) = num(bb-1)
                bot = K.impE(self._neq[(aa - 1, bb - 1)][0], inner)
            self._neq[(aa, bb)] = (K.impI(bot, h[1]), Not(h[1]))
        return self._neq[key]

    def lt_num(self, a: int, b: int) -> PF:
        """Proof of num(a) < num(b) for a < b."""
        assert a < b
        for c in range(a + 1, b + 1):
            if (a, c) in self._lt:
                continue
            m = c - 1
            l2 = self.ax("L2_lt_succ", num(a), num(m))
            back = K.andE2(l2[0])  # (a<m ∨ a=m) → a < S(m)
            left, right = Lt(num(a), num(m)), Eq(num(a), num(m))
            if a == m:
                d = K.orI2(K.refl(num(a)), left)
            else:
                d = K.orI1(self._lt[(a, m)][0], right)
            p = (K.impE(back, d), Lt(num(a), S(num(m))))
            self._lt[(a, c)] = self.rewrite_arg(p, 1, self.NUMs(m))
        return self._lt[(a, b)]

    def nlt_num(self, a: int, b: int) -> PF:
        """Proof of ¬(num(a) < num(b)) for a ≥ b."""
        assert a >= b
        for c in range(0, b + 1):
            if (a, c) in self._nlt:
                continue
            if c == 0:
                self._nlt[(a, c)] = self.ax("L1_not_lt_zero", num(a))
                continue
            m = c - 1
            hf = Lt(num(a), num(c))
            h = (K.hyp(hf), hf)
            h2 = self.rewrite_arg(h, 1, self.NUM(m))  # a < S(m)
            l2 = self.ax("L2_lt_succ", num(a), num(m))
            d = K.impE(K.andE1(l2[0]), h2[0])
            left, right = Lt(num(a), num(m)), Eq(num(a), num(m))
            bl = K.impE(self._nlt[(a, m)][0], K.hyp(left))
            br = K.impE(self.neq_num(a, m)[0], K.hyp(right))
            self._nlt[(a, c)] = (K.impI(K.orE(d, bl, br), hf), Not(hf))
        return self._nlt[(a, b)]

    # -- closed atoms -------------------------------------------------------------
    def decide_atom(self, f: Atom) -> Tuple[bool, PF]:
        s, t = f.args
        a, ps = self.eval_term(s)
        b, pt = self.eval_term(t)
        if f.pred == "=":
            if a == b:
                return True, self.trans(ps, self.symm(pt))
            h = (K.hyp(f), f)
            e = self.chain(self.symm(ps), h, pt)  # num(a) = num(b)
            return False, (K.impI(K.impE(self.neq_num(a, b)[0], e[0]), f), Not(f))
        if f.pred == "<":
            if a < b:
                p = self.lt_num(a, b)
                p = self.rewrite_arg(p, 0, self.symm(ps))
                p = self.rewrite_arg(p, 1, self.symm(pt))
                return True, p
            h = (K.hyp(f), f)
            h2 = self.rewrite_arg(h, 0, ps)
            h3 = self.rewrite_arg(h2, 1, pt)
            return False, (K.impI(K.impE(self.nlt_num(a, b)[0], h3[0]), f), Not(f))
        raise Undecided(f"unknown predicate {f.pred}")

    # -- Δ0 / Σ1 ----------------------------------------------------------------------
    def decide(self, f: Formula, witness_bound: int = 0) -> Tuple[bool, PF]:
        """Decide a closed Δ0 sentence with a kernel proof of it or its negation.

        Unbounded existentials are attempted by witness search up to
        ``witness_bound`` (Σ1 sentences); failure raises Undecided.
        """
        if f.fv():
            raise Undecided("not a sentence")
        tf = type(f)
        if tf is Bot:
            return False, (K.impI(K.hyp(BOT), BOT), Not(BOT))
        if tf is Atom:
            return self.decide_atom(f)
        if tf is Imp:
            va, pa = self.decide(f.a, witness_bound)
            if not va:
                if type(f.b) is Bot:
                    return True, pa
                return True, (K.impI(K.botE(K.impE(pa[0], K.hyp(f.a)), f.b), f.a), f)
            vb, pb = self.decide(f.b, witness_bound)
            if vb:
                return True, (K.impI(pb[0], f.a), f)
            # a true, b false: ¬(a → b)
            return False, (K.impI(K.impE(pb[0], K.impE(K.hyp(f), pa[0])), f), Not(f))
        if tf is And:
            va, pa = self.decide(f.a, witness_bound)
            if not va:
                return False, (K.impI(K.impE(pa[0], K.andE1(K.hyp(f))), f), Not(f))
            vb, pb = self.decide(f.b, witness_bound)
            if not vb:
                return False, (K.impI(K.impE(pb[0], K.andE2(K.hyp(f))), f), Not(f))
            return True, (K.andI(pa[0], pb[0]), f)
        if tf is Or:
            va, pa = self.decide(f.a, witness_bound)
            if va:
                return True, (K.orI1(pa[0], f.b), f)
            vb, pb = self.decide(f.b, witness_bound)
            if vb:
                return True, (K.orI2(pb[0], f.a), f)
            bot = K.orE(K.hyp(f), K.impE(pa[0], K.hyp(f.a)), K.impE(pb[0], K.hyp(f.b)))
            return False, (K.impI(bot, f), Not(f))
        bf = bounded_forall(f)
        if bf is not None:
            x, t, body = bf
            n, pt = self.eval_term(t)
            insts = []
            for k in range(n):
                v, p = self.decide(subst1(body, x, num(k)), witness_bound)
                if not v:
                    # counterexample k
                    lt = self.lt_num(k, n)
                    if t != num(n):
                        lt = self.rewrite_arg(lt, 1, self.symm(pt))
                    h = K.hyp(f)
                    got = K.impE(K.allE(h, num(k)), lt[0])
                    return False, (K.impI(K.impE(p[0], got), f), Not(f))
                insts.append(p)
            return True, self._bounded_all_proof(x, t, n, pt, body, insts)
        be = bounded_exists(f)
        if be is not None:
            x, t, body = be
            n, pt = self.eval_term(t)
            negs = []
            for k in range(n):
                v, p = self.decide(subst1(body, x, num(k)), witness_bound)
                if v:
                    lt = self.lt_num(k, n)
                    if t != num(n):
                        lt = self.rewrite_arg(lt, 1, self.symm(pt))
                    return True, (K.exI(K.andI(lt[0], p[0]), x, f.body, num(k)), f)
                negs.append(p)
            nbody = Not(body)
            pall = self._bounded_all_proof(x, t, n, pt, nbody, negs)
            y = fresh_var("w", f.fv() | {x} | body.fv() | t.fv())
            hy = And(Lt(Var(y), t), subst1(body, x, Var(y)))
            inner = K.impE(K.impE(K.allE(pall[0], Var(y)), K.andE1(K.hyp(hy))), K.andE2(K.hyp(hy)))
            return False, (K.impI(K.exE(K.hyp(f), inner, y), f), Not(f))
        if tf is Exists:
            # unbounded existential: Σ1 witness search
            for k in range(witness_bound + 1):
                try:
                    v, p = self.decide(subst1(f.body, f.var, num(k)), witness_bound)
                except Undecided:
                    continue
                if v:
                    return True, (K.exI(p[0], f.var, f.body, num(k)), f)
            raise Undecided("no witness found")
        raise Undecided("unbounded universal quantifier")

    def _bounded_all_proof(self, x: str, t: Term, n: int, pt: PF, body: Formula, insts: List[PF]) -> PF:
        """Proof of ∀x (x < t → body) from proofs of body[k/x] for k < n, where t = n."""
        xv = Var(x)
        prev = None  # proof of x < num(m) → body
        for m in range(0, n + 1):
            hf = Lt(xv, num(m))
            if m == 0:
                q = self.ax("L1_not_lt_zero", xv)
                cur = K.impI(K.botE(K.impE(q[0], K.hyp(hf)), body), hf)
            else:
                k = m - 1
                h2 = self.rewrite_arg((K.hyp(hf), hf), 1, self.NUM(k))  # x < S(k)
                l2 = self.ax("L2_lt_succ", xv, num(k))
                d = K.impE(K.andE1(l2[0]), h2[0])
                left, right = Lt(xv, num(k)), Eq(xv, num(k))
                bl = K.impE(prev, K.hyp(left))
                # from x = k and body[k] derive body[x]
                eq_kx = self.symm((K.hyp(right), right))       # k = x
                bk = insts[k]
                if x in body.fv():
                    z = fresh_var(self.Z, body.fv() | {x})
                    phi = subst1(body, x, Var(z))
                    br = K.esubst(eq_kx[0], bk[0], z, phi)
                else:
                    br = bk[0]
                cur = K.impI(K.orE(d, bl, br), hf)
            prev = cur
        # prev : x < num(n) → body ; adapt to x < t
        if t != num(n):
            ht = Lt(xv, t)
            h2 = self.rewrite_arg((K.hyp(ht), ht), 1, pt)
            prev = K.impI(K.impE(prev, h2[0]), ht)
        return K.allI(prev, x), Forall(x, Imp(Lt(xv, t), body))
