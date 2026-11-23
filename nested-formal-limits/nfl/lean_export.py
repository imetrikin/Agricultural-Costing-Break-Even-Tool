"""Export Environment-B theories and kernel proofs to Lean (lean/NestedLimits/Replay.lean).

Lean then re-checks, independently of both Python kernels:
  * that each Python axiom of B is literally an `IsAxiom` of the Lean embedding
    (so the parent's Con(B) theorem is about *this* B), and
  * that each exported Python proof is a valid `Derives [] φ` derivation.

Translation: named variables -> de Bruijn indices, contexts carried top-down.
"""
from __future__ import annotations

from typing import Dict, List, Optional, Tuple

from .logic import kernel as K
from .logic.syntax import (
    Atom, Bot, And, Exists, Fn, Forall, Formula, Imp, Num, Or, Term, Var, subst1,
)

AXIOM_CTOR = {
    "Q1_succ_ne_zero": "q1", "Q2_succ_inj": "q2", "Q3_add_zero": "q3", "Q4_add_succ": "q4",
    "Q5_mul_zero": "q5", "Q6_mul_succ": "q6", "L1_not_lt_zero": "l1", "L2_lt_succ": "l2",
}


class Exporter:
    def __init__(self, theory):
        self.T = theory
        self.fdefs: Dict[str, str] = {}      # lean expr -> name
        self.fdef_lines: List[str] = []
        self.cdefs: Dict[Tuple[str, ...], str] = {}
        self.lines: List[str] = []
        self.aux = 0

    # -- de Bruijn translation -------------------------------------------------
    def tm(self, t: Term, env: Dict[str, int]) -> str:
        if isinstance(t, Var):
            if t.name not in env:
                raise KeyError(t.name)
            return f"(Tm.var {env[t.name]})"
        if isinstance(t, Num):
            return f"(Tm.lit {t.value})"
        if t.name == "0":
            return "Tm.zero"
        if t.name == "S":
            return f"(Tm.succ {self.tm(t.args[0], env)})"
        op = {"+": "add", "*": "mul"}[t.name]
        return f"(Tm.{op} {self.tm(t.args[0], env)} {self.tm(t.args[1], env)})"

    def fm(self, f: Formula, env: Dict[str, int]) -> str:
        """Returns the name of a reducible definition of the translated formula."""
        if isinstance(f, Bot):
            e = "Fm.bot"
        elif isinstance(f, Atom):
            op = {"=": "eq", "<": "lt"}[f.pred]
            e = f"(Fm.{op} {self.tm(f.args[0], env)} {self.tm(f.args[1], env)})"
        elif isinstance(f, (Imp, And, Or)):
            op = {Imp: "imp", And: "and", Or: "or"}[type(f)]
            e = f"(Fm.{op} {self.fm(f.a, env)} {self.fm(f.b, env)})"
        else:
            op = "all" if isinstance(f, Forall) else "ex"
            env2 = {k: v + 1 for k, v in env.items()}
            env2[f.var] = 0
            e = f"(Fm.{op} {self.fm(f.body, env2)})"
        if e not in self.fdefs:
            name = f"F{len(self.fdefs)}"
            self.fdefs[e] = name
            self.fdef_lines.append(f"@[reducible] def {name} : Fm := {e}")
        return self.fdefs[e]

    def body(self, q: Formula, env: Dict[str, int]) -> str:
        """For q = ∀x φ / ∃x φ: the de Bruijn body φ (x ↦ 0)."""
        env2 = {k: v + 1 for k, v in env.items()}
        env2[q.var] = 0
        return self.fm(q.body, env2)

    def ctx(self, names: Tuple[str, ...]) -> str:
        if names not in self.cdefs:
            name = f"C{len(self.cdefs)}"
            self.cdefs[names] = name
            self.fdef_lines.append(f"@[reducible] def {name} : List Fm := [{', '.join(names)}]")
        return self.cdefs[names]

    # -- proofs -------------------------------------------------------------------------
    def export_theorem(self, name: str, proof: K.Proof, statement: Formula, library: Optional[K.Library]):
        chk = K.Checker(self.T, library)
        chk.check_theorem(proof, statement)
        memo = chk.last_memo
        names = set()
        stack = [proof]
        seen = set()
        while stack:
            n = stack.pop()
            if id(n) in seen:
                continue
            seen.add(id(n))
            stack.extend(n.prems)
            for a in n.args:
                if isinstance(a, Formula) or isinstance(a, Term):
                    names |= a.fv()
                if isinstance(a, str) and n.rule in ("allI", "exE"):
                    names.add(a)
            if n.rule == "schema" and n.args[0] == "IND":
                names |= n.args[1][1].fv() | {n.args[1][0]}
            names |= memo[id(n)].concl.fv()
            for h in memo[id(n)].hyps.values():
                names |= h.fv()
        env = {v: i for i, v in enumerate(sorted(names))}
        self._closed_cache: Dict[int, str] = {}
        term = self.node(proof, (), env, memo, library)
        stmt = self.fm(statement, {})
        self.lines.append(f"theorem {name} : Derives [] {stmt} :=\n  {term}\n")

    def node(self, n: K.Proof, ctx: Tuple[Tuple[str, Formula], ...], env: Dict[str, int], memo, library) -> str:
        """ctx: tuple of (lean name of the formula under env, named formula)."""
        j = memo[id(n)]
        C = self.ctx(tuple(nm for nm, _ in ctx))
        # closed sub-derivations without free variables: export once as an auxiliary theorem
        if not j.hyps and not j.concl.fv() and ctx and n.rule not in ("hyp", "refl"):
            if id(n) not in self._closed_cache:
                aux = f"aux{self.aux}"
                self.aux += 1
                body = self.node(n, (), env, memo, library)
                self.lines.append(f"theorem {aux} : Derives [] {self.fm(j.concl, {})} :=\n  {body}\n")
                self._closed_cache[id(n)] = aux
            return f"(@Derives.ofNil {C} {self.fm(j.concl, env)} {self._closed_cache[id(n)]})"
        r, a, P = n.rule, n.args, n.prems
        c = lambda q: memo[id(q)].concl
        if r == "hyp":
            f = self.fm(a[0], env)
            idx = [nm for nm, _ in ctx].index(f)
            mem = "(List.Mem.head _)"
            for _ in range(idx):
                mem = f"(List.Mem.tail _ {mem})"
            return f"(@Derives.hyp {C} {f} {mem})"
        if r in ("ax", "lemma"):
            name, ts = a
            if r == "ax":
                F = self.T.axioms[name]
                out = f"(@Derives.ax {C} {self.fm(F, {})} IsAxiom.{AXIOM_CTOR[name]})"
            else:
                F = library.get(name)
                out = f"(@Derives.ofNil {C} {self.fm(F, {})} L_{name})"
            for t in ts:
                out = f"(@Derives.allE {C} {self.body(F, env)} {self.tm(t, env)} {out})"
                F = subst1(F.body, F.var, t)
            return out
        if r == "schema":
            name, params = a
            if name == "IND":
                x, phi = params
                env2 = {k: v + 1 for k, v in env.items()}
                env2[x] = 0
                psi = self.fm(phi, env2)
                return f"(@Derives.ax {C} {self.fm(j.concl, env)} (IsAxiom.ind {psi}))"
            if name == "NUM":
                return f"(@Derives.ax {C} {self.fm(j.concl, env)} (IsAxiom.numAx {params[0]}))"
            raise ValueError(name)
        if r == "refl":
            return f"(@Derives.refl {C} {self.tm(a[0], env)})"
        if r == "impI":
            f = self.fm(a[0], env)
            return f"(@Derives.impI {C} {f} {self.fm(c(P[0]), env)} {self.node(P[0], ((f, a[0]),) + ctx, env, memo, library)})"
        if r == "impE":
            imp = c(P[0])
            return (f"(@Derives.impE {C} {self.fm(imp.a, env)} {self.fm(imp.b, env)} "
                    f"{self.node(P[0], ctx, env, memo, library)} {self.node(P[1], ctx, env, memo, library)})")
        if r == "andI":
            return (f"(@Derives.andI {C} {self.fm(c(P[0]), env)} {self.fm(c(P[1]), env)} "
                    f"{self.node(P[0], ctx, env, memo, library)} {self.node(P[1], ctx, env, memo, library)})")
        if r in ("andE1", "andE2"):
            cj = c(P[0])
            return (f"(@Derives.{r} {C} {self.fm(cj.a, env)} {self.fm(cj.b, env)} "
                    f"{self.node(P[0], ctx, env, memo, library)})")
        if r == "orI1":
            return (f"(@Derives.orI1 {C} {self.fm(c(P[0]), env)} {self.fm(a[0], env)} "
                    f"{self.node(P[0], ctx, env, memo, library)})")
        if r == "orI2":
            return (f"(@Derives.orI2 {C} {self.fm(a[0], env)} {self.fm(c(P[0]), env)} "
                    f"{self.node(P[0], ctx, env, memo, library)})")
        if r == "orE":
            d = c(P[0])
            fa, fb = self.fm(d.a, env), self.fm(d.b, env)
            return (f"(@Derives.orE {C} {fa} {fb} {self.fm(j.concl, env)} {self.node(P[0], ctx, env, memo, library)} "
                    f"{self.node(P[1], ((fa, d.a),) + ctx, env, memo, library)} "
                    f"{self.node(P[2], ((fb, d.b),) + ctx, env, memo, library)})")
        if r == "botE":
            return f"(@Derives.botE {C} {self.fm(a[0], env)} {self.node(P[0], ctx, env, memo, library)})"
        if r == "raa":
            nfo = Imp(a[0], Bot())
            nf = self.fm(nfo, env)
            return f"(@Derives.raa {C} {self.fm(a[0], env)} {self.node(P[0], ((nf, nfo),) + ctx, env, memo, library)})"
        if r == "allI":
            y = a[0]
            env2 = {k: v + 1 for k, v in env.items()}
            env2[y] = 0
            sctx = tuple((self.fm(f, env2), f) for _, f in ctx)
            return (f"(@Derives.allI {C} {self.fm(c(P[0]), env2)} "
                    f"{self.node(P[0], sctx, env2, memo, library)})")
        if r == "allE":
            q = c(P[0])
            return (f"(@Derives.allE {C} {self.body(q, env)} {self.tm(a[0], env)} "
                    f"{self.node(P[0], ctx, env, memo, library)})")
        if r == "exI":
            x, phi, t = a
            return (f"(@Derives.exI {C} {self.body(Exists(x, phi), env)} {self.tm(t, env)} "
                    f"{self.node(P[0], ctx, env, memo, library)})")
        if r == "exE":
            q = c(P[0])
            y = a[0]
            env2 = {k: v + 1 for k, v in env.items()}
            env2[y] = 0
            insto = subst1(q.body, q.var, Var(y))
            sctx = ((self.fm(insto, env2), insto),) + tuple((self.fm(f, env2), f) for _, f in ctx)
            return (f"(@Derives.exE {C} {self.body(q, env)} {self.fm(j.concl, env)} "
                    f"{self.node(P[0], ctx, env, memo, library)} {self.node(P[1], sctx, env2, memo, library)})")
        if r == "subst":
            x, phi = a
            s, t = c(P[0]).args
            env2 = {k: v + 1 for k, v in env.items()}
            env2[x] = 0
            return (f"(@Derives.subst {C} {self.fm(phi, env2)} {self.tm(s, env)} {self.tm(t, env)} "
                    f"{self.node(P[0], ctx, env, memo, library)} {self.node(P[1], ctx, env, memo, library)})")
        raise ValueError(f"cannot export rule {r}")

    def _shift_name(self, fname: str) -> str:
        """Name of the definition for (Fm.shift F) -- emitted as a reducible def."""
        e = f"(Fm.shift {fname})"
        if e not in self.fdefs:
            name = f"F{len(self.fdefs)}"
            self.fdefs[e] = name
            self.fdef_lines.append(f"@[reducible] def {name} : Fm := {e}")
        return self.fdefs[e]

    def axiom_checks(self) -> List[str]:
        out = []
        for name, ctor in AXIOM_CTOR.items():
            if name in self.T.axioms:
                out.append(f"example : IsAxiom {self.fm(self.T.axioms[name], {})} := IsAxiom.{ctor}")
        return out

    def render(self, header: str = "") -> str:
        ax = self.axiom_checks()
        return "\n".join([
            "/- AUTO-GENERATED by nfl/lean_export.py -- do not edit.",
            header,
            "-/",
            "import NestedLimits.Proofs",
            "set_option maxRecDepth 100000",
            "set_option maxHeartbeats 0",
            "namespace NL",
            "",
            *self.fdef_lines,
            "",
            "/-! The Python axioms of B are literally the Lean axioms: -/",
            *ax,
            "",
            "/-! Proofs found by the Python agents, replayed: -/",
            *self.lines,
            "end NL",
            "",
        ])
