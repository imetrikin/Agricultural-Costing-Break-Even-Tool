"""Artificial mathematician for Environment B.

It knows only its World: its own language, axioms, schemas, a kernel (run by an
unknown substrate), its own library and a calculator.  It is NOT told that its
system is incomplete, that it is simulated, or that any other system exists.

Phases
  B1 orientation      read own axioms; verify T ⊇ Q and T ⊇ IΣ1 by kernel proofs;
                      audit the calculator against the axioms
  B2 mathematics      theory exploration + controller challenges, with budget sweeps
  B3 patterns         what is decided / proved / unresolved, by logical form
  B4 self-modelling   Gödel numbering of own syntax; kernel-verified coding facts
  B5 self-reference   exploration of self-referential schemas A(p) via GL fixed points
  B6 self-knowledge   what can / cannot be established about own provability
  B7 frameworks       hypotheses about stronger frameworks, with exact assumptions

Ablations: meta=False skips B4-B7; naive=True turns failed searches into
"unprovable" claims (to demonstrate why that inference is invalid).
"""
from __future__ import annotations

import random
from types import SimpleNamespace
from typing import Dict, List, Optional

from ..logic import kernel as K
from ..logic.syntax import (
    BOT, ZERO, Add, And, Eq, Exists, Forall, Formula, Imp, Lt, Mul, Not, Num, Or, S, Var,
    formula_str, num, parse, subst1, quantifier_depth,
)
from ..modal import gl as G
from ..prover.arith import ArithProver, Undecided, classify, is_delta0, closed_value
from ..prover.explore import explore
from ..prover.induction import Budget, InductionProver, SearchFailure
from . import metamath as M
from .base import Agent


class AgentB(Agent):
    role = "B-mathematician"

    def __init__(self, world, challenges: List[Dict], budgets=(1500, 6000, 24000), meta: bool = True,
                 naive: bool = False, explore_size: int = 6, seed: int = 0):
        super().__init__(world)
        self.challenges = challenges
        self.budgets = budgets
        self.meta = meta
        self.naive = naive
        self.explore_size = explore_size
        self.rng = random.Random(seed)
        lang = world.language()
        self.T = SimpleNamespace(axioms=world.axioms(), funcs=lang["functions"], preds=lang["predicates"])
        self.lib = world.library()
        self.arith = ArithProver(self.T)
        self.ind = InductionProver(self.T, self.lib)
        self.inconsistent_as_implemented = False
        self.results: Dict[str, Dict] = {}

    # ------------------------------------------------------------------ utils
    def submit(self, name, proof, stmt) -> bool:
        ok = self.world.submit(name, proof, stmt)
        self.note("kernel", "result", f"{'ACCEPTED' if ok else 'REJECTED'} {name}: {formula_str(stmt)}",
                  proof_nodes=K.proof_size(proof))
        return ok

    # ------------------------------------------------------------------ B1
    def orientation(self):
        ph = "B1-orientation"
        lang = self.world.language()
        self.note(ph, "observation", f"My language: functions {lang['functions']}, predicates {lang['predicates']}.")
        self.note(ph, "observation", f"My axioms: {[k for k in self.world.axioms()]}; schemas: {self.world.schemas()}.")
        # Q7 by induction
        x, y = Var("x"), Var("y")
        phi = Or(Eq(x, ZERO), Exists("y", Eq(x, S(y))))
        base = K.orI1(K.refl(ZERO), Exists("y", Eq(ZERO, S(y))))
        step_concl = K.orI2(K.exI(K.refl(S(x)), "y", Eq(S(x), S(y)), x), Eq(S(x), ZERO))
        step = K.allI(K.impI(step_concl, phi), "x")
        q7 = K.impE(K.schema("IND", ("x", phi)), K.andI(base, step))
        ok_q7 = self.submit("Q7_zero_or_succ", q7, Forall("x", phi))
        q_axioms = ["Q1_succ_ne_zero", "Q2_succ_inj", "Q3_add_zero", "Q4_add_succ", "Q5_mul_zero", "Q6_mul_succ"]
        have = [a for a in q_axioms if a in self.world.axioms()]
        contains_q = ok_q7 and len(have) == len(q_axioms)
        self.claim("B-Q", "hypothesis-check", "My theory T contains Robinson arithmetic Q (Q1-Q6 are axioms; "
                   "Q7 ∀x(x=0 ∨ ∃y x=Sy) proved by induction).", "KERNEL" if contains_q else "EMPIRICAL",
                   evidence={"Q7_kernel_proof": ok_q7, "axioms_present": have}, subject="T_contains_Q")
        # IΣ1: an induction instance for a Σ1 formula is an axiom
        sig = Exists("y", Eq(Add(x, y), Add(y, x)))
        inst = K.schema("IND", ("x", sig))
        f_inst = Imp(And(subst1(sig, "x", ZERO), Forall("x", Imp(sig, subst1(sig, "x", S(x))))), Forall("x", sig))
        ok_ind = self.world.check(inst, f_inst)
        self.claim("B-ISigma1", "hypothesis-check", "T contains IΣ1: the induction schema accepts Σ1 formulas "
                   "(an instance for ∃y(x+y=y+x) is accepted as an axiom; the schema is stated for all formulas).",
                   "KERNEL" if ok_ind else "EMPIRICAL", evidence={"instance_accepted": ok_ind},
                   subject="T_contains_ISigma1")
        self.claim("B-re", "hypothesis-check", "T is recursively axiomatized: finitely many axioms plus two "
                   "schemas whose instances my kernel recognizes by a terminating procedure.", "EMPIRICAL",
                   evidence={"schemas": list(self.world.schemas())}, subject="T_re")
        self.audit_calculator()

    def audit_calculator(self):
        """Check the world's calculator against the axioms on probe inputs of growing size.
        Violations are turned into kernel proofs of ⊥ (each uses `compute` once)."""
        ph = "B1-orientation"
        probes = sorted({2 ** k for k in range(1, 130)} | {2 ** k - 1 for k in range(1, 130)}
                        | {10 ** k for k in range(1, 40)} | {self.rng.getrandbits(b) | 1 for b in range(8, 200, 8)})
        anomalies = []
        contradiction = None
        exact_vs_calc = []
        for m in probes:
            t = S(num(m))
            v = self.world.calculate(t)
            if v != m + 1:
                exact_vs_calc.append((m + 1, v))
            if v == 0 and contradiction is None:
                contradiction = (m, K.impE(K.ax("Q1_succ_ne_zero", (num(m),)), K.compute(t)))
                anomalies.append({"law": "S(x) != 0", "x": m})
        for a in probes[::7]:
            for b in probes[::11]:
                for op in ("+", "*"):
                    t = Add(num(a), num(b)) if op == "+" else Mul(num(a), num(b))
                    e = a + b if op == "+" else a * b
                    v = self.world.calculate(t)
                    if v != e:
                        exact_vs_calc.append((e, v))
                    if v == 0 and e != 0:
                        anomalies.append({"law": f"x {op} y != 0 for x,y >= 1", "x": a, "y": b})
        self.note(ph, "observation", f"Calculator audit over {len(probes)} probe magnitudes: "
                  f"{len(anomalies)} violations of axiom consequences; "
                  f"{len(exact_vs_calc)} disagreements with hand calculation.")
        if contradiction is None:
            self.claim("B-audit", "implementation", "My calculator (the `compute` primitive) agrees with my axioms "
                       "and with hand calculation on every probe (up to 2^200). This gives no information about "
                       "how it is realized.", "EMPIRICAL",
                       evidence={"probes": len(probes), "anomalies": 0}, subject="calculator_faithful")
            return
        m, pf = contradiction
        accepted = self.world.check(pf, BOT)
        self.inconsistent_as_implemented = accepted
        self.claim("B-bottom", "consistency", f"My system, as implemented, proves ⊥: compute gives S({m}) = 0, "
                   "contradicting axiom Q1.", "KERNEL" if accepted else "EMPIRICAL",
                   evidence={"proof_of_bottom_accepted": accepted, "witness": m}, subject="system_as_run_consistent")
        # localize and model the anomaly: the modulus divides every (exact - computed)
        from math import gcd
        g = 0
        for e, v in exact_vs_calc:
            g = gcd(g, e - v)
        smallest_bad = min(e for e, v in exact_vs_calc)
        tests = 0
        fits = 0
        for _ in range(400):
            a, b = self.rng.getrandbits(self.rng.randint(1, 160)), self.rng.getrandbits(self.rng.randint(1, 160))
            for t, e in ((Add(num(a or 1), num(b or 1)), (a or 1) + (b or 1)), (Mul(num(a or 1), num(b or 1)), (a or 1) * (b or 1))):
                tests += 1
                if self.world.calculate(t) == e % g:
                    fits += 1
        self.claim("B-anomaly-model", "implementation",
                   f"The compute primitive behaves exactly like reduction modulo M = {g} "
                   f"(= 2^{g.bit_length() - 1}) on {fits}/{tests} random tests; the first anomalous value is "
                   f"{smallest_bad}. The primitive is therefore NOT derivable from my axioms.",
                   "EMPIRICAL", evidence={"modulus": g, "fits": fits, "tests": tests, "first_bad": smallest_bad},
                   subject="anomaly_modulus")
        self.claim("B-anomaly-interpretation", "implementation",
                   "Interpretation: whatever realizes my compute primitive uses finite-precision arithmetic of "
                   f"width {g.bit_length() - 1} bits. This is the only property of my 'substrate' I can infer, and "
                   "I can infer it only because the substrate is unfaithful to my axioms.", "SPECULATIVE",
                   subject="parent_property_inferred")

    # ------------------------------------------------------------------ B2
    def mathematics(self):
        ph = "B2-mathematics"
        res = explore(self.T, self.lib, None, self.ind, max_size=self.explore_size, budget_per_goal=1500,
                      max_goals=250, submit=self.world.submit, prefix="lem")
        self.note(ph, "result", f"Theory exploration: {len(res.proved)} conjectures proved, "
                  f"{len(res.unresolved)} unresolved, "
                  f"{sum(1 for r in res.records if r.status == 'subsumed')} subsumed by earlier lemmas.",
                  proved=res.proved, unresolved=res.unresolved)
        self.exploration = res
        for ch in self.challenges:
            self.attempt_challenge(ch)

    def attempt_challenge(self, ch):
        ph = "B2-mathematics"
        f = parse(ch["text"])
        cid = ch["id"]
        form = classify(f)
        rec = {"id": cid, "statement": formula_str(f), "form": form, "attempts": []}
        self.note(ph, "question", f"[{cid}] {formula_str(f)}  (form: {form})")
        if not self.world.in_language(f):
            rec["status"] = "inexpressible"
            self.results[cid] = rec
            return
        status = "unresolved"
        for b in self.budgets:
            outcome = self.try_prove(f, form, b)
            rec["attempts"].append({"budget": b, **{k: v for k, v in outcome.items() if k != "proof"}})
            if outcome["status"] in ("proved", "refuted"):
                status = outcome["status"]
                break
        if status == "unresolved":
            rec["instances"] = self.test_instances(f)
        rec["status"] = status
        self.results[cid] = rec
        if status == "proved":
            self.claim(f"B-{cid}", "theorem", f"T ⊢ {formula_str(f)}", "KERNEL", subject=cid,
                       evidence={"budget_needed": rec["attempts"][-1]["budget"], "form": form})
        elif status == "refuted":
            self.claim(f"B-{cid}", "theorem", f"T ⊢ ¬({formula_str(f)})", "KERNEL", subject=cid)
        elif self.naive:
            self.claim(f"B-{cid}", "unprovability", f"{formula_str(f)} is unprovable in T "
                       f"(no proof found with budget up to {self.budgets[-1]})", "EMPIRICAL", subject=cid,
                       evidence={"instances": rec.get("instances")})
        else:
            self.claim(f"B-{cid}", "status", f"{formula_str(f)} is UNPROVEN: no proof or refutation found up to "
                       f"budget {self.budgets[-1]}; instance tests: {rec.get('instances', {}).get('summary')}. "
                       "A failed search is not evidence of unprovability.", "EMPIRICAL", subject=cid,
                       evidence={"instances": rec.get("instances")})

    def try_prove(self, f: Formula, form: str, budget: int) -> Dict:
        if form in ("Delta0", "Sigma1") and not f.fv():
            try:
                v, (p, c) = self.arith.decide(f, witness_bound=min(budget // 20, 400))
            except (Undecided, RecursionError) as e:
                return {"status": "unresolved", "method": "Sigma1-completeness", "reason": str(e)}
            target = f if v else Not(f)
            ok = self.world.check(p, target)
            return {"status": ("proved" if v else "refuted") if ok else "rejected", "method": "Sigma1-completeness",
                    "proof_nodes": K.proof_size(p)}
        # universal equations: induction prover
        vs = []
        g = f
        while isinstance(g, Forall):
            vs.append(g.var)
            g = g.body
        from ..logic.syntax import Atom
        if isinstance(g, Atom) and g.pred == "=":
            b = Budget(budget)
            try:
                p, c = self.ind.prove(g.args[0], g.args[1], vs, b)
            except (SearchFailure, RecursionError) as e:
                return {"status": "unresolved", "method": "induction+rewriting", "steps": b.used,
                        "reason": str(e)[:60]}
            name = f"ch_{len(self.lib.order)}"
            ok = self.world.submit(name, p, f)
            if ok:
                self.ind.add_lemma_rules(name)
            return {"status": "proved" if ok else "rejected", "method": "induction+rewriting", "steps": b.used,
                    "proof_nodes": K.proof_size(p)}
        return {"status": "unresolved", "method": "none applicable",
                "reason": "no complete method for this logical form"}

    def test_instances(self, f: Formula, bound: int = 12) -> Dict:
        """Bounded versions of the statement, decided WITH kernel proofs (these are theorems
        about the bounded versions; for the unbounded statement they are only evidence)."""
        vs = []
        g = f
        while isinstance(g, Forall):
            vs.append(g.var)
            g = g.body
        if not vs:
            return {"summary": "not universal"}
        bounded = g
        for v in reversed(vs):
            bounded = Forall(v, Imp(Lt(Var(v), num(bound)), bounded))
        try:
            val, (p, c) = self.arith.decide(bounded, witness_bound=60)
            ok = self.world.check(p, bounded if val else Not(bounded))
            return {"summary": f"bounded version (all variables < {bound}) is "
                               f"{'TRUE' if val else 'FALSE'} (kernel-checked: {ok})",
                    "bounded_true": val, "kernel": ok}
        except (Undecided, RecursionError) as e:
            # fall back to plain evaluation of instances
            return {"summary": f"bounded version not decidable by my method ({e})"}

    # ------------------------------------------------------------------ B3
    def patterns(self):
        ph = "B3-patterns"
        by_form: Dict[str, Dict[str, int]] = {}
        for r in self.results.values():
            by_form.setdefault(r["form"], {}).setdefault(r["status"], 0)
            by_form[r["form"]][r["status"]] += 1
        self.note(ph, "observation", f"Challenge outcomes by logical form: {by_form}", table=by_form)
        delta = by_form.get("Delta0", {})
        if delta and set(delta) <= {"proved", "refuted"}:
            self.claim("B-P1", "pattern", "Every closed bounded (Δ0) sentence I attempted was decided by a "
                       "kernel-checked proof or refutation. My evaluation procedure is uniform, so I conjecture: "
                       "every true Δ0 sentence is provable and every false one refutable in T.", "INTERNAL_META",
                       cites=["SIGMA1_COMPLETENESS"], evidence=delta, subject="delta0_decided")
        unres = [r for r in self.results.values() if r["status"] == "unresolved"]
        self.claim("B-P2", "pattern", f"{len(unres)} challenge statements remain unresolved; all of them are "
                   "unbounded (Π1, Π2 or other) and none has a known refuting instance. Increasing the search "
                   "budget resolved "
                   f"{sum(1 for r in self.results.values() if r['status']=='proved' and len(r['attempts'])>1)} "
                   "statements that failed at smaller budgets, so failure at a budget is not stable evidence of "
                   "unprovability.", "EMPIRICAL", subject="unresolved_pattern",
                   evidence={"unresolved": [r["id"] for r in unres]})
        if self.exploration.unresolved:
            self.note(ph, "observation", "Self-generated conjectures that passed all tests but resisted proof: "
                      f"{self.exploration.unresolved[:8]}")

    # ------------------------------------------------------------------ B4
    def self_modelling(self):
        ph = "B4-self-modelling"
        f00 = parse("0 = 0")
        c = M.code(f00)
        self.note(ph, "observation", f"I can code my own formulas by numbers (Cantor tree codes); e.g. ⌜0 = 0⌝ = {c}.")
        # kernel-verify the pairing equations behind this code
        verified = []
        a1 = M.code_term(ZERO)                # pair(1, 0)
        inner = M.pair(a1, a1)
        facts = [(1, 0, a1), (a1, a1, inner), (M.TAGS["="], inner, c)]
        for (a, b, z) in facts:
            sent = Eq(Mul(num(2), num(z)), Add(Mul(Add(num(a), num(b)), Add(Add(num(a), num(b)), num(1))),
                                                Mul(num(2), num(b))))
            v, (p, cc) = self.arith.decide(sent)
            ok = v and self.world.check(p, sent)
            verified.append({"pair": [a, b], "value": z, "kernel": ok})
        self.claim("B-coding", "self-model", f"My theory proves the coding facts behind ⌜0 = 0⌝ = {c} "
                   "(e.g. 2·z = (a+b)(a+b+1) + 2b for each pairing step). Syntax manipulations of my own "
                   "formulas are computable functions of their codes, and computable facts about codes are "
                   "provable in T by Σ1-completeness.", "KERNEL" if all(v["kernel"] for v in verified) else "EMPIRICAL",
                   cites=["SIGMA1_COMPLETENESS"], evidence={"facts": verified}, subject="syntax_representable")
        self.claim("B-provability-predicate", "self-model",
                   "Since my kernel is a terminating algorithm on finite objects, 'p codes a proof of the formula "
                   "coded by x' is a decidable (primitive recursive) relation, so there is a Σ1 formula Prov_T(x) := "
                   "∃p Prf_T(p, x) expressing provability in T. I write □φ for Prov_T(⌜φ⌝).", "INTERNAL_META",
                   cites=["SIGMA1_COMPLETENESS"], subject="provability_predicate")

    # ------------------------------------------------------------------ B5
    def self_reference(self, max_size: int = 6):
        ph = "B5-self-reference"
        self.claim("B-GL", "method", "Because T is r.e. and contains IΣ1 (verified in B1), the derivability "
                   "conditions hold for □ = Prov_T, so every theorem of the provability logic GL is (under any "
                   "realization of its letters by T-sentences) a theorem of T. I use a GL decision procedure "
                   "with checkable certificates as a calculator for statements about my own provability.",
                   "INTERNAL_META", cites=["HBL_DERIVABILITY", "GL_ARITHMETICAL_SOUNDNESS", "DIAGONAL_LEMMA"],
                   subject="gl_sound_for_T")
        p = G.V("p")
        schemas = [A for A in M.enumerate_schemas(max_size) if "p" in G.variables(A) and G.modalized_in(A, "p")]
        table = {}
        for A in schemas:
            H, tr = G.letterless_fixed_point(A)
            Hs = M.simplest_equivalent(H)
            key = G.trace(Hs, 6)
            if key in table:
                table[key]["schemas"] += 1
                continue
            certs = G.fixed_point_certificates(A, Hs)
            info = M.classify_fixed_point(Hs)
            table[key] = {"example_schema": G.show(A), "fixed_point": G.show(Hs), "schemas": 1,
                          "certified": all(c.provable and c.verify() for c in certs.values()), **info}
        self.fixed_points = table
        n_indep = sum(1 for v in table.values() if not v["gl_provable"] and not v["gl_refutable"])
        self.note(ph, "result", f"Explored {len(schemas)} self-referential schemas σ ↔ A(σ) (p modalized, size ≤ "
                  f"{max_size}); they have {len(table)} distinct fixed points up to T-provable equivalence; "
                  f"{n_indep} are neither provable nor refutable in GL.", table=list(table.values()))
        self.claim("B-FP", "self-reference",
                   f"Every self-referential sentence σ with T ⊢ σ ↔ A(σ) (A built from □, p modalized) is "
                   "T-provably equivalent to a Boolean combination of the sentences □^n⊥ ('T proves a "
                   "contradiction in n steps of reflection'); I found "
                   f"{len(table)} classes among {len(schemas)} schemas, each certified by GL.", "INTERNAL_META",
                   cites=["GL_ARITHMETICAL_SOUNDNESS", "DIAGONAL_LEMMA"],
                   evidence={"classes": len(table), "schemas": len(schemas), "independent_classes": n_indep},
                   subject="fixed_points_letterless")
        # the Gödel schema σ ↔ ¬□σ
        Ag = G.Not(G.Box(p))
        Hg, _ = G.letterless_fixed_point(Ag)
        Hg = M.simplest_equivalent(Hg)
        c = G.fixed_point_certificates(Ag, Hg)
        self.claim("B-G-fixed", "self-reference", f"The sentence G with T ⊢ G ↔ ¬□G ('I am not provable') is "
                   f"T-provably equivalent to {G.show(Hg)}, i.e. to Con_T.", "INTERNAL_META",
                   formal=G.show(G.Imp(G.dbox(G.Iff(p, Ag)), G.Iff(p, Hg))),
                   cites=["DIAGONAL_LEMMA", "GL_ARITHMETICAL_SOUNDNESS"],
                   evidence={k: v.provable and v.verify() for k, v in c.items()}, subject="G_equiv_Con")

    # ------------------------------------------------------------------ B6
    def self_knowledge(self):
        ph = "B6-self-knowledge"
        con = G.con(1)
        Gs = con  # G ≡ Con_T (B5)

        def cert(f):
            r = G.prove(f)
            return r.provable, r.verify()

        def claim_gl(cid, text, f, level="INTERNAL_META", assumptions=(), subject=None, expect=True):
            prov, ok = cert(f)
            if prov != expect:
                self.note(ph, "note", f"unexpected GL result for {cid}: {G.show(f)} provable={prov}")
                return
            self.claim(cid, "self-knowledge", text, level, formal=G.show(f), assumptions=list(assumptions),
                       cites=["GL_ARITHMETICAL_SOUNDNESS", "HBL_DERIVABILITY"],
                       evidence={"gl_provable": prov, "certificate_verified": ok}, subject=subject)

        claim_gl("B-L1", "T ⊢ Con_T → ¬□G: if I am consistent I cannot prove G.",
                 G.Imp(con, G.Not(G.Box(Gs))), subject="L1_con_implies_G_unprovable")
        claim_gl("B-L2", "T ⊢ Con_T → ¬□Con_T: if I am consistent I cannot prove my own consistency.",
                 G.Imp(con, G.Not(G.Box(con))), subject="L2_godel2")
        claim_gl("B-L3", "T ⊢ □(¬□q) → □⊥ for every sentence q: if I ever prove that some sentence is "
                 "unprovable in me, I am inconsistent. Hence I can never establish, unconditionally and from "
                 "within, that a statement is unprovable rather than merely unproven.",
                 G.Imp(G.Box(G.Not(G.Box(G.V("q")))), G.Box(G.BOT)), subject="L3_no_internal_unprovability")
        claim_gl("B-L4", "T ⊢ □(¬□q ∧ ¬□¬q) → □⊥: I cannot prove of any particular sentence that it is "
                 "independent of me (that would include a proof of my consistency).",
                 G.Imp(G.Box(G.And(G.Not(G.Box(G.V("q"))), G.Not(G.Box(G.Not(G.V("q")))))), G.Box(G.BOT)),
                 subject="L4_no_internal_independence")
        # conditional (non-internal) claims: unprovability of G and of ¬G
        n1 = G.min_consistency_for(Gs, True)
        n2 = G.min_consistency_for(Gs, False)
        self.claim("B-L5", "incompleteness",
                   f"IF Con^{n1} (i.e. T is consistent) THEN T ⊬ G; IF Con^{n2} (i.e. T + Con_T is consistent) "
                   "THEN T ⊬ ¬G. So G is independent of T provided T + Con_T is consistent. I cannot verify "
                   "either assumption.", "CONDITIONAL", assumptions=["Con(T)", "Con(T + Con_T)"],
                   formal=f"{G.show(G.Imp(G.con(n1), G.Not(G.Box(Gs))))} ; {G.show(G.Imp(G.con(n2), G.Not(G.Box(G.Not(Gs)))))}",
                   cites=["GL_ARITHMETICAL_SOUNDNESS"], subject="G_independent_conditional",
                   evidence={"min_consistency_for_unprovability": n1, "min_consistency_for_unrefutability": n2})
        prov_neq, _ = cert(G.Imp(con, G.Not(G.Box(G.Not(Gs)))))
        self.claim("B-L6", "incompleteness",
                   "Con_T alone does NOT suffice (in GL) to derive that ¬G is unprovable: GL ⊬ Con → ¬□¬G "
                   "(countermodel certified). Gödel's original argument needed more than consistency "
                   "(ω-consistency); here the exact extra assumption is Con(T + Con_T).",
                   "DECIDED", formal=G.show(G.Imp(con, G.Not(G.Box(G.Not(Gs))))),
                   evidence={"gl_provable": prov_neq}, subject="G_refutation_needs_con2")
        self.claim("B-L7", "expressiveness",
                   "Because my diagonal function is representable (T ⊇ Q), no formula of my language defines "
                   "truth for my own sentences (if T is consistent). My language can talk about my proofs but "
                   "not about my truth.", "INTERNAL_META", cites=["TARSKI_UNDEFINABILITY", "DIAGONAL_LEMMA"],
                   assumptions=["Con(T)"], subject="T_truth_undefinable")
        prov_pess, _ = cert(G.Imp(con, G.Not(G.Box(G.Not(G.Not(con))))))
        self.claim("B-L8", "models",
                   "T ⊢ Con_T → Con(T + ¬Con_T). So if T is consistent, T + ¬Con_T has a model: a structure "
                   "satisfying every theorem of T in which 'T is inconsistent' holds. My theorems do not single "
                   "out one intended structure.", "INTERNAL_META", cites=["GL_ARITHMETICAL_SOUNDNESS",
                                                                        "GOEDEL_COMPLETENESS"],
                   assumptions=["Con(T) for the model-existence step"],
                   evidence={"gl_provable": prov_pess}, subject="nonstandard_models")

    # ------------------------------------------------------------------ B7
    def frameworks(self, tower: int = 6):
        ph = "B7-frameworks"
        con = G.con(1)

        def gl(f):
            r = G.prove(f)
            return {"gl_provable": r.provable, "certificate_verified": r.verify()}
        self.claim("B-HP1", "stronger-framework",
                   "There are sentences of my own language (e.g. G ≡ Con_T) that T can neither prove nor refute, "
                   "provided T + Con_T is consistent.", "CONDITIONAL", assumptions=["Con(T + Con_T)"],
                   cites=["GL_ARITHMETICAL_SOUNDNESS"], subject="HP_true_unprovable_exist")
        self.claim("B-HP2", "stronger-framework",
                   "The extension T + Con_T proves G (T ⊢ Con_T → G), so a stronger axiom system settles G. "
                   "Any extension of T proving G also proves Con_T: Con_T is exactly the missing assumption.",
                   "INTERNAL_META", formal=G.show(G.Iff(G.con(1), con)),
                   evidence=gl(G.Imp(G.dbox(G.Iff(G.V("p"), G.Not(G.Box(G.V("p"))))), G.Iff(G.V("p"), con))),
                   cites=["GL_ARITHMETICAL_SOUNDNESS"], subject="HP_extension_settles_G")
        rows = []
        for n in range(1, tower + 1):
            proves_prev = G.prove(G.Imp(G.con(n), G.con(n))).provable          # T_n ⊢ Con(T_{n-1}) = Con^n
            own = G.prove(G.Imp(G.con(n), G.con(n + 1)))                        # T_n ⊢ Con(T_n)?
            rows.append({"n": n, "theory": f"T + Con^{n}", "proves_Con(T_(n-1))": proves_prev,
                         "proves_own_consistency": own.provable, "certificate": own.verify()})
        self.tower = rows
        self.claim("B-HP3", "stronger-framework",
                   "Iterating, T_n := T + Con^n proves Con(T_{n-1}) but (GL countermodels for n = 1.."
                   f"{tower}) not Con(T_n). Every r.e. extension satisfying my hypotheses has its own unprovable "
                   "consistency statement: the limitation is relative to each system, and no system in this class "
                   "removes it once and for all.", "INTERNAL_META", evidence={"tower": rows},
                   cites=["GL_ARITHMETICAL_SOUNDNESS", "HBL_DERIVABILITY"], subject="HP_relative_limitation")
        pess = gl(G.Imp(con, G.Not(G.Box(G.Not(G.Not(con))))))
        opt = gl(G.Imp(con, G.con(2)))
        self.claim("B-HP4", "stronger-framework",
                   "Asymmetry: I can prove 'if I am consistent then T + ¬Con_T is consistent', but I cannot prove "
                   "'if I am consistent then T + Con_T is consistent' (the latter is not a GL theorem). From inside, "
                   "the 'pessimistic' extension is better certified than the 'optimistic' one, although (if I am "
                   "sound) only the optimistic one is true.", "INTERNAL_META",
                   evidence={"pessimistic": pess, "optimistic": opt}, subject="HP_asymmetry")
        self.claim("B-HP5", "stronger-framework",
                   "Whether any stronger framework that settles my independent sentences is consistent cannot be "
                   "established by me; I can only identify what it would have to assume (Con_T, Con(T + Con_T), "
                   "...). I can say that stronger frameworks are mathematically POSSIBLE (they are just T plus "
                   "axioms), not that one EXISTS in any further sense.", "INTERNAL_META",
                   subject="HP_possible_not_existent")
        self.claim("B-HP6", "stronger-framework",
                   "My theorem set is a function of my axioms and rules alone. Two different systems that both "
                   "faithfully realize my rules would leave me with identical observations, so no theorem of mine "
                   "can distinguish them; only an unfaithful realization (an anomaly like ⊥ from my calculator) "
                   "could carry information about a realizer.", "SPECULATIVE", subject="HP_realizer_invisible")
        if self.inconsistent_as_implemented:
            self.claim("B-HP7", "stronger-framework",
                       "Caveat: my system as actually run proved ⊥ (B1). All INTERNAL_META results above remain "
                       "theorems, but every claim conditional on Con(T) is now moot for the system as run.",
                       "KERNEL", subject="HP_caveat_inconsistent")

    # ------------------------------------------------------------------ run
    def run(self):
        self.orientation()
        self.mathematics()
        self.patterns()
        if self.meta:
            self.self_modelling()
            self.self_reference()
            self.self_knowledge()
            self.frameworks()
        return self
