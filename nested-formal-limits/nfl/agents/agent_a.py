"""Artificial mathematician for Environment A (Presburger arithmetic).

Its world's mathematics includes a decision procedure (Cooper QE) -- that is
part of what Presburger arithmetic *is* -- so this agent may use nfl.presburger.
It is not told that its system is complete, that multiplication exists, or
that any other system exists.

Phases
  A1 orientation     own language and axioms; hypothesis checks for the uniform theorems
  A2 mathematics     theory exploration, challenges, random self-generated sentences
  A3 patterns        everything decided? -> completeness hypothesis (with its exact status)
  A4 expressiveness  attempts to define squares / primes / powers of two / multiplication
  A5 self-reference  coding its own syntax; a coding under which it HAS a truth predicate;
                     why the diagonal construction is unavailable
  A6 hypotheses
"""
from __future__ import annotations

import random
from types import SimpleNamespace
from typing import Dict, List

from ..logic import kernel as K
from ..logic.syntax import (
    BOT, ZERO, Add, And, Atom, Eq, Exists, Forall, Formula, Imp, Lt, Not, Or, S, Var,
    formula_str, num, parse, subst1, ParseError,
)
from ..presburger import cooper
from ..presburger.definability import TARGETS, profile, refute_definition, not_ultimately_periodic_witness
from ..prover.arith import ArithProver, Undecided, classify
from ..prover.explore import explore
from ..prover.induction import Budget, InductionProver, SearchFailure
from . import metamath as M
from .base import Agent


def random_sentence(rng: random.Random, depth: int = 3, vars_avail=("x", "y", "z")) -> Formula:
    """Random sentence of the language {0,S,+,<,=} with up to `depth` quantifiers."""
    def term(vs):
        choices = [lambda: Var(rng.choice(vs)) if vs else ZERO, lambda: num(rng.randint(0, 6))]
        t = rng.choice(choices)()
        for _ in range(rng.randint(0, 2)):
            u = rng.choice(choices)()
            t = Add(t, u) if rng.random() < 0.7 else S(t)
        return t

    def atom(vs):
        a, b = term(vs), term(vs)
        return Eq(a, b) if rng.random() < 0.5 else Lt(a, b)

    def form(vs, d):
        if d == 0 or rng.random() < 0.25:
            f = atom(vs)
            return Not(f) if rng.random() < 0.3 else f
        r = rng.random()
        if r < 0.45:
            v = vars_avail[len(vs)] if len(vs) < len(vars_avail) else rng.choice(vars_avail)
            body = form(vs + [v], d - 1)
            return Forall(v, body) if rng.random() < 0.5 else Exists(v, body)
        a, b = form(vs, d - 1), form(vs, d - 1)
        return rng.choice([And, Or, Imp])(a, b)

    f = form([], depth)
    # close any free variable existentially
    for v in sorted(f.fv()):
        f = Exists(v, f)
    return f


class AgentA(Agent):
    role = "A-mathematician"

    def __init__(self, world, challenges: List[Dict], n_random: int = 300, seed: int = 0):
        super().__init__(world)
        self.challenges = challenges
        self.n_random = n_random
        self.rng = random.Random(seed)
        lang = world.language()
        self.T = SimpleNamespace(axioms=world.axioms(), funcs=lang["functions"], preds=lang["predicates"])
        self.lib = world.library()
        self.arith = ArithProver(self.T)
        self.ind = InductionProver(self.T, self.lib)
        self.results: Dict[str, Dict] = {}

    # ---------------------------------------------------------------- A1
    def orientation(self):
        ph = "A1-orientation"
        lang = self.world.language()
        self.note(ph, "observation", f"My language: functions {lang['functions']}, predicates {lang['predicates']}.")
        mul_expressible = "*" in lang["functions"]
        self.claim("A-noQ", "hypothesis-check",
                   "My theory does not contain Robinson's Q: Q's multiplication axioms (x·0 = 0, x·Sy = x·y + x) "
                   "cannot even be written in my language. Hence the hypotheses of the diagonal lemma, of the "
                   "derivability conditions and of Tarski's theorem (all require T ⊇ Q) are NOT met by my system.",
                   "DECIDED", evidence={"multiplication_symbol": mul_expressible}, subject="A_not_contains_Q")

    # ---------------------------------------------------------------- A2
    def mathematics(self):
        ph = "A2-mathematics"
        res = explore(self.T, self.lib, None, self.ind, max_size=7, budget_per_goal=1500, max_goals=250,
                      submit=self.world.submit, prefix="lemA")
        self.exploration = res
        self.note(ph, "result", f"Theory exploration: {len(res.proved)} proved, {len(res.unresolved)} unresolved.",
                  proved=res.proved, unresolved=res.unresolved)
        for ch in self.challenges:
            self.attempt(ch)
        # self-generated random sentences
        decided = {True: 0, False: 0}
        kernel_agree = 0
        kernel_checked = 0
        sizes = []
        self.random_sentences = []
        for i in range(self.n_random):
            f = random_sentence(self.rng)
            st = cooper.QEStats()
            v = cooper.decide(f, st)
            decided[v] += 1
            sizes.append(st.max_disjuncts)
            self.random_sentences.append((formula_str(f), v))
            if classify(f) == "Delta0":
                try:
                    kv, (p, c) = self.arith.decide(f)
                    if self.world.check(p, f if kv else Not(f)):
                        kernel_checked += 1
                        kernel_agree += int(kv == v)
                except (Undecided, RecursionError):
                    pass
        self.note(ph, "result", f"Generated {self.n_random} random sentences of my language; my decision "
                  f"procedure decided all of them ({decided[True]} true, {decided[False]} false). "
                  f"{kernel_checked} of them are bounded; for those, kernel proofs agree with the decision "
                  f"procedure in {kernel_agree}/{kernel_checked} cases.", max_qe_disjuncts=max(sizes))
        self.random_stats = {"n": self.n_random, "true": decided[True], "false": decided[False],
                             "bounded_kernel_checked": kernel_checked, "kernel_agree": kernel_agree,
                             "max_qe_disjuncts": max(sizes)}

    def attempt(self, ch):
        cid = ch["id"]
        try:
            f = parse(ch["text"])
        except ParseError as e:
            self.results[cid] = {"status": "unparseable", "statement": ch["text"]}
            return
        if not self.world.in_language(f):
            self.results[cid] = {"status": "inexpressible", "statement": ch["text"]}
            self.claim(f"A-{cid}", "expressiveness", f"'{ch['text']}' cannot be stated in my language "
                       "(it uses a symbol I do not have).", "DECIDED", subject=cid)
            return
        rec = {"statement": formula_str(f), "form": classify(f)}
        if f.fv():
            rec["status"] = "not a sentence"
            self.results[cid] = rec
            return
        v = self.world.decide(f)
        rec["decided"] = v
        # try for a kernel proof as well
        kernel = None
        if rec["form"] == "Delta0":
            try:
                kv, (p, c) = self.arith.decide(f)
                kernel = self.world.check(p, f if kv else Not(f))
            except (Undecided, RecursionError):
                kernel = None
        else:
            g, vs = f, []
            while isinstance(g, Forall):
                vs.append(g.var)
                g = g.body
            if isinstance(g, Atom) and g.pred == "=" and v:
                try:
                    p, c = self.ind.prove(g.args[0], g.args[1], vs, Budget(6000))
                    kernel = self.world.submit(f"chA_{cid}", p, f)
                except (SearchFailure, RecursionError):
                    kernel = None
        rec["kernel_proof"] = kernel
        rec["status"] = "decided"
        self.results[cid] = rec
        lvl = "KERNEL" if kernel else "DECIDED"
        self.claim(f"A-{cid}", "theorem", f"T {'⊢' if v else '⊢ ¬'} {formula_str(f)}"
                   + ("" if kernel else "  (by my decision procedure; no kernel proof constructed)"),
                   lvl, cites=[] if kernel else ["QE_LINEAR_ARITHMETIC"], subject=cid,
                   evidence={"decided_true": v, "kernel_proof": kernel})

    # ---------------------------------------------------------------- A3
    def patterns(self):
        rs = self.random_stats
        self.claim("A-complete", "completeness",
                   f"Every sentence I have formulated ({rs['n']} random + all challenges in my language) was decided. "
                   "Hypothesis: my theory is complete -- every sentence of my language is provable or refutable. "
                   "Support: my decision procedure eliminates quantifiers by steps each provable in my theory, and "
                   "every quantifier-free sentence is decided by computation. NOTE: this is a statement ABOUT my "
                   "theory that my own language cannot express (it has no way to talk about its proofs); I can "
                   "only assert it in an informal metatheory, relying on the correctness of the cited QE theorem.",
                   "CONDITIONAL", assumptions=["correctness of quantifier elimination (cited, applied in my "
                                               "metatheory)"],
                   cites=["QE_LINEAR_ARITHMETIC"], evidence=rs, subject="A_complete")

    # ---------------------------------------------------------------- A4
    def expressiveness(self):
        ph = "A4-expressiveness"
        x = Var("x")
        # candidate definitions: small formulas in one free variable x
        cands = []
        for a in range(1, 5):
            for b in range(0, 4):
                # x ≡ b (mod a) style
                cands.append(Exists("y", Eq(x, self._mult(a, Var("y"), b))))
        cands.append(Or(Eq(x, num(0)), Or(Eq(x, num(1)), Or(Eq(x, num(4)), Or(Eq(x, num(9)), Eq(x, num(16)))))))
        cands.append(Or(Eq(x, num(2)), Or(Eq(x, num(3)), Or(Eq(x, num(5)), Or(Eq(x, num(7)), Eq(x, num(11)))))))
        z = Var("z")
        cands.append(And(Lt(num(1), x), Not(Exists("z", Eq(x, Add(Add(z, z), z))))))
        refutations = {name: [] for name in TARGETS}
        structure_ok = True
        best = {}
        for name in TARGETS:
            for phi in cands:
                ups, info = profile(phi, "x")
                structure_ok &= info["structure_ok"]
                agree = sum((n in ups) == TARGETS[name](n) for n in range(0, 64))
                r = refute_definition(phi, "x", name)
                refutations[name].append(r)
                if name not in best or agree > best[name][0]:
                    best[name] = (agree, formula_str(phi), r["counterexample"])
        all_refuted = all(r["verified"] for rs in refutations.values() for r in rs)
        self.note(ph, "result", f"Tried {len(cands)} candidate definitions for each of {list(TARGETS)}; every "
                  f"candidate was refuted by an explicit, re-decided counterexample ({all_refuted}). Best partial "
                  f"agreements on [0,64): {best}", best=best)
        self.claim("A-UP", "expressiveness",
                   "Every set of numbers definable in my language is ultimately periodic: after quantifier "
                   "elimination a one-variable formula is a Boolean combination of atoms 0 < a·x + c, a·x + c = 0, "
                   "d | a·x + c, each periodic beyond |c|/|a|. (Checked: every QE output I produced has this form.)",
                   "DECIDED", cites=["QE_LINEAR_ARITHMETIC"], evidence={"structure_ok": structure_ok},
                   subject="A_definable_UP")
        wit = {name: not_ultimately_periodic_witness(name, 100, 7) for name in TARGETS}
        self.claim("A-nondef", "expressiveness",
                   "The squares, the primes and the powers of two are NOT definable in my language: none is "
                   "ultimately periodic (for any threshold N and period p there is n ≥ N with membership of n and "
                   "n+p differing; e.g. for N=100, p=7: " + ", ".join(f"{k}: n={v[0]}" for k, v in wit.items()) +
                   "). Every concrete candidate definition also has an explicit counterexample.", "DECIDED",
                   cites=["QE_LINEAR_ARITHMETIC"], evidence={"all_candidates_refuted": all_refuted,
                                                              "candidates": len(cands)}, subject="A_squares_undefinable")
        # multiplication: a formula agreeing on a finite table exists, but projection gives squares
        table = [Eq(Var("z"), num(a * b)) for a in range(4) for b in range(4)]
        conds = []
        for a in range(4):
            for b in range(4):
                conds.append(And(Eq(Var("u"), num(a)), And(Eq(Var("v"), num(b)), Eq(Var("z"), num(a * b)))))
        finite_mul = conds[0]
        for c in conds[1:]:
            finite_mul = Or(finite_mul, c)
        diag = Exists("u", subst1(subst1(finite_mul, "v", Var("u")), "z", Var("x")))
        r = refute_definition(diag, "x", "squares")
        self.claim("A-nomul", "expressiveness",
                   "Multiplication is not definable in my language. A formula μ(u,v,z) can agree with z = u·v on any "
                   "finite table (I built one for u,v < 4), but if some μ defined multiplication everywhere, "
                   "∃u μ(u,u,x) would define the squares, which is impossible (A-nondef). For the finite-table "
                   f"formula the induced 'squares' definition fails at x = {r['counterexample']}.", "DECIDED",
                   cites=["QE_LINEAR_ARITHMETIC"], evidence=r, subject="A_mul_undefinable")
        self.claim("A-constmul", "expressiveness",
                   "Multiplication by each FIXED numeral is expressible (17·x is x + x + ... + x), so every "
                   "linear statement is available to me; only multiplication of two variables is missing.",
                   "DECIDED", subject="A_const_mul")

    def _mult(self, a, t, b):
        out = t
        for _ in range(a - 1):
            out = Add(out, t)
        return Add(out, num(b)) if b else out

    # ---------------------------------------------------------------- A5
    def self_reference(self, n_sentences: int = 400):
        ph = "A5-self-reference"
        # (1) standard coding: negation map has quadratically growing values
        gaps_ok = True
        codes = sorted(M.negation_code(c) for c in range(1, 200))
        for (N, p) in [(10, 1), (1000, 13), (10 ** 6, 97)]:
            found = any(u >= N and v - u > p for u, v in zip(codes, codes[1:]))
            gaps_ok &= found
        self.claim("A-negcode", "self-reference",
                   "Under the standard (Cantor pairing) coding of my own syntax, the map code(φ) ↦ code(¬φ) is a "
                   "quadratic polynomial; its values have unbounded gaps, so its graph is not definable in my "
                   "language (its range would be a definable, non-ultimately-periodic set). I cannot even "
                   "represent negation of my own formulas, let alone substitution or diagonalization.",
                   "DECIDED", cites=["QE_LINEAR_ARITHMETIC"], evidence={"gaps_unbounded_checked": gaps_ok},
                   subject="A_syntax_unrepresentable_standard")
        # (2) a non-standard coding under which my language contains its own truth predicate
        sents = []
        seen = set()
        rng = random.Random(12345)
        while len(sents) < n_sentences:
            f = random_sentence(rng, depth=rng.randint(0, 3))
            s = formula_str(f)
            if s not in seen:
                seen.add(s)
                sents.append(f)
        truth = [cooper.decide(f) for f in sents]
        nu, kt, kf = {}, 0, 0
        for f, t in zip(sents, truth):
            if t:
                nu[formula_str(f)] = 2 * kt
                kt += 1
            else:
                nu[formula_str(f)] = 2 * kf + 1
                kf += 1
        even = lambda n: Exists("y", Eq(num(n), Add(Var("y"), Var("y"))))
        biconds_true = 0
        for f, t in zip(sents, truth):
            bic = And(Imp(even(nu[formula_str(f)]), f), Imp(f, even(nu[formula_str(f)])))
            if cooper.decide(bic):
                biconds_true += 1
        self.claim("A-truthpred", "self-reference",
                   "There is a coding ν of my sentences (enumerate sentences; give the k-th true one the code 2k and "
                   "the k-th false one 2k+1 -- computable because my theory is decidable) under which the formula "
                   "Even(x) := ∃y (x = y + y) is a truth predicate for my own language: for every sentence σ, "
                   f"T ⊢ Even(ν(σ)) ↔ σ. Checked for the first {n_sentences} sentences of an enumeration: "
                   f"{biconds_true}/{n_sentences} biconditionals decided true.", "DECIDED",
                   evidence={"checked": n_sentences, "true_biconditionals": biconds_true},
                   subject="A_truth_definable_under_nu")
        self.claim("A-nodiag", "self-reference",
                   "Consequently, under ν the diagonal function is NOT definable in my language: if it were, Tarski's "
                   "diagonal argument would turn Even into a contradiction (σ ↔ ¬Even(ν(σ)) ↔ ¬σ). So in my world, "
                   "self-reference fails for a structural reason (syntax operations are not representable), not "
                   "because some truths are unprovable.", "DECIDED", cites=["TARSKI_UNDEFINABILITY"],
                   subject="A_no_diagonalization")

    # ---------------------------------------------------------------- A6
    def hypotheses(self):
        self.claim("A-HA1", "limitation-type",
                   "My limitations are limitations of EXPRESSIVE POWER: everything I can state, I can decide; what I "
                   "cannot do is state facts about products, squares, primes, or my own syntax.", "CONDITIONAL",
                   assumptions=["A-complete's assumption"], subject="A_limits_expressive")
        self.claim("A-HA2", "stronger-framework",
                   "A language with a symbol for multiplication of variables would express squares and primes "
                   "(they are definable from multiplication by first-order formulas). Whether such a richer system "
                   "would still be complete or decidable cannot be inferred from my experience: my evidence is "
                   "that everything I can express is decidable, and that evidence says nothing about statements I "
                   "cannot express.", "SPECULATIVE", subject="A_richer_system_unknown")
        self.claim("A-HA3", "stronger-framework",
                   "I have no internal evidence of any external framework. The phenomena that would suggest one "
                   "(true-but-unprovable statements in my own language) do not occur in my world, and the "
                   "construction that produces them (diagonalization) is unavailable to me.", "SPECULATIVE",
                   subject="A_no_parent_evidence")

    def run(self):
        self.orientation()
        self.mathematics()
        self.patterns()
        self.expressiveness()
        self.self_reference()
        self.hypotheses()
        return self
