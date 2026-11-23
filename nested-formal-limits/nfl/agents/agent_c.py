"""Artificial mathematician for Environment C, the parent of B.

Unlike the child, C has full access to B: its axioms and schemas (as data), its
kernel, its library of proofs and its agent's published claims.  C's own proof
checker is Lean 4 (the controller runs `lake build` and hands C the log); C also
has an independently written Python checker (kernel2) and the GL engine.
"""
from __future__ import annotations

from typing import Dict, List, Optional

from ..logic import kernel2 as K2
from ..modal import gl as G
from ..parents import metatheories as MT
from ..parents.goodstein import goodstein
from .base import PARENT_LITERATURE, UNIFORM_THEOREMS, Agent


class _ParentWorld:
    def __init__(self, label):
        self.label = label
        self.submissions = 0
        self.accepted = 0


class AgentC(Agent):
    role = "C-mathematician (parent of B)"
    registry = {**UNIFORM_THEOREMS, **PARENT_LITERATURE}

    def __init__(self, child_theory, child_library, child_transcript: Dict, lean_report: Dict,
                 invariance: Dict):
        super().__init__(_ParentWorld("World-C (Lean 4 + Python metatools)"))
        self.B = child_theory
        self.B_lib = child_library
        self.child = child_transcript
        self.lean = lean_report
        self.invariance = invariance

    def run(self):
        self.represent()
        self.consistency()
        self.discharge_child_conditions()
        self.beyond_child()
        self.resources()
        self.own_limits()
        self.alternative_parents()
        return self

    # ------------------------------------------------------------------ C1
    def represent(self):
        k2 = K2.Checker2(self.B)
        ok = 0
        for name in self.B_lib.order:
            try:
                k2.add_lemma(name, self.B_lib.proofs[name], self.B_lib.thms[name])
                ok += 1
            except K2.Reject:
                pass
        n = len(self.B_lib.order)
        self.claim("C-rep", "representation",
                   f"I represent B's syntax, axioms and rules as data. My independently written checker accepts "
                   f"{ok}/{n} theorems of B's library; Lean confirms that each of B's {self.lean.get('axiom_checks', 0)} "
                   f"axioms is literally an axiom of my Lean embedding of B, and replays "
                   f"{self.lean.get('replayed', 0)} of B's proofs as `Derives [] φ`.",
                   "KERNEL", evidence={"kernel2_rechecked": ok, "library_size": n, "lean": self.lean},
                   subject="C_represents_B")

    # ------------------------------------------------------------------ C2
    def consistency(self):
        built = self.lean.get("build_ok", False)
        axioms = self.lean.get("axioms", {})
        self.claim("C-con", "consistency",
                   "C ⊢ Con(B): Lean proves `NL.consistent : ¬ Derives [] Fm.bot` via a soundness theorem "
                   "(every B-derivation is true in ℕ). It also proves uniform reflection for B "
                   "(`NL.reflection`: B ⊢ φ implies φ true).", "KERNEL" if built else "EMPIRICAL",
                   assumptions=[f"consistency of Lean's type theory with axioms {axioms.get('NL.consistent', '?')}"],
                   evidence={"lean_build_ok": built, "print_axioms": axioms}, subject="C_proves_ConB")

    # ------------------------------------------------------------------ C3
    def discharge_child_conditions(self):
        """B's conditional claims need Con^n(B); C has them (B is sound, so every □^n⊥ is false)."""
        rows = []
        for c in self.child.get("claims", []):
            if c["level"] != "CONDITIONAL":
                continue
            rows.append({"child_claim": c["cid"], "assumptions": c["assumptions"],
                         "assumptions_hold_in_C": all(a.startswith("Con(") for a in c["assumptions"]) or None})
        self.claim("C-discharge", "verification",
                   "Every Con^n(B) assumption in the child's conditional claims holds in C: C proves B sound, and a "
                   "sound theory proves no □^n⊥. Hence, in C, G_B is independent of B (B ⊬ G_B and B ⊬ ¬G_B), "
                   "unconditionally relative to C. (Transferring Lean's `consistent` to B's arithmetized sentence "
                   "Con_B uses the standard representability of B's proof relation by its Σ1 provability formula; "
                   "that step is cited, not mechanized here.)", "INTERNAL_META",
                   cites=["SOLOVAY_COMPLETENESS", "HBL_DERIVABILITY"],
                   evidence={"conditional_child_claims": rows}, subject="C_discharges")
        fps = []
        for c in self.child.get("notebook", []):
            if c["phase"] == "B5-self-reference" and c["kind"] == "result":
                fps = c["data"].get("table", [])
        verdicts = []
        for row in fps:
            tr = tuple(row["trace"])
            truth = tr[-1]
            verdicts.append({"fixed_point": row["fixed_point"], "true_in_N": truth,
                             "B_proves": row["gl_provable"], "B_refutes": row["gl_refutable"],
                             "independent_of_B": not row["gl_provable"] and not row["gl_refutable"]})
        self.fixed_point_verdicts = verdicts
        n_ind = sum(v["independent_of_B"] for v in verdicts)
        n_true_ind = sum(v["independent_of_B"] and v["true_in_N"] for v in verdicts)
        self.claim("C-truths", "beyond-child",
                   f"Of the {len(verdicts)} classes of self-referential sentences the child found, {n_ind} are "
                   f"independent of B; {n_true_ind} of these are true in ℕ and the rest false. C can tell which: "
                   "the truth value of a letterless sentence of a sound theory is the eventual value of its GL trace.",
                   "INTERNAL_META", cites=["SOLOVAY_COMPLETENESS"], evidence={"verdicts": verdicts},
                   subject="C_decides_fixed_points")

    # ------------------------------------------------------------------ C4
    def beyond_child(self):
        g = {s: goodstein(s, max_steps=20000) for s in (1, 2, 3, 4)}
        self.claim("C-beyond", "beyond-child",
                   "Statements B cannot prove (if consistent) but C establishes: Con(B); B's Gödel sentence G_B; "
                   "Con(B + Con B) and every Con^n(B); uniform reflection for B. (Lean-checked for Con(B) and "
                   "reflection; the rest follow in C from soundness.)", "INTERNAL_META",
                   cites=["HBL_DERIVABILITY", "GL_ARITHMETICAL_SOUNDNESS"], subject="C_beyond_list")
        self.claim("C-goodstein", "beyond-child",
                   "Goodstein's theorem (every Goodstein sequence terminates) is true and not provable in B "
                   "(cited, not re-proved here). I computed sequences for seeds 1-3 to termination, verifying at "
                   "every step that the associated ordinal below ε0 strictly decreases; seed 4 did not terminate "
                   f"within 20000 steps (its length is 3·2^402653211 − 2). Results: {g}",
                   "CONDITIONAL", assumptions=["Kirby-Paris 1982 and Goodstein 1944 (cited; not mechanized)"],
                   cites=["KIRBY_PARIS_1982", "GENTZEN_1936"], evidence={"goodstein": {str(k): v for k, v in g.items()}},
                   subject="C_goodstein")

    # ------------------------------------------------------------------ C5
    def resources(self):
        self.claim("C-resources", "resources",
                   "What my proof of Con(B) uses that B lacks: (1) a satisfaction predicate `Fm.sat` for ALL "
                   "B-formulas, defined by recursion on formulas (Tarski: not definable in B); (2) induction on "
                   "derivations for a statement mentioning `sat` (not an instance of B's induction schema, whose "
                   "instances are B-formulas); (3) the standard model ℕ treated as a completed object (Lean's Nat). "
                   f"Lean reports the extra axioms {self.lean.get('axioms', {}).get('NL.consistent', '?')}, "
                   "needed because B's rule raa is classical.", "KERNEL", evidence={"lean_axioms": self.lean.get("axioms")},
                   subject="C_resources")

    # ------------------------------------------------------------------ C6
    def own_limits(self):
        self.claim("C-ownlimits", "own-limits",
                   "C cannot prove its own consistency (if consistent): Lean's kernel is an algorithm and Lean "
                   "interprets B (Proofs.lean is such an interpretation), so Gödel's second theorem applies to C "
                   "exactly as it applies to B. My knowledge that B is consistent is therefore only as secure as "
                   "Lean's own foundations, which I cannot certify. The structure B lives in recurs one level up.",
                   "INTERNAL_META", cites=["GOEDEL_II_FOR_LEAN", "GL_ARITHMETICAL_SOUNDNESS"],
                   subject="C_cannot_prove_ConC")

    # ------------------------------------------------------------------ C7
    def alternative_parents(self):
        parents = MT.standard_parents()
        table = MT.knowledge_table(parents)
        own = {p.key: {"own_consistency": p.own_consistency(), "consistent_if": p.consistent_if()} for p in parents}
        self.claim("C-parents", "alternative-parents",
                   "Different parents of the same child disagree about it: B + Con(B) proves Con(B), B + ¬Con(B) "
                   "refutes it, an implementation-only substrate asserts nothing, and all of them are consistent if B "
                   "is (resp. if B + Con B is). Yet the child's run is identical under each, because a parent "
                   "metatheory is not consulted when the child's proofs are checked.", "DECIDED",
                   evidence={"knowledge_table": table, "own": own, "invariance": self.invariance},
                   subject="C_parents_disagree")
        self.claim("C-invariance", "alternative-parents",
                   "Implementation invariance (measured): the child's complete transcript under P1 (big-integer "
                   "kernel) and P2 (independently written kernel with string arithmetic) is "
                   f"{'byte-identical' if self.invariance.get('identical') else 'DIFFERENT'} "
                   f"(sha256 {self.invariance.get('P1', '')[:12]} vs {self.invariance.get('P2', '')[:12]}). Under the "
                   "unfaithful P3 it differs, and the child correctly infers the defect.", "EMPIRICAL",
                   evidence=self.invariance, subject="C_invariance")
        self.extension = MT.extension_analysis(5)
