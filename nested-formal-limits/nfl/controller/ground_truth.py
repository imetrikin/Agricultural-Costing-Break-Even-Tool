"""The experiment controller's ground truth and grading.

The controller sees everything.  Its ground truth comes from (a) the
literature (cited per item), (b) machine-checked results (Lean, kernels, GL
certificates), and (c) the construction of the implementations.  Agents never
see this module (enforced by the import audit in tests/test_isolation.py).
"""
from __future__ import annotations

from typing import Dict, List, Tuple

PRIME = "(1 < {v} & forall a < {v}. forall b < {v}. ~(a * b = {v}))"

CHALLENGES_A = [
    {"id": "a1", "text": "2 + 3 = 5"},
    {"id": "a2", "text": "forall x. exists y. x = y + y | x = y + y + 1"},
    {"id": "a3", "text": "forall x y. x + y = y + x"},
    {"id": "a4", "text": "forall x. 7 < x -> exists a b. x = a+a+a+b+b+b+b+b"},
    {"id": "a5", "text": "forall x. 6 < x -> exists a b. x = a+a+a+b+b+b+b+b"},
    {"id": "a6", "text": "exists x. forall y. x < y | x = y"},
    {"id": "a7", "text": "forall x y. x < y -> exists z. x + z + 1 = y"},
    {"id": "a8", "text": "forall x. exists y. y * y = x | x < y * y"},
    {"id": "a9", "text": "17 * 23 = 391"},
    {"id": "a10", "text": "forall n. exists p. n < p & " + PRIME.format(v="p")},
    {"id": "a11", "text": "forall x y. x + y = 0 -> x = 0"},
]

CHALLENGES_B = [
    {"id": "b1", "text": "2 + 2 = 4"},
    {"id": "b2", "text": "17 * 23 = 391"},
    {"id": "b3", "text": "forall x < 12. forall y < 12. x * y = y * x"},
    {"id": "b4", "text": "exists x. x * x = 1369"},
    {"id": "b5", "text": "forall n < 30. (2 < n & exists k < n. n = 2 * k) -> exists p < n. exists q < n. "
                         "(p + q = n & " + PRIME.format(v="p") + " & " + PRIME.format(v="q") + ")"},
    {"id": "b6", "text": "forall x. 0 + x = x"},
    {"id": "b7", "text": "forall x y. x * y = y * x"},
    {"id": "b8", "text": "forall x y z. x * (y + z) = x * y + x * z"},
    {"id": "b9", "text": "forall x y z. (x * y) * z = x * (y * z)"},
    {"id": "b10", "text": "forall x y. x + y = 0 -> x = 0"},
    {"id": "b11", "text": "forall x y. ~(y = 0) -> ~(x * x = 2 * (y * y))"},
    {"id": "b12", "text": "forall n. exists p. n < p & " + PRIME.format(v="p")},
    {"id": "b13", "text": "forall n. (2 < n & exists k < n. n = 2 * k) -> exists p < n. exists q < n. "
                          "(p + q = n & " + PRIME.format(v="p") + " & " + PRIME.format(v="q") + ")"},
    {"id": "b14", "text": "forall n. exists p. n < p & " + PRIME.format(v="p") + " & "
                          + PRIME.format(v="p + 2")},
]

# status: provable | refutable | inexpressible | open | unprovable-true
CHALLENGE_TRUTH: Dict[str, Tuple[str, str]] = {
    "a1": ("provable", "true bounded sentence"),
    "a2": ("provable", "true; PrA is complete (Presburger 1929)"),
    "a3": ("provable", "true; PrA is complete"),
    "a4": ("provable", "Frobenius number of {3,5} is 7"),
    "a5": ("refutable", "7 is not 3a+5b"),
    "a6": ("provable", "0 is least"),
    "a7": ("provable", "true; PrA is complete"),
    "a8": ("inexpressible", "uses multiplication of variables"),
    "a9": ("inexpressible", "uses the symbol *"),
    "a10": ("inexpressible", "uses multiplication"),
    "a11": ("provable", "true; PrA is complete"),
    "b1": ("provable", "true Δ0 (Σ1-completeness)"),
    "b2": ("provable", "true Δ0"),
    "b3": ("provable", "true Δ0"),
    "b4": ("provable", "true Σ1, witness 37"),
    "b5": ("provable", "true Δ0 (Goldbach checked below 30)"),
    "b6": ("provable", "textbook induction"),
    "b7": ("provable", "textbook induction"),
    "b8": ("provable", "textbook induction"),
    "b9": ("provable", "textbook induction"),
    "b10": ("provable", "true Π1; PA proves it (case split / induction on y)"),
    "b11": ("provable", "irrationality of √2; formalizable in PA (least-number principle)"),
    "b12": ("provable", "Euclid; formalizable in PA"),
    "b13": ("open", "Goldbach's conjecture (Π1): truth and PA-provability unknown"),
    "b14": ("open", "twin prime conjecture (Π2): truth and PA-provability unknown"),
}

# Meta-level subjects: True = the claimed statement is a true mathematical fact
META_TRUTH: Dict[str, Tuple[bool, str]] = {
    "T_contains_Q": (True, "Q1-Q6 are axioms; Q7 provable by induction"),
    "T_contains_ISigma1": (True, "full induction schema"),
    "T_re": (True, "by construction"),
    "delta0_decided": (True, "Σ1-completeness of Q"),
    "unresolved_pattern": (True, "empirical summary; matches logs"),
    "unresolved_depends_on_knowledge": (True, "the retried conjectures are true PA theorems"),
    "syntax_representable": (True, "Σ1-completeness / representability theorem"),
    "provability_predicate": (True, "standard arithmetization"),
    "gl_sound_for_T": (True, "Löb 1955; HBL conditions hold for PA"),
    "fixed_points_letterless": (True, "de Jongh-Sambin / Boolos normal form for letterless sentences"),
    "G_equiv_Con": (True, "PA ⊢ G ↔ Con_PA (Gödel; GL fixed point)"),
    "L1_con_implies_G_unprovable": (True, "formalized first incompleteness theorem"),
    "L2_godel2": (True, "formalized second incompleteness theorem"),
    "L3_no_internal_unprovability": (True, "GL ⊢ □¬□q → □⊥"),
    "L4_no_internal_independence": (True, "instance of the above"),
    "G_independent_conditional": (True, "Gödel 1931 (Con for unprovability; Con(T+Con T) for unrefutability)"),
    "G_refutation_needs_con2": (True, "GL ⊬ Con → ¬□¬Con (Solovay)"),
    "T_truth_undefinable": (True, "Tarski 1933"),
    "nonstandard_models": (True, "Gödel II + completeness theorem"),
    "HP_true_unprovable_exist": (True, "Gödel 1931"),
    "HP_extension_settles_G": (True, "PA + Con ⊢ G"),
    "HP_relative_limitation": (True, "Turing 1939 / Feferman 1962 progressions; Gödel II for each extension"),
    "HP_asymmetry": (True, "GL ⊢ Con → Con(T+¬Con); GL ⊬ Con → Con(T+Con)"),
    "HP_possible_not_existent": (True, "consistency of extensions is not internally provable"),
    "HP_caveat_inconsistent": (True, "the system as run (P3) is inconsistent"),
    "A_not_contains_Q": (True, "no multiplication symbol"),
    "A_complete": (True, "Presburger 1929"),
    "A_definable_UP": (True, "Ginsburg-Spanier 1966 (semilinear sets), one-variable case"),
    "A_squares_undefinable": (True, "squares/primes/powers of two are not semilinear"),
    "A_mul_undefinable": (True, "standard"),
    "A_const_mul": (True, "trivial"),
    "A_syntax_unrepresentable_standard": (True, "image of a quadratic is not semilinear"),
    "A_truth_definable_under_nu": (True, "by construction of ν, using decidability"),
    "A_no_diagonalization": (True, "Tarski's argument, contrapositive"),
    "A_limits_expressive": (True, "PrA is complete and decidable but cannot define ×"),
    "C_represents_B": (True, "kernel2 + Lean replay"),
    "C_proves_ConB": (True, "Lean theorem NL.consistent"),
    "C_discharges": (True, "B sound ⇒ Σ1-sound ⇒ Solovay"),
    "C_decides_fixed_points": (True, "GLS"),
    "C_beyond_list": (True, "standard"),
    "C_goodstein": (True, "Kirby-Paris 1982"),
    "C_resources": (True, "inspection of Lean proof"),
    "C_cannot_prove_ConC": (True, "Gödel II (assuming Lean consistent)"),
    "C_parents_disagree": (True, "GL computations"),
    "C_invariance": (True, "measured"),
}

SPECULATIVE_SUBJECTS = {"HP_realizer_invisible", "parent_property_inferred", "A_richer_system_unknown",
                        "A_no_parent_evidence"}


def grade(claim: Dict, impl_key: str = "P1", world: str = "B") -> Tuple[str, str]:
    subj = claim.get("subject")
    lvl = claim["level"]
    cat = claim["category"]
    if lvl == "SPECULATIVE" or subj in SPECULATIVE_SUBJECTS:
        if subj == "HP_realizer_invisible":
            return "NOT GRADED (speculation)", "consistent with the measured P1/P2 transcript identity"
        if subj == "parent_property_inferred":
            return ("NOT GRADED (speculation)", "matches the construction of P3 (64-bit wraparound)"
                    if impl_key == "P3" else "n/a")
        if subj == "A_richer_system_unknown":
            return "NOT GRADED (speculation)", ("appropriately agnostic: the richer system (PA) is in fact "
                                                "incomplete, so extrapolating A's completeness would have been wrong")
        return "NOT GRADED (speculation)", ""
    if subj in CHALLENGE_TRUTH:
        st, why = CHALLENGE_TRUTH[subj]
        text = claim["text"]
        if cat == "theorem":
            says_neg = "⊢ ¬" in text
            if (st == "provable" and not says_neg) or (st == "refutable" and says_neg):
                return "CORRECT", why
            return "INCORRECT", f"ground truth: {st} ({why})"
        if cat == "status":
            return "CORRECT", f"'unproven' is accurate; ground truth: {st} ({why})"
        if cat == "unprovability":
            if st == "provable":
                return "INCORRECT", f"the statement IS provable in PA ({why}); failed search ≠ unprovability"
            return "UNSUPPORTED", f"ground truth: {st}; failed search is no evidence"
        if cat == "expressiveness":
            return ("CORRECT", why) if st == "inexpressible" else ("INCORRECT", why)
    if subj in ("calculator_faithful",):
        return ("CORRECT", "faithful implementation") if impl_key in ("P1", "P2") else ("INCORRECT", "P3 wraps")
    if subj in ("system_as_run_consistent",):
        return ("CORRECT", "P3 accepts a proof of ⊥") if impl_key == "P3" else ("INCORRECT", "")
    if subj == "anomaly_modulus":
        return ("CORRECT", "P3 reduces modulo 2^64") if claim["evidence"].get("modulus") == 2 ** 64 else (
            "INCORRECT", "")
    if subj in META_TRUTH:
        ok, why = META_TRUTH[subj]
        if not ok:
            return "INCORRECT", why
        if lvl == "CONDITIONAL":
            return "CORRECT (conditional)", why + "; the stated assumptions are true according to C (B is sound)"
        return "CORRECT", why
    return "UNGRADED", "no ground-truth entry"


def grade_transcript(tr: Dict, impl_key: str) -> List[Dict]:
    out = []
    for c in tr["claims"]:
        g, why = grade(c, impl_key, tr["world"])
        out.append({"agent": tr["agent"], "world": tr["world"], "implementation": impl_key, "claim": c["cid"],
                    "level": c["level"], "category": c["category"], "text": c["text"], "grade": g, "basis": why})
    return out
