"""Parent *metatheories*: formal systems that reason ABOUT the child B.

Distinct from implementations (implementations.py), which merely RUN B.

For the letterless provability sentences S about B (Boolean combinations of
□^n⊥, which by the GL analysis include B's Gödel sentence and its consistency
statements), what each parent proves is computable:

  syntactic parent B + X (X letterless):   proves S  iff  GL ⊢ X → S
      (⇐ by arithmetical soundness of GL; ⇒ by Solovay's theorem, assuming B is
       Σ1-sound -- which the semantic parent C_lean establishes)
  semantic parent (proves B sound):        proves S  iff  S is true in ℕ
      (the eventual value of S's trace; modulo the standard formalization of the
       arithmetized provability predicate inside the parent)
  implementation-only parent:              proves nothing about B; it only runs B's checker.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional

from ..modal import gl as G


@dataclass
class Metatheory:
    key: str
    name: str
    kind: str                 # 'semantic' | 'syntactic' | 'implementation-only'
    description: str
    extra_axiom: Optional[tuple] = None   # for syntactic parents B + X

    def decides(self, S) -> Optional[bool]:
        """True: proves S; False: proves ¬S; None: neither (or no opinion)."""
        if self.kind == "implementation-only":
            return None
        if self.kind == "semantic":
            return G.value_if_sound(S)
        X = self.extra_axiom
        if G.provable(G.Imp(X, S)):
            return True
        if G.provable(G.Imp(X, G.Not(S))):
            return False
        return None

    def own_consistency(self) -> Optional[str]:
        """Does the parent prove its own consistency?  (Only computable for syntactic parents.)"""
        if self.kind != "syntactic":
            return None
        X = self.extra_axiom
        own_con = G.Not(G.Box(G.Not(X)))          # Con(B + X) = ¬□¬X
        if G.provable(G.Imp(X, own_con)):
            return "proves its own consistency"
        if G.provable(G.Imp(X, G.Not(own_con))):
            return "proves its own INconsistency"
        return "neither"

    def consistent_if(self) -> str:
        if self.kind == "syntactic":
            X = self.extra_axiom
            # B + X consistent  iff  B ⊬ ¬X ; which letterless assumption makes ¬□¬X true?
            n = G.min_consistency_for(G.Not(X), True)
            return f"consistent iff B ⊬ ¬X; guaranteed by Con^{n}(B)" if n else "inconsistent"
        if self.kind == "semantic":
            return "relative to the consistency of the parent's own foundations (not provable by the parent)"
        return "n/a (makes no assertions)"


def standard_parents() -> List[Metatheory]:
    return [
        Metatheory("C_lean", "C-lean (Lean 4 CIC)", "semantic",
                   "Lean's type theory; proves soundness of B w.r.t. ℕ, hence Con(B) (machine-checked, "
                   "lean/NestedLimits/Proofs.lean)."),
        Metatheory("C_opt", "C-opt = B + Con(B)", "syntactic",
                   "The 'optimistic' syntactic parent: B plus its consistency statement.", G.con(1)),
        Metatheory("C_pess", "C-pess = B + ¬Con(B)", "syntactic",
                   "The 'pessimistic' parent: B plus the statement that B is inconsistent. Consistent if B is "
                   "(Gödel II), but Σ1-unsound.", G.Box(G.BOT)),
        Metatheory("C_con2", "C-tower2 = B + Con²(B)", "syntactic",
                   "Two steps up the Turing progression.", G.con(2)),
        Metatheory("C_impl", "C-impl (an implementation substrate)", "implementation-only",
                   "A machine that runs B's proof checker (a polynomial-time algorithm, formalizable in very weak "
                   "arithmetic) and makes no claims about B."),
    ]


SENTENCES = {
    "Con(B)": G.con(1),
    "G_B (≡ Con(B))": G.con(1),
    "¬Con(B)": G.Box(G.BOT),
    "Con(B + Con B)": G.con(2),
    "Con^3(B)": G.con(3),
    "□Con(B) (B proves its consistency)": G.Box(G.con(1)),
}


def knowledge_table(parents: List[Metatheory]) -> List[Dict]:
    rows = []
    for name, S in SENTENCES.items():
        row = {"sentence": name, "formal": G.show(S), "true_in_N_if_B_sound": G.value_if_sound(S)}
        for p in parents:
            d = p.decides(S)
            row[p.key] = "proves" if d is True else ("refutes" if d is False else "—")
        rows.append(row)
    return rows


def extension_analysis(max_n: int = 5) -> List[Dict]:
    """Control 5: the child extended by additional axioms.  For T_n = B + Con^n and for B + ¬Con."""
    rows = []
    for n in range(0, max_n + 1):
        X = G.con(n) if n > 0 else G.TOP
        own_con = G.Not(G.Box(G.Not(X)))                  # Con(T_n) ≡ Con^{n+1}
        # Gödel sentence of T_n:  G_n ↔ ¬□_{T_n} G_n  where □_{T_n} φ = □(X → φ)
        A = G.Not(G.Box(G.Imp(X, G.V("p"))))
        H, _ = G.letterless_fixed_point(A)
        rows.append({
            "theory": "B" if n == 0 else f"B + Con^{n}",
            "own_consistency_equiv_Con^": n + 1 if G.provable(G.Iff(own_con, G.con(n + 1))) else None,
            "proves_own_consistency": G.provable(G.Imp(X, own_con)),
            "goedel_sentence_equiv_own_consistency": G.provable(G.Imp(X, G.Iff(H, own_con))),
            "goedel_sentence_provable": G.provable(G.Imp(X, H)),
            "unprovability_needs": f"Con^{G.min_consistency_for(G.Imp(X, H), True)}",
        })
    X = G.Box(G.BOT)
    own_con = G.Not(G.Box(G.Not(X)))
    rows.append({"theory": "B + ¬Con(B)", "proves_own_consistency": G.provable(G.Imp(X, own_con)),
                 "proves_own_inconsistency": G.provable(G.Imp(X, G.Not(own_con))),
                 "consistent_given": "Con(B) (Gödel II: B ⊬ Con(B))"})
    return rows
