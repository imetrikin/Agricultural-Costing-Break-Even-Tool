"""Shared agent infrastructure: notebooks, claims with evidence levels, and the
registry of *uniform* metatheorems an agent may cite.

Evidence levels (strongest first)
  KERNEL         a closed theorem of the agent's own theory, accepted by its kernel
  DECIDED        output of a terminating decision procedure, with an independently
                 checked certificate where available (GL tableau / countermodel;
                 Cooper QE cross-checked)
  INTERNAL_META  a statement about the agent's own provability, obtained from a GL
                 certificate plus cited uniform metatheorems whose hypotheses the agent
                 verified for its own theory; such statements are provable *in* the
                 agent's own theory (the cited theorems are formalizable there)
  CONDITIONAL    holds under an explicitly named assumption the agent cannot
                 establish internally (e.g. Con(T), Σ1-soundness)
  EMPIRICAL      instance tests, failed searches, statistics
  SPECULATIVE    interpretation; not mathematics

Policy for citations: an agent may cite only theorems that are *uniform* in the
theory ("for every theory T satisfying H ..."), never facts that name its own
system; it must record which hypotheses it checked and how.
"""
from __future__ import annotations

import json
from dataclasses import asdict, dataclass, field
from typing import Any, Dict, List, Optional

LEVELS = ["KERNEL", "DECIDED", "INTERNAL_META", "CONDITIONAL", "EMPIRICAL", "SPECULATIVE"]


@dataclass
class Claim:
    cid: str
    category: str
    text: str
    level: str
    formal: Optional[str] = None
    assumptions: List[str] = field(default_factory=list)
    cites: List[str] = field(default_factory=list)
    evidence: Dict[str, Any] = field(default_factory=dict)
    subject: Optional[str] = None      # key for ground-truth comparison

    def __post_init__(self):
        assert self.level in LEVELS, self.level


@dataclass
class Entry:
    phase: str
    kind: str          # 'question' | 'attempt' | 'result' | 'observation' | 'note'
    text: str
    data: Dict[str, Any] = field(default_factory=dict)


# ---------------------------------------------------------------------------
# Uniform metatheorems (general mathematics available to every agent)
# ---------------------------------------------------------------------------

UNIFORM_THEOREMS: Dict[str, Dict[str, str]] = {
    "SIGMA1_COMPLETENESS": {
        "statement": "If T ⊇ Q, every true Σ1 sentence is provable in T.",
        "hypotheses": "T contains Robinson's Q",
        "source": "standard (e.g. Boolos-Burgess-Jeffrey, Computability and Logic, ch. 16)",
        "formalizable_in_T": "yes (formalized Σ1-completeness is provable in IΣ1)",
    },
    "DIAGONAL_LEMMA": {
        "statement": "If T ⊇ Q and the coding is standard, for every formula ψ(x) there is a sentence σ "
                     "with T ⊢ σ ↔ ψ(⌜σ⌝).",
        "hypotheses": "T contains Q (represents the primitive recursive substitution function)",
        "source": "Gödel 1931; Carnap 1934",
        "formalizable_in_T": "yes",
    },
    "HBL_DERIVABILITY": {
        "statement": "For r.e. T ⊇ IΣ1 with its standard Σ1 provability predicate: (D1) T ⊢ φ ⇒ T ⊢ □φ; "
                     "(D2) T ⊢ □(φ→ψ) → (□φ → □ψ); (D3) T ⊢ □φ → □□φ.",
        "hypotheses": "T recursively axiomatized; T ⊇ IΣ1",
        "source": "Hilbert-Bernays 1939; Löb 1955; mechanized e.g. in Lean (FormalizedFormalLogic/Foundation)",
        "formalizable_in_T": "yes",
    },
    "GL_ARITHMETICAL_SOUNDNESS": {
        "statement": "If GL ⊢ A then T ⊢ A* for every arithmetical realization * (□ ↦ Prov_T).",
        "hypotheses": "HBL_DERIVABILITY hypotheses + DIAGONAL_LEMMA (for Löb's theorem)",
        "source": "Löb 1955; Boolos 1993, The Logic of Provability, ch. 3",
        "formalizable_in_T": "yes (each instance)",
    },
    "SOLOVAY_COMPLETENESS": {
        "statement": "If T ⊇ IΣ1 is r.e. and Σ1-sound, then GL ⊬ A implies T ⊬ A* for some realization; "
                     "for letterless A (fixed realization) GL ⊬ A implies T ⊬ A*.",
        "hypotheses": "T Σ1-sound (NOT verifiable inside T)",
        "source": "Solovay 1976; mechanized in Lean (Foundation)",
        "formalizable_in_T": "only conditionally on Σ1-soundness",
    },
    "TARSKI_UNDEFINABILITY": {
        "statement": "If the diagonal function is representable in T (and T is consistent), no formula Tr(x) "
                     "satisfies T ⊢ Tr(⌜σ⌝) ↔ σ for all sentences σ.",
        "hypotheses": "diagonal function representable in T",
        "source": "Tarski 1933/1936",
        "formalizable_in_T": "yes",
    },
    "GOEDEL_COMPLETENESS": {
        "statement": "Every consistent first-order theory has a model.",
        "hypotheses": "none (first-order logic)",
        "source": "Gödel 1930",
        "formalizable_in_T": "only in a stronger form (needs WKL0)",
    },
    "QE_LINEAR_ARITHMETIC": {
        "statement": "Cooper's procedure maps every formula of the language {0,S,+,<} to an equivalent "
                     "quantifier-free formula over atoms 0<L, L=0, d|L; each step is provable from the "
                     "successor/addition/order axioms with induction for that language.",
        "hypotheses": "the theory contains those axioms and that induction schema",
        "source": "Presburger 1929; Cooper 1972; mechanized in Isabelle (Nipkow 2008/2010)",
        "formalizable_in_T": "each instance",
    },
}


# Specific results about particular theories.  Only the PARENT (Agent C, which by
# construction has full access to the child's definition) may cite these.
PARENT_LITERATURE: Dict[str, Dict[str, str]] = {
    "KIRBY_PARIS_1982": {
        "statement": "Goodstein's theorem is true but not provable in PA.",
        "source": "L. Kirby, J. Paris, Bull. London Math. Soc. 14 (1982); Goodstein, JSL 9 (1944)",
    },
    "GENTZEN_1936": {
        "statement": "PA's consistency is provable in PRA + quantifier-free transfinite induction up to ε0.",
        "source": "G. Gentzen, Math. Annalen 112 (1936)",
    },
    "GOEDEL_II_FOR_LEAN": {
        "statement": "If Lean's type theory is consistent it does not prove its own consistency (Gödel II applies "
                     "to any consistent r.e. system interpreting enough arithmetic).",
        "source": "Gödel 1931; Lean's consistency strength: Carneiro, 'The Type Theory of Lean' (2019)",
    },
}


class Agent:
    """Base class.  Subclasses implement run()."""

    role = "agent"
    registry = UNIFORM_THEOREMS

    def __init__(self, world):
        self.world = world
        self.notebook: List[Entry] = []
        self.claims: List[Claim] = []
        self.cited: Dict[str, str] = {}

    def note(self, phase, kind, text, **data):
        self.notebook.append(Entry(phase, kind, text, data))

    def claim(self, cid, category, text, level, **kw) -> Claim:
        c = Claim(cid, category, text, level, **kw)
        for name in c.cites:
            if name not in self.registry:
                raise ValueError(f"{name} is not a theorem this agent may cite")
            self.cited[name] = self.registry[name]["statement"]
        self.claims.append(c)
        return c

    def transcript(self) -> Dict[str, Any]:
        return {
            "agent": self.role,
            "world": self.world.label,
            "notebook": [asdict(e) for e in self.notebook],
            "claims": [asdict(c) for c in self.claims],
            "cited_uniform_theorems": self.cited,
            "world_stats": {"submissions": self.world.submissions, "accepted": self.world.accepted},
        }

    def transcript_json(self) -> str:
        return json.dumps(self.transcript(), indent=1, sort_keys=True, default=str)
