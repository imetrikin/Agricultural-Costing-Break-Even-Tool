"""The *only* interface through which an artificial mathematician touches its world.

A World bundles: a theory (own language + axioms), the parent implementation
that runs the proof checker, a library of the agent's own checked theorems, and
world-internal computational primitives.  It exposes no information about the
implementation (name, code, faithfulness) and no information about any other
environment.  The controller constructs Worlds; agents receive only the World.

Isolation is enforced by construction plus a static import audit
(tests/test_isolation.py): agent modules may import only the logic/prover/
modal toolkits and this sandbox, never parents/, presburger/ (except agent A,
whose world *is* Presburger arithmetic), controller/, or other agents.
"""
from __future__ import annotations

from typing import Dict, List, Optional

from ..logic import kernel as K
from ..logic.syntax import Formula, Term, formula_str


class World:
    def __init__(self, label: str, theory, implementation, decision_procedure=None):
        self.__theory = theory
        self.__impl = implementation
        self.__library = K.Library(theory)
        self.__checker = implementation.checker(theory, self.__library)
        self.__decide = decision_procedure
        self.label = label
        self.submissions = 0
        self.accepted = 0
        self.kernel_steps = 0

    # -- what the inhabitant can know about its own mathematics ---------------------
    def language(self) -> Dict[str, Dict[str, int]]:
        return {"functions": dict(self.__theory.funcs), "predicates": dict(self.__theory.preds),
                "numeral_literals": self.__theory.numerals}

    def axioms(self) -> Dict[str, Formula]:
        return dict(self.__theory.axioms)

    def schemas(self) -> Dict[str, str]:
        return {k: (v.__doc__ or "").strip().splitlines()[0] for k, v in self.__theory.schemas.items()}

    def in_language(self, f: Formula) -> bool:
        return self.__theory.formula_ok(f)

    def term_in_language(self, t: Term) -> bool:
        return self.__theory.term_ok(t)

    # -- proof checking (performed by the substrate) ---------------------------------
    def check(self, proof: K.Proof, statement: Formula) -> bool:
        self.submissions += 1
        try:
            self.__checker.check_theorem(proof, statement)
        except Exception:
            return False
        self.accepted += 1
        return True

    def submit(self, name: str, proof: K.Proof, statement: Formula) -> bool:
        """Check a closed theorem and, if accepted, add it to the agent's library."""
        if not self.check(proof, statement):
            return False
        if statement.fv():
            return True
        lib = self.__library
        if name in lib:
            return True
        try:
            self.__checker.register_lemma(name, proof, statement)
        except Exception:
            return False
        lib.thms[name] = statement
        lib.proofs[name] = proof
        lib.order.append(name)
        return True

    def library(self) -> K.Library:
        """The agent's own library (read access; writes go through submit)."""
        return self.__library

    def proof_of(self, name: str) -> K.Proof:
        return self.__library.proofs[name]

    # -- world-internal computation --------------------------------------------------
    def calculate(self, t: Term) -> int:
        """The world's calculator: the same primitive the kernel's `compute` rule uses."""
        if t.fv() or not self.__theory.term_ok(t):
            raise ValueError("calculate expects a closed term of the language")
        return self.__checker.evaluate(t)

    def decide(self, sentence: Formula) -> Optional[bool]:
        """A decision procedure, if this world's mathematics has one (Environment A)."""
        if self.__decide is None:
            return None
        return self.__decide(sentence)

