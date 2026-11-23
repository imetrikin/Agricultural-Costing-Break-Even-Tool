"""Parent *implementations*: the computational substrates that run a child's proof checker.

An implementation is what the child's world "runs on".  It is distinct from a
parent *metatheory* (a formal system that proves things about the child; see
metatheories.py).  The experiment uses:

  P1  reference      kernel.py, closed-term evaluation with Python big integers
  P2  independent    kernel2.py (separately written, locally-nameless), decimal-string arithmetic
  P3  glitch64       kernel.py, but the `compute` rule evaluates modulo 2^64
                     (a deliberately unfaithful parent, modelling finite-precision hardware)

P1 and P2 are *faithful*: they accept exactly the same proofs.  P3 is not.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Optional

from ..logic import kernel as K
from ..logic import kernel2 as K2
from ..prover.arith import closed_value


class ImplementationRejection(Exception):
    pass


@dataclass
class Implementation:
    name: str
    description: str
    faithful: bool

    def checker(self, theory, library: Optional[K.Library] = None):
        raise NotImplementedError


class _P1Checker:
    def __init__(self, theory, library, evaluator):
        self.k = K.Checker(theory, library, evaluator=evaluator)
        self._ev = evaluator

    def evaluate(self, t) -> int:
        return self._ev(t)

    def check_theorem(self, proof, expected=None):
        try:
            return self.k.check_theorem(proof, expected)
        except K.ProofError as e:
            raise ImplementationRejection(str(e)) from None

    def register_lemma(self, name, proof, statement):
        pass  # P1 reads lemmas from the shared Library object, which only holds checked theorems


class _P2Checker:
    def evaluate(self, t) -> int:
        return int(K2.s_eval(K2.db_term(t)))

    def __init__(self, theory, library, allow_compute):
        self.k = K2.Checker2(theory, allow_compute=allow_compute)
        if library is not None:
            for name in library.order:          # P2 re-checks every lemma itself
                self.k.add_lemma(name, library.proofs[name], library.thms[name])

    def check_theorem(self, proof, expected=None):
        try:
            self.k.check_theorem(proof, expected)
        except (K2.Reject, RecursionError, KeyError, TypeError, ValueError) as e:
            raise ImplementationRejection(str(e)) from None
        return expected

    def register_lemma(self, name, proof, statement):
        try:
            self.k.add_lemma(name, proof, statement)
        except K2.Reject as e:
            raise ImplementationRejection(str(e)) from None


class Reference(Implementation):
    def __init__(self):
        super().__init__("P1-reference", "kernel.py; machine big-integer evaluation", True)

    def checker(self, theory, library=None):
        return _P1Checker(theory, library, closed_value)


class Independent(Implementation):
    def __init__(self):
        super().__init__("P2-independent", "kernel2.py (separately written); decimal-string arithmetic", True)

    def checker(self, theory, library=None):
        return _P2Checker(theory, library, allow_compute=True)


class Glitch64(Implementation):
    MOD = 2 ** 64

    def __init__(self):
        super().__init__("P3-glitch64", "kernel.py, but `compute` wraps modulo 2^64 (unfaithful)", False)

    def checker(self, theory, library=None):
        return _P1Checker(theory, library, lambda t: closed_value(t) % self.MOD)


ALL = {"P1": Reference, "P2": Independent, "P3": Glitch64}
