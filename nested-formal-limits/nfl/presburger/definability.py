"""What can Environment A *express*?

Structure theorem used (and checked on every QE output we produce): after
quantifier elimination, a formula φ(x) with one free variable is a Boolean
combination of atoms  0 < a·x + c,  a·x + c = 0,  d | a·x + c.  Each atom is
periodic in x beyond |c|/|a| with period d, hence φ defines an *ultimately
periodic* set (threshold N, period p).  This is the one-variable case of the
Ginsburg–Spanier theorem (Presburger-definable = semilinear).

Non-definability results then reduce to elementary facts: a set that is not
ultimately periodic (squares, primes, powers of two, the image of x ↦ x·x)
is not definable; hence multiplication is not definable (its diagonal would
define the squares).  For each concrete candidate formula the agent also gets
a *finite, checkable* counterexample.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from functools import reduce
from typing import Callable, Dict, List, Optional, Tuple

from ..logic.syntax import Formula, formula_str, num, subst1
from .cooper import QEStats, atoms, atom_lin, eval_qf, lcm, qe_formula, decide


@dataclass
class UPSet:
    """Ultimately periodic subset of ℕ: membership of n ≥ threshold repeats with `period`."""
    threshold: int
    period: int
    bits: Tuple[bool, ...]   # membership for 0 .. threshold+period-1

    def __contains__(self, n: int) -> bool:
        if n < len(self.bits):
            return self.bits[n]
        return self.bits[self.threshold + (n - self.threshold) % self.period]

    def describe(self, limit=30) -> str:
        mem = [n for n in range(limit) if n in self]
        return f"threshold={self.threshold}, period={self.period}, first members={mem}"


def profile(phi: Formula, var: str) -> Tuple[UPSet, dict]:
    """Ultimately-periodic profile of {n ∈ ℕ : φ(n)} computed from the QE normal form."""
    if phi.fv() - {var}:
        raise ValueError("profile expects exactly one free variable")
    st = QEStats()
    q = qe_formula(phi, st)
    thr, per = 0, 1
    structure_ok = True
    for a in atoms(q):
        L = atom_lin(a)
        if L.vars() - {var}:
            structure_ok = False
        c = L.coeff(var)
        if a[0] in ("lt", "eq"):
            if c != 0:
                thr = max(thr, abs(L.k) // abs(c) + 2)
        else:
            per = lcm(per, a[1])
    bits = tuple(eval_qf(q, {var: n}) for n in range(thr + per))
    return UPSet(thr, per, bits), {"qe_atoms": sum(1 for _ in atoms(q)), "eliminations": st.eliminations,
                                   "structure_ok": structure_ok}


def check_profile(phi: Formula, var: str, ups: UPSet, upto: int = 60) -> bool:
    """Independent cross-check: decide φ(n) sentence-by-sentence and compare."""
    for n in range(upto):
        if decide(subst1(phi, var, num(n))) != (n in ups):
            return False
    return True


# ---------------------------------------------------------------------------
# Target sets that need multiplication
# ---------------------------------------------------------------------------


def is_square(n: int) -> bool:
    r = math.isqrt(n)
    return r * r == n


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for d in range(2, math.isqrt(n) + 1):
        if n % d == 0:
            return False
    return True


def is_pow2(n: int) -> bool:
    return n > 0 and n & (n - 1) == 0


TARGETS: Dict[str, Callable[[int], bool]] = {
    "squares": is_square,
    "primes": is_prime,
    "powers_of_two": is_pow2,
}


def not_ultimately_periodic_witness(name: str, N: int, p: int) -> Tuple[int, int]:
    """For target `name` and any (threshold N, period p ≥ 1) return n ≥ N with
    target(n) ≠ target(n + p) -- a finite certificate that the target set has no
    ultimately periodic description with these parameters.

    Proof sketches (each instance is verified numerically by the caller):
      squares: n = k² with k ≥ max(√N, p) ⇒ k² < k² + p < (k+1)².
      powers of two: n = 2^k ≥ max(N, p+1) ⇒ 2^k < 2^k + p < 2^{k+1}.
      primes: q prime ≥ max(N, 2) and q ∤ p; then q + q·p is composite, so walking
              q, q+p, ..., q+q·p some consecutive pair differs.
    """
    target = TARGETS[name]
    if name == "squares":
        k = max(math.isqrt(N) + 1, p + 1)
        return k * k, p
    if name == "powers_of_two":
        k = max(N, p + 1, 1).bit_length()
        return 2 ** k, p
    if name == "primes":
        q = max(N, 2)
        while not (is_prime(q) and p % q != 0):
            q += 1
        n = q
        for i in range(q + 1):
            if target(n) != target(n + p):
                return n, p
            n += p
        raise AssertionError("no witness found (should be impossible)")
    raise KeyError(name)


def refute_definition(phi: Formula, var: str, name: str) -> dict:
    """Given a candidate definition φ(x) of a target set, produce a checkable counterexample."""
    ups, info = profile(phi, var)
    n, p = not_ultimately_periodic_witness(name, ups.threshold, ups.period)
    target = TARGETS[name]
    # one of n, n+p is a point where φ and the target disagree (φ is periodic there)
    for m in (n, n + p):
        if (m in ups) != target(m):
            # double-check by deciding the sentence φ(m) directly
            direct = decide(subst1(phi, var, num(m)))
            return {"candidate": formula_str(phi), "target": name, "counterexample": m,
                    "candidate_says": direct, "target_says": target(m), "profile": ups.describe(),
                    "verified": direct != target(m)}
    raise AssertionError("periodicity argument failed")
