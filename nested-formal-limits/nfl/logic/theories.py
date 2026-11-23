"""Explicit axiomatizations of the environments' object theories.

Environment A  = PrA  (Presburger arithmetic)   language {0, S, +, <, =}
Environment B  = PA   (Peano arithmetic)        language {0, S, +, *, <, =}

Both use the same logical calculus (kernel.py).  `<` is a primitive symbol
governed by L1/L2; this is a definitional extension of the textbook
formulation where x < y abbreviates ∃z (x + S z = y) (L1, L2 and that
definition are inter-derivable with induction).  Numeral literals are
governed by the schema NUM:  n+1 = S(n), with 0 the constant.
"""
from __future__ import annotations

from .kernel import ProofError, Theory
from .syntax import (
    ZERO, And, Eq, Forall, Formula, Iff, Imp, Lt, Not, Or, S, Var, Add, Mul, num, parse, subst1,
)

x, y = Var("x"), Var("y")

SUCC_AXIOMS = {
    "Q1_succ_ne_zero": parse("forall x. ~(S(x) = 0)"),
    "Q2_succ_inj": parse("forall x y. S(x) = S(y) -> x = y"),
}
ADD_AXIOMS = {
    "Q3_add_zero": parse("forall x. x + 0 = x"),
    "Q4_add_succ": parse("forall x y. x + S(y) = S(x + y)"),
}
MUL_AXIOMS = {
    "Q5_mul_zero": parse("forall x. x * 0 = 0"),
    "Q6_mul_succ": parse("forall x y. x * S(y) = x * y + x"),
}
ORDER_AXIOMS = {
    "L1_not_lt_zero": parse("forall x. ~(x < 0)"),
    "L2_lt_succ": parse("forall x y. x < S(y) <-> (x < y | x = y)"),
}


def induction_instance(theory: Theory, params) -> Formula:
    """IND: (φ(0) ∧ ∀x (φ(x) → φ(Sx))) → ∀x φ(x), for any formula φ of the language."""
    if len(params) != 2:
        raise ProofError("IND takes (variable, formula)")
    v, phi = params
    if not isinstance(v, str) or not isinstance(phi, Formula):
        raise ProofError("IND takes (variable, formula)")
    theory.require_formula(phi)
    base = subst1(phi, v, ZERO)
    step = Forall(v, Imp(phi, subst1(phi, v, S(Var(v)))))
    return Imp(And(base, step), Forall(v, phi))


def numeral_instance(theory: Theory, params) -> Formula:
    """NUM: (n+1) = S(n) for numeral literals."""
    if len(params) != 1 or not isinstance(params[0], int) or params[0] < 0:
        raise ProofError("NUM takes a natural number")
    n = params[0]
    return Eq(num(n + 1), S(num(n)))


def presburger() -> Theory:
    ax = {}
    ax.update(SUCC_AXIOMS)
    ax.update(ADD_AXIOMS)
    ax.update(ORDER_AXIOMS)
    return Theory(
        name="PrA",
        funcs={"0": 0, "S": 1, "+": 2},
        preds={"=": 2, "<": 2},
        numerals=True,
        axioms=ax,
        schemas={"IND": induction_instance, "NUM": numeral_instance},
        description="Presburger arithmetic: successor, addition, order; induction for all formulas "
                    "of the language {0,S,+,<}. No multiplication symbol.",
    )


def peano() -> Theory:
    ax = {}
    ax.update(SUCC_AXIOMS)
    ax.update(ADD_AXIOMS)
    ax.update(MUL_AXIOMS)
    ax.update(ORDER_AXIOMS)
    return Theory(
        name="PA",
        funcs={"0": 0, "S": 1, "+": 2, "*": 2},
        preds={"=": 2, "<": 2},
        numerals=True,
        axioms=ax,
        schemas={"IND": induction_instance, "NUM": numeral_instance},
        description="Peano arithmetic (first order): Robinson's Q axioms for S,+,*, recursive "
                    "axioms for <, and the induction schema for all formulas of {0,S,+,*,<}.",
    )


def robinson_q() -> Theory:
    """Robinson arithmetic Q (no induction) -- used for hypothesis checks only."""
    ax = {}
    ax.update(SUCC_AXIOMS)
    ax.update(ADD_AXIOMS)
    ax.update(MUL_AXIOMS)
    ax.update(ORDER_AXIOMS)
    ax["Q7_zero_or_succ"] = parse("forall x. x = 0 | exists y. x = S(y)")
    return Theory(
        name="Q",
        funcs={"0": 0, "S": 1, "+": 2, "*": 2},
        preds={"=": 2, "<": 2},
        numerals=True,
        axioms=ax,
        schemas={"NUM": numeral_instance},
        description="Robinson arithmetic: PA without induction (plus Q7).",
    )


def describe(theory: Theory) -> str:
    from .syntax import formula_str
    lines = [f"Theory {theory.name}: {theory.description}",
             f"  function symbols: {theory.funcs}", f"  predicate symbols: {theory.preds}",
             "  axioms:"]
    for k, v in theory.axioms.items():
        lines.append(f"    {k}: {formula_str(v)}")
    for k in theory.schemas:
        doc = (theory.schemas[k].__doc__ or "").strip().splitlines()[0]
        lines.append(f"    schema {k}: {doc}")
    return "\n".join(lines)
