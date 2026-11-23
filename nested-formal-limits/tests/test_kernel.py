"""The trusted kernel must accept valid proofs and reject invalid ones; kernel2 must agree."""
import pytest

from nfl.logic import kernel as K
from nfl.logic import kernel2 as K2
from nfl.logic.syntax import (
    ZERO, Add, And, Eq, Exists, Forall, Imp, Lt, Mul, Not, Or, S, Var, alpha_eq, parse, subst1,
)
from nfl.logic.theories import peano, presburger

T = peano()
x, y = Var("x"), Var("y")


def both(proof, stmt, theory=T):
    a = b = True
    try:
        K.Checker(theory).check_theorem(proof, stmt)
    except K.ProofError:
        a = False
    try:
        K2.Checker2(theory).check_theorem(proof, stmt)
    except K2.Reject:
        b = False
    return a, b


def zero_add_proof():
    phi = parse("0 + x = x")
    base = K.ax("Q3_add_zero", [ZERO])
    st = K.esubst(K.hyp(phi), K.ax("Q4_add_succ", [ZERO, x]), "z", Eq(Add(ZERO, S(x)), S(Var("z"))))
    step = K.allI(K.impI(st, phi), "x")
    return K.impE(K.schema("IND", ("x", phi)), K.andI(base, step)), Forall("x", phi)


def test_induction_proof_accepted_by_both():
    p, f = zero_add_proof()
    assert both(p, f) == (True, True)


def test_eigenvariable_violation_rejected():
    h = K.hyp(parse("0 + x = x"))
    assert both(K.allI(h, "x"), parse("forall x. 0 + x = x")) == (False, False)


def test_open_assumption_rejected():
    f = parse("0 = 0")
    assert both(K.hyp(f), f) == (False, False)


def test_language_violation_rejected():
    prA = presburger()
    p = K.ax("Q3_add_zero", [Mul(x, x)])
    assert both(p, Eq(Add(Mul(x, x), ZERO), Mul(x, x)), prA) == (False, False)


def test_wrong_instance_rejected():
    p = K.ax("Q3_add_zero", [x])
    assert both(p, parse("x + 0 = 0")) == (False, False)


def test_mismatched_modus_ponens_rejected():
    p = K.impE(K.ax("Q1_succ_ne_zero", [ZERO]), K.refl(ZERO))
    assert both(p, Eq(ZERO, ZERO)) == (False, False)


def test_unknown_axiom_rejected():
    assert both(K.ax("Q5_mul_zero", [x]), parse("x * 0 = 0"), presburger()) == (False, False)


def test_compute_disabled_without_evaluator():
    p = K.compute(Add(S(ZERO), S(ZERO)))
    with pytest.raises(K.ProofError):
        K.Checker(T).check_theorem(p, None)


def test_capture_avoiding_substitution():
    f = Forall("y", Lt(x, y))
    g = subst1(f, "x", y)
    assert isinstance(g, Forall) and g.var != "y"
    assert alpha_eq(g, Forall("w", Lt(y, Var("w"))))


def test_raa_and_exists_elimination():
    # from ∃y (x = S y) derive ¬(x = 0)
    hx = parse("exists y. x = S(y)")
    inner_h = Eq(x, S(y))
    eq0 = Eq(x, ZERO)
    # under x = S y and x = 0: S y = 0 contradicts Q1
    sy_eq_x = K.esubst(K.hyp(inner_h), K.refl(x), "z", Eq(Var("z"), x))          # x = x  -> S y = x
    sy_eq_0 = K.esubst(K.hyp(eq0), sy_eq_x, "z", Eq(S(y), Var("z")))             # S y = 0
    bot = K.impE(K.ax("Q1_succ_ne_zero", [y]), sy_eq_0)
    p = K.impI(K.impI(K.exE(K.hyp(hx), bot, "y"), eq0), hx)
    stmt = Imp(hx, Not(eq0))
    assert both(p, stmt) == (True, True)
