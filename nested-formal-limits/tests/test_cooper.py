"""Cooper's procedure vs brute force (bounded sentences) and vs Z3 (unbounded)."""
import itertools
import random

import pytest

from nfl.agents.agent_a import random_sentence
from nfl.logic.syntax import Atom, Bot, And, Exists, Forall, Imp, Or, parse
from nfl.presburger import cooper
from nfl.presburger.definability import profile, check_profile, refute_definition
from nfl.prover.arith import closed_value
from nfl.logic.syntax import subst1, num


def brute(f, bound=12):
    """Evaluate with all quantifiers restricted to [0, bound) -- exact for formulas whose
    quantifiers are explicitly bounded below `bound`."""
    if isinstance(f, Bot):
        return False
    if isinstance(f, Atom):
        a, b = (closed_value(t) for t in f.args)
        return a == b if f.pred == "=" else a < b
    if isinstance(f, Imp):
        return (not brute(f.a, bound)) or brute(f.b, bound)
    if isinstance(f, And):
        return brute(f.a, bound) and brute(f.b, bound)
    if isinstance(f, Or):
        return brute(f.a, bound) or brute(f.b, bound)
    vals = (brute(subst1(f.body, f.var, num(k)), bound) for k in range(bound))
    return all(vals) if isinstance(f, Forall) else any(vals)


@pytest.mark.parametrize("s", [
    "forall x < 10. exists y < 10. x + y = 9",
    "exists x < 8. x + x + x = 7",
    "forall x < 9. forall y < 9. x < y | y < x | x = y",
    "forall x < 7. (exists y < 7. x = y + y) | (exists y < 7. x = y + y + 1)",
])
def test_bounded_vs_brute(s):
    f = parse(s)
    assert cooper.decide(f) == brute(f)


def test_known_unbounded():
    assert cooper.decide(parse("forall x. 7 < x -> exists a b. x = a+a+a+b+b+b+b+b"))
    assert not cooper.decide(parse("forall x. 6 < x -> exists a b. x = a+a+a+b+b+b+b+b"))
    assert not cooper.decide(parse("forall x. exists y. y < x"))


def test_profile_matches_direct_decision():
    phi = parse("exists y. x = y + y + y + 1 | x < 4")
    ups, info = profile(phi, "x")
    assert info["structure_ok"]
    assert check_profile(phi, "x", ups, upto=40)


def test_square_refutation_has_verified_counterexample():
    phi = parse("exists y. x = y + y + y + y")
    r = refute_definition(phi, "x", "squares")
    assert r["verified"]


def test_against_z3():
    z3 = pytest.importorskip("z3")
    from nfl.experiments.crosschecks import cooper_vs_z3
    r = cooper_vs_z3(40, seed=99)
    assert r["disagree"] == 0
