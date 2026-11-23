"""Σ1-completeness tactic: decisions must match the standard model and be kernel-accepted."""
import random

from nfl.logic import kernel as K
from nfl.logic.syntax import Add, And, Eq, Forall, Imp, Lt, Mul, Not, Or, Var, num, parse
from nfl.logic.theories import peano
from nfl.prover.arith import ArithProver, closed_value

T = peano()


def rand_term(rng, d=2):
    if d == 0 or rng.random() < 0.3:
        return num(rng.randint(0, 6))
    op = rng.choice([Add, Mul])
    return op(rand_term(rng, d - 1), rand_term(rng, d - 1))


def test_random_closed_atoms():
    rng = random.Random(1)
    A = ArithProver(T)
    C = K.Checker(T)
    for _ in range(60):
        a, b = rand_term(rng), rand_term(rng)
        f = Eq(a, b) if rng.random() < 0.5 else Lt(a, b)
        truth = (closed_value(a) == closed_value(b)) if f.pred == "=" else (closed_value(a) < closed_value(b))
        v, (p, c) = A.decide(f)
        assert v == truth
        C.check_theorem(p, f if v else Not(f))


def test_bounded_quantifiers():
    A = ArithProver(T)
    C = K.Checker(T)
    for s, truth in [("forall x < 6. exists y < 7. x + 1 = y", True),
                     ("exists x < 10. x * x = 50", False),
                     ("forall x < 5. x * x < 17", True)]:
        f = parse(s)
        v, (p, c) = A.decide(f)
        assert v == truth
        C.check_theorem(p, f if v else Not(f))
