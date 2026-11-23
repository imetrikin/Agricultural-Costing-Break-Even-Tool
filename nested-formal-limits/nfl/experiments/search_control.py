"""Control 6b: the same true, PA-provable statements under different search budgets and prior knowledge.

Shows that 'not found' depends on the searcher's state (budget, induction depth, known lemmas) and is
therefore not a property of the statement.
"""
from __future__ import annotations

from ..logic import kernel as K
from ..logic.syntax import forall_many, parse
from ..logic.theories import peano
from ..prover.explore import explore
from ..prover.induction import Budget, InductionProver, SearchFailure

GOALS = [
    ("add_comm", "x + y = y + x", ["x", "y"]),
    ("add_assoc", "(x + y) + z = x + (y + z)", ["x", "y", "z"]),
    ("mul_comm", "x * y = y * x", ["x", "y"]),
    ("distrib_right", "(x + y) * z = x * z + y * z", ["x", "y", "z"]),
    ("mul_assoc", "(x * y) * z = x * (y * z)", ["x", "y", "z"]),
]


def attempt(prover, theory, lib, goal, budget):
    name, g, vs = goal
    f = parse(g)
    b = Budget(budget)
    try:
        p, c = prover.prove(f.args[0], f.args[1], vs, b)
        K.Checker(theory, lib).check_theorem(p, forall_many(vs, f))
        return {"status": "proved", "steps": b.used, "proof_nodes": K.proof_size(p)}
    except (SearchFailure, RecursionError) as e:
        return {"status": "not found", "steps": b.used}


def run(budgets=(25, 100, 400, 1600, 6400)):
    T = peano()
    rows = []
    for knowledge in ("axioms only", "after theory exploration"):
        for depth in (1, 2, 3):
            lib = K.Library(T)
            prover = InductionProver(T, lib, max_depth=depth)
            if knowledge != "axioms only":
                explore(T, lib, K.Checker(T, lib), prover, max_size=6, budget_per_goal=1500, max_goals=250)
            for goal in GOALS:
                row = {"knowledge": knowledge, "induction_depth": depth, "goal": goal[0]}
                for b in budgets:
                    row[f"budget {b}"] = attempt(prover, T, lib, goal, b)["status"]
                rows.append(row)
    return rows
