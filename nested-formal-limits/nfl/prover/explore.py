"""Theory exploration: the agents' source of *self-generated* questions.

QuickSpec/Hipster-style: enumerate terms of the agent's own language,
group them by their values on sample inputs (in the standard model, which the
agent can compute with), propose equations between terms of the same class,
and try to prove them in increasing size, adding every kernel-checked theorem
as a new rewrite lemma.  Conjectures that survive testing but resist proof are
recorded as *unresolved* -- which is NOT evidence of unprovability.
"""
from __future__ import annotations

import itertools
import random
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Tuple

from ..logic import kernel as K
from ..logic.syntax import ZERO, Eq, Fn, Term, Var, forall_many, formula_str, num, subst_term, term_size, term_str
from .arith import closed_value
from .induction import Budget, InductionProver, Normalizer, SearchFailure, holds_on_samples, lpo_gt


def enumerate_terms(funcs: Dict[str, int], var_names: Sequence[str], max_size: int) -> List[Term]:
    by_size: Dict[int, List[Term]] = {1: [Var(v) for v in var_names] + [ZERO]}
    for size in range(2, max_size + 1):
        out = []
        if "S" in funcs:
            out += [Fn("S", (t,)) for t in by_size.get(size - 1, [])]
        for op in ("+", "*"):
            if op not in funcs:
                continue
            for ls in range(1, size - 1):
                rs = size - 1 - ls
                for a in by_size.get(ls, []):
                    for b in by_size.get(rs, []):
                        out.append(Fn(op, (a, b)))
        by_size[size] = out
    return [t for s in sorted(by_size) for t in by_size[s]]


def congruence_consequence(l: Term, r: Term):
    """If l = f(..a..), r = f(..b..) differ in one argument and a = b holds on samples,
    the equation is a congruence consequence of the smaller equation a = b."""
    if type(l) is Fn and type(r) is Fn and l.name == r.name and len(l.args) == len(r.args):
        diff = [i for i, (a, b) in enumerate(zip(l.args, r.args)) if a != b]
        if len(diff) == 1:
            a, b = l.args[diff[0]], r.args[diff[0]]
            vs = sorted(a.fv() | b.fv())
            if holds_on_samples(a, b, vs, n_max=4):
                return (a, b)
    return None


def canonical_vars(lhs: Term, rhs: Term) -> Tuple[Term, Term, Tuple[str, ...]]:
    order: List[str] = []

    def walk(t):
        if type(t) is Var:
            if t.name not in order:
                order.append(t.name)
        elif type(t) is Fn:
            for a in t.args:
                walk(a)
    walk(lhs)
    walk(rhs)
    names = ["x", "y", "z", "u", "v", "w"]
    ren = {v: Var(names[i]) for i, v in enumerate(order)}
    return subst_term(lhs, ren), subst_term(rhs, ren), tuple(names[: len(order)])


@dataclass
class ExplorationRecord:
    statement: str
    size: int
    status: str            # 'proved' | 'unresolved' | 'refuted' | 'subsumed'
    steps: int = 0
    proof_size: int = 0
    note: str = ""


@dataclass
class ExplorationResult:
    records: List[ExplorationRecord] = field(default_factory=list)
    proved: List[str] = field(default_factory=list)
    unresolved: List[str] = field(default_factory=list)


def explore(theory, library: K.Library, checker, prover: InductionProver,
            var_names=("x", "y", "z"), max_size: int = 7, budget_per_goal: int = 4000,
            max_goals: int = 400, seed: int = 0, prefix: str = "lem", rounds: int = 4,
            submit=None) -> ExplorationResult:
    """`checker` may be None if `submit(name, proof, statement) -> bool` is given; the
    submit callback must kernel-check the proof and add the theorem to `library`."""
    if submit is None:
        def submit(name, p, stmt):
            try:
                checker.check_theorem(p, stmt)
            except K.ProofError:
                return False
            library.thms[name] = stmt
            library.proofs[name] = p
            library.order.append(name)
            return True
    rng = random.Random(seed)
    terms = enumerate_terms(theory.funcs, var_names, max_size)
    samples = [{v: rng.randint(0, 12) for v in var_names} for _ in range(24)]

    def fp(t):
        return tuple(closed_value(subst_term(t, {k: num(v) for k, v in s.items()})) for s in samples)

    classes: Dict[tuple, List[Term]] = {}
    for t in terms:
        classes.setdefault(fp(t), []).append(t)
    cands = {}
    for cls in classes.values():
        if len(cls) < 2:
            continue
        cls = sorted(cls, key=lambda t: (term_size(t), term_str(t)))
        rep = cls[0]
        for other in cls[1:]:
            l, r, vs = canonical_vars(other, rep)
            if not vs:
                continue
            key = (term_str(l), term_str(r))
            if key not in cands:
                cands[key] = (l, r, vs)
    goals = sorted(cands.values(), key=lambda e: (term_size(e[0]) + term_size(e[1]), term_str(e[0])))
    res = ExplorationResult()
    attempts = 0
    pending = list(goals)
    for rnd in range(rounds):
        progress = False
        still = []
        seen = set()
        attempts = 0
        for (l, r, vs) in pending:
            # simplify with the oriented rules first and drop duplicates
            try:
                nm0 = Normalizer([ru for ru in prover._rules([]) if not ru.ordered], prover, Budget(2000))
                l0, r0 = nm0.norm(l)[0], nm0.norm(r)[0]
                if l0 != r0:
                    l0, r0, vs0 = canonical_vars(l0, r0)
                    if (term_str(r0), term_str(l0)) in seen or (term_str(l0), term_str(r0)) in seen:
                        continue
                    if not (l0 == l and r0 == r):
                        seen.add((term_str(l0), term_str(r0)))
                        l, r, vs = l0, r0, vs0
            except SearchFailure:
                pass
            seen.add((term_str(l), term_str(r)))
            cong = congruence_consequence(l, r)
            if cong is not None:
                res.records.append(ExplorationRecord(formula_str(forall_many(vs, Eq(l, r))),
                                                     term_size(l) + term_size(r), "subsumed",
                                                     note="congruence consequence of a smaller equation"))
                continue
            stmt = forall_many(vs, Eq(l, r))
            s = formula_str(stmt)
            size = term_size(l) + term_size(r)
            try:
                nm = Normalizer(prover._rules([]), prover, Budget(2000))
                if nm.norm(l)[0] == nm.norm(r)[0]:
                    note = f"round {rnd}"
                    # A joinable equation that LPO can orient is still worth keeping as a rule
                    # (e.g. associativity, which completes ordered AC-rewriting).
                    oriented_only = [ru for ru in prover._rules([]) if not ru.ordered]
                    nm2 = Normalizer(oriented_only, prover, Budget(2000))
                    l2, r2 = nm2.norm(l)[0], nm2.norm(r)[0]
                    if l2 != r2:
                        l2, r2, vs2 = canonical_vars(l2, r2)
                        orientable = (lpo_gt(l2, r2) and r2.fv() <= l2.fv()) or (lpo_gt(r2, l2) and l2.fv() <= r2.fv())
                        stmt2 = forall_many(vs2, Eq(l2, r2))
                        s2 = formula_str(stmt2)
                        if orientable and s2 not in res.proved:
                            try:
                                p, f = prover.prove(l2, r2, vs2, Budget(2000))
                                name = f"{prefix}{len(library.order)}"
                                if not submit(name, p, stmt2):
                                    raise K.ProofError("rejected by kernel")
                                prover.add_lemma_rules(name)
                                res.proved.append(s2)
                                res.records.append(ExplorationRecord(s2, term_size(l2) + term_size(r2), "proved", 0,
                                                                     K.proof_size(p),
                                                                     note=note + "; joinable only via permutative "
                                                                          "rules, kept as oriented rule"))
                                progress = True
                                continue
                            except (SearchFailure, K.ProofError):
                                pass
                    res.records.append(ExplorationRecord(s, size, "subsumed", note=note))
                    continue
            except SearchFailure:
                pass
            if attempts >= max_goals:
                still.append((l, r, vs))
                continue
            if not holds_on_samples(l, r, vs, n_max=5):
                res.records.append(ExplorationRecord(s, size, "refuted", note="counterexample in small model check"))
                continue
            attempts += 1
            b = Budget(budget_per_goal)
            try:
                p, f = prover.prove(l, r, vs, b)
                name = f"{prefix}{len(library.order)}"
                if not submit(name, p, stmt):
                    raise K.ProofError("rejected by kernel")
            except (SearchFailure, K.ProofError, RecursionError) as e:
                still.append((l, r, vs))
                continue
            prover.add_lemma_rules(name)
            res.records.append(ExplorationRecord(s, size, "proved", b.used, K.proof_size(p), note=f"round {rnd}"))
            res.proved.append(s)
            progress = True
        pending = still
        if not progress:
            break
    for (l, r, vs) in pending:
        s = formula_str(forall_many(vs, Eq(l, r)))
        res.records.append(ExplorationRecord(s, term_size(l) + term_size(r), "unresolved",
                                             note="tested true on all inputs < 5; no proof found within budget"))
        res.unresolved.append(s)
    return res
