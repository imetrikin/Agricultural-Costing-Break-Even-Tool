"""Independent verification of the experiment's own tools.

  X1  Cooper QE vs Z3 on random Presburger sentences
  X2  kernel.py vs kernel2.py on every library proof, plus random proof mutations
  X3  GL tableau vs brute-force Kripke-model search; certificate checks
  X4  Lean replay (driven from run_all.py)
"""
from __future__ import annotations

import itertools
import random
from typing import Dict, List, Optional

from ..logic import kernel as K
from ..logic import kernel2 as K2
from ..logic.syntax import (
    Add, And, Atom, Bot, Eq, Exists, Fn, Forall, Formula, Imp, Lt, Not, Num, Or, S, Term, Var, num,
)
from ..modal import gl as G
from ..presburger import cooper


# ---------------------------------------------------------------- X1
def to_z3(f: Formula, env: Dict, z3):
    def tm(t: Term):
        if isinstance(t, Var):
            return env[t.name]
        if isinstance(t, Num):
            return z3.IntVal(t.value)
        if t.name == "0":
            return z3.IntVal(0)
        if t.name == "S":
            return tm(t.args[0]) + 1
        if t.name == "+":
            return tm(t.args[0]) + tm(t.args[1])
        raise ValueError(t.name)
    if isinstance(f, Bot):
        return z3.BoolVal(False)
    if isinstance(f, Atom):
        a, b = tm(f.args[0]), tm(f.args[1])
        return a == b if f.pred == "=" else a < b
    if isinstance(f, Imp):
        return z3.Implies(to_z3(f.a, env, z3), to_z3(f.b, env, z3))
    if isinstance(f, And):
        return z3.And(to_z3(f.a, env, z3), to_z3(f.b, env, z3))
    if isinstance(f, Or):
        return z3.Or(to_z3(f.a, env, z3), to_z3(f.b, env, z3))
    v = z3.Int(f"{f.var}_{len(env)}_{id(f) % 100000}")
    env2 = dict(env)
    env2[f.var] = v
    body = to_z3(f.body, env2, z3)
    if isinstance(f, Forall):
        return z3.ForAll([v], z3.Implies(v >= 0, body))
    return z3.Exists([v], z3.And(v >= 0, body))


def cooper_vs_z3(n: int = 200, seed: int = 7) -> Dict:
    try:
        import z3
    except ImportError:
        return {"skipped": "z3 not installed"}
    from ..agents.agent_a import random_sentence
    rng = random.Random(seed)
    agree = disagree = unknown = 0
    examples = []
    for _ in range(n):
        f = random_sentence(rng, depth=rng.randint(1, 3))
        ours = cooper.decide(f)
        s = z3.Solver()
        s.set("timeout", 10000)
        s.add(z3.Not(to_z3(f, {}, z3)))
        r = s.check()
        theirs = True if r == z3.unsat else (False if r == z3.sat else None)
        if theirs is None:
            unknown += 1
        elif theirs == ours:
            agree += 1
        else:
            disagree += 1
            examples.append(str(f))
    return {"n": n, "agree": agree, "disagree": disagree, "z3_unknown": unknown, "disagreements": examples[:5]}


# ---------------------------------------------------------------- X2
def _nodes(p: K.Proof) -> List[K.Proof]:
    out, seen, stack = [], set(), [p]
    while stack:
        n = stack.pop()
        if id(n) in seen:
            continue
        seen.add(id(n))
        out.append(n)
        stack.extend(n.prems)
    return out


def _rebuild(p: K.Proof, target: K.Proof, replacement: K.Proof, memo=None) -> K.Proof:
    memo = {} if memo is None else memo
    if p is target:
        return replacement
    if id(p) in memo:
        return memo[id(p)]
    new_prems = tuple(_rebuild(q, target, replacement, memo) for q in p.prems)
    out = p if all(a is b for a, b in zip(new_prems, p.prems)) else K.Proof(p.rule, new_prems, p.args)
    memo[id(p)] = out
    return out


def mutate(p: K.Proof, rng: random.Random) -> Optional[K.Proof]:
    nodes = _nodes(p)
    n = rng.choice(nodes)
    kind = rng.randrange(5)
    if kind == 0 and n.rule in ("allE",):
        m = K.Proof(n.rule, n.prems, (S(n.args[0]),))
    elif kind == 1 and n.rule in ("andE1", "andE2"):
        m = K.Proof("andE2" if n.rule == "andE1" else "andE1", n.prems, n.args)
    elif kind == 2 and n.rule in ("impI", "botE", "raa", "orI1", "orI2", "hyp"):
        m = K.Proof(n.rule, n.prems, (Not(n.args[0]),) + n.args[1:])
    elif kind == 3 and len(n.prems) >= 2:
        prems = list(n.prems)
        prems[0], prems[1] = prems[1], prems[0]
        m = K.Proof(n.rule, tuple(prems), n.args)
    elif kind == 4 and n.rule == "ax" and n.args[1]:
        ts = list(n.args[1])
        ts[0] = S(ts[0])
        m = K.Proof("ax", (), (n.args[0], tuple(ts)))
    else:
        return None
    return _rebuild(p, n, m)


def kernels_agree(theory, library: K.Library, mutations: int = 300, seed: int = 3) -> Dict:
    k1 = K.Checker(theory, library)
    k2 = K2.Checker2(theory)
    both_ok = 0
    disagreements = []
    for name in library.order:
        p, f = library.proofs[name], library.thms[name]
        a = b = True
        try:
            k1.check_theorem(p, f)
        except K.ProofError:
            a = False
        try:
            k2.add_lemma(name, p, f)
        except K2.Reject:
            b = False
        both_ok += a and b
        if a != b:
            disagreements.append(name)
    rng = random.Random(seed)
    names = list(library.order)
    tried = rejected_both = accepted_both = mut_disagree = 0
    while tried < mutations and names:
        name = rng.choice(names)
        m = mutate(library.proofs[name], rng)
        if m is None:
            continue
        tried += 1
        f = library.thms[name]
        a = b = True
        try:
            k1.check_theorem(m, f)
        except (K.ProofError, RecursionError, ValueError):
            a = False
        try:
            k2.check_theorem(m, f)
        except (K2.Reject, RecursionError, ValueError, KeyError):
            b = False
        if a and b:
            accepted_both += 1
        elif not a and not b:
            rejected_both += 1
        else:
            mut_disagree += 1
    return {"library_proofs": len(names), "accepted_by_both": both_ok, "disagreements": disagreements,
            "mutants": tried, "mutants_rejected_by_both": rejected_both,
            "mutants_accepted_by_both (harmless mutations)": accepted_both, "mutant_disagreements": mut_disagree}


# ---------------------------------------------------------------- X3
def random_modal(rng: random.Random, size: int, vars_=("p", "q")):
    if size <= 1:
        return rng.choice([G.V(v) for v in vars_] + [G.BOT])
    r = rng.random()
    if r < 0.3:
        return G.Box(random_modal(rng, size - 1, vars_))
    if r < 0.45:
        return G.Not(random_modal(rng, size - 1, vars_))
    k = rng.randint(1, size - 2) if size > 2 else 1
    op = rng.choice([G.Imp, G.And, G.Or])
    return op(random_modal(rng, k, vars_), random_modal(rng, max(1, size - 1 - k), vars_))


def all_gl_frames(n: int):
    pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
    for bits in range(1 << len(pairs)):
        R = {i: set() for i in range(n)}
        for k, (i, j) in enumerate(pairs):
            if bits >> k & 1:
                R[i].add(j)
        ok = all(not (j in R[i] and i in R[j]) for i in range(n) for j in range(n) if i != j)
        ok = ok and all(R[j] <= R[i] for i in range(n) for j in R[i])
        if ok:
            yield {i: frozenset(s) for i, s in R.items()}


def brute_countermodel(f, max_worlds: int = 3):
    vs = sorted(G.variables(f))
    for n in range(1, max_worlds + 1):
        for R in all_gl_frames(n):
            for bits in range(1 << (n * len(vs))):
                val = {w: frozenset(v for k, v in enumerate(vs) if bits >> (w * len(vs) + k) & 1)
                       for w in range(n)}
                m = G.Model(list(range(n)), R, val, 0)
                for root in range(n):
                    m.root = root
                    if not G.holds(m, root, f):
                        return m
    return None


def gl_vs_bruteforce(n: int = 300, seed: int = 11) -> Dict:
    rng = random.Random(seed)
    stats = {"n": n, "provable": 0, "not_provable": 0, "certificates_ok": 0, "conflicts": 0,
             "countermodel_sizes": {}}
    known = {
        "K": (G.Imp(G.Box(G.Imp(G.V("p"), G.V("q"))), G.Imp(G.Box(G.V("p")), G.Box(G.V("q")))), True),
        "4": (G.Imp(G.Box(G.V("p")), G.Box(G.Box(G.V("p")))), True),
        "Löb": (G.Imp(G.Box(G.Imp(G.Box(G.V("p")), G.V("p"))), G.Box(G.V("p"))), True),
        "T": (G.Imp(G.Box(G.V("p")), G.V("p")), False),
        "5": (G.Imp(G.Dia(G.V("p")), G.Box(G.Dia(G.V("p")))), False),
        "Grz-ish": (G.Imp(G.Box(G.Imp(G.Box(G.Imp(G.V("p"), G.Box(G.V("p")))), G.V("p"))), G.V("p")), False),
    }
    stats["known"] = {k: G.prove(f).provable == exp for k, (f, exp) in known.items()}
    for _ in range(n):
        f = random_modal(rng, rng.randint(3, 9))
        r = G.prove(f)
        ok = r.verify()
        stats["certificates_ok"] += ok
        if r.provable:
            stats["provable"] += 1
            if brute_countermodel(f, 3) is not None:
                stats["conflicts"] += 1
        else:
            stats["not_provable"] += 1
            k = len(r.countermodel.worlds)
            stats["countermodel_sizes"][k] = stats["countermodel_sizes"].get(k, 0) + 1
    return stats
