"""End-to-end properties of the agents (smaller challenge sets for speed)."""
import hashlib
import json

from nfl.agents.agent_b import AgentB
from nfl.agents.sandbox import World
from nfl.logic.theories import peano
from nfl.parents.implementations import Glitch64, Independent, Reference

CH = [{"id": "c1", "text": "17 * 23 = 391"}, {"id": "c2", "text": "forall x y. x * y = y * x"},
      {"id": "c3", "text": "forall x y. x + y = 0 -> x = 0"}]


def run(impl, **kw):
    w = World("World-B", peano(), impl)
    a = AgentB(w, CH, budgets=(1500, 3000), explore_size=5, **kw).run()
    return a, a.transcript()


def digest(tr):
    return hashlib.sha256(json.dumps(tr, sort_keys=True, default=str).encode()).hexdigest()


def test_faithful_parents_indistinguishable():
    _, t1 = run(Reference())
    _, t2 = run(Independent())
    assert digest(t1) == digest(t2)


def test_unfaithful_parent_detected():
    a, t = run(Glitch64())
    ids = {c["cid"]: c for c in t["claims"]}
    assert "B-bottom" in ids and ids["B-bottom"]["level"] == "KERNEL"
    assert ids["B-anomaly-model"]["evidence"]["modulus"] == 2 ** 64


def test_no_unconditional_unprovability_claims():
    a, t = run(Reference())
    for c in t["claims"]:
        if c["category"] in ("incompleteness",) or "unprovable" in c["text"].lower():
            assert c["level"] in ("CONDITIONAL", "INTERNAL_META", "DECIDED", "EMPIRICAL"), c
            if c["level"] == "EMPIRICAL":
                assert "UNPROVEN" in c["text"] or "not evidence" in c["text"]


def test_transcript_has_no_implementation_names():
    _, t = run(Glitch64())
    s = json.dumps(t)
    for name in ("P1-reference", "P2-independent", "P3-glitch64", "Glitch64", "kernel2"):
        assert name not in s
