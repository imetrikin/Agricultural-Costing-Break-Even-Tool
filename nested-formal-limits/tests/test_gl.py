"""GL decision procedure: known theorems, certificates, brute-force agreement, fixed points."""
import random

from nfl.modal import gl as G
from nfl.experiments.crosschecks import brute_countermodel, random_modal

p, q = G.V("p"), G.V("q")


def test_known():
    assert G.prove(G.Imp(G.Box(G.Imp(G.Box(p), p)), G.Box(p))).provable          # Löb
    assert not G.prove(G.Imp(G.Box(p), p)).provable                                 # T
    assert G.prove(G.Imp(G.con(1), G.Not(G.Box(G.con(1))))).provable               # Gödel II
    assert not G.prove(G.Imp(G.con(1), G.con(2))).provable


def test_certificates_and_bruteforce():
    rng = random.Random(5)
    for _ in range(120):
        f = random_modal(rng, rng.randint(3, 8))
        r = G.prove(f)
        assert r.verify()
        if r.provable:
            assert brute_countermodel(f, 3) is None


def test_tampered_certificate_rejected():
    r = G.prove(G.Imp(G.Box(p), G.Box(G.Box(p))))
    assert r.provable and r.verify()
    bad = G.GLResult(G.Imp(G.Box(p), p), True, tableau=r.tableau)
    assert not bad.verify()


def test_goedel_fixed_point_is_consistency():
    A = G.Not(G.Box(p))
    H, tr = G.letterless_fixed_point(A)
    c = G.fixed_point_certificates(A, H)
    assert all(v.provable and v.verify() for v in c.values())
    assert G.provable(G.Iff(H, G.con(1)))
