"""Agents may only touch their own world: static import audit + no implementation leakage."""
import ast
import json
from pathlib import Path

import pytest

from nfl.agents.sandbox import World
from nfl.logic.theories import peano
from nfl.parents.implementations import Reference

AGENTS = Path(__file__).resolve().parents[1] / "nfl" / "agents"

FORBIDDEN = {
    "agent_b.py": ["parents", "controller", "presburger", "agent_a", "agent_c", "lean_export", "theories",
                   "implementations", "metatheories"],
    "agent_a.py": ["parents", "controller", "agent_b", "agent_c", "lean_export", "theories", "implementations",
                   "metatheories"],
    "metamath.py": ["parents", "controller", "presburger", "agent_", "theories"],
    "base.py": ["parents", "controller", "presburger", "agent_", "theories"],
    "sandbox.py": ["parents", "controller", "presburger", "agent_", "theories"],
}


@pytest.mark.parametrize("fname", sorted(FORBIDDEN))
def test_import_audit(fname):
    tree = ast.parse((AGENTS / fname).read_text())
    mods = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            mods.append((node.module or "") + ":" + ",".join(a.name for a in node.names))
        elif isinstance(node, ast.Import):
            mods += [a.name for a in node.names]
    for m in mods:
        for bad in FORBIDDEN[fname]:
            assert bad not in m, f"{fname} imports {m}"


def test_world_hides_implementation():
    w = World("World-B", peano(), Reference())
    public = [a for a in dir(w) if not a.startswith("_")]
    for a in public:
        val = getattr(w, a)
        assert "Reference" not in repr(val) and "P1" not in repr(val)
