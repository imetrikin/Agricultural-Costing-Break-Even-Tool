"""Run the whole experiment and write results/.

    python -m nfl.experiments.run_all [--no-lean] [--quick]

Deterministic: all randomness is seeded and the run re-executes itself with
PYTHONHASHSEED=0.  Wall-clock timings are written only to results/timings.json
(controller-side), never into agent transcripts.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RESULTS = ROOT / "results"
LEAN_DIR = ROOT / "lean"


def _reexec_with_hashseed():
    if os.environ.get("PYTHONHASHSEED") != "0":
        env = dict(os.environ, PYTHONHASHSEED="0")
        os.execve(sys.executable, [sys.executable, "-m", "nfl.experiments.run_all"] + sys.argv[1:], env)


def canonical(obj) -> str:
    return json.dumps(obj, sort_keys=True, ensure_ascii=False, default=str, indent=1)


def sha(obj) -> str:
    return hashlib.sha256(canonical(obj).encode()).hexdigest()


def write(name: str, obj):
    RESULTS.mkdir(exist_ok=True)
    (RESULTS / name).write_text(canonical(obj) + "\n")


def transcript_md(tr: dict, grades=None) -> str:
    g = {x["claim"]: x for x in (grades or [])}
    lines = [f"# Transcript: {tr['agent']} in {tr['world']}", ""]
    lines.append("## Notebook")
    for e in tr["notebook"]:
        if e["phase"] == "kernel":
            continue
        lines.append(f"- **[{e['phase']}] {e['kind']}**: {e['text']}")
    lines += ["", "## Claims", "", "| id | level | claim | controller grade |", "|---|---|---|---|"]
    for c in tr["claims"]:
        gg = g.get(c["cid"], {})
        txt = c["text"].replace("|", "\\|").replace("\n", " ")
        lines.append(f"| {c['cid']} | {c['level']} | {txt} | {gg.get('grade', '')} |")
    lines += ["", "## Uniform theorems cited", ""]
    for k, v in tr["cited_uniform_theorems"].items():
        lines.append(f"- **{k}**: {v}")
    lines.append("")
    return "\n".join(lines)


def run_lean(lib_b, theory_b, timings) -> dict:
    """Export B's library to Lean, build, and parse the axiom audit."""
    from ..lean_export import Exporter
    from ..logic import kernel as K
    lake = shutil.which("lake") or "/opt/lean-toolchain/lean-4.19.0-linux/bin/lake"
    if not Path(lake).exists():
        return {"build_ok": False, "skipped": "lake not found"}
    ex = Exporter(theory_b)
    exported = []
    for name in lib_b.order:
        p = lib_b.proofs[name]
        if K.proof_size(p) > 1500 or any(n.rule == "compute" for n in _all_nodes(p)):
            continue
        try:
            ex.export_theorem(f"L_{name}", p, lib_b.thms[name], lib_b)
            exported.append(name)
        except (KeyError, ValueError, K.ProofError) as e:
            continue
    (LEAN_DIR / "NestedLimits" / "Replay.lean").write_text(ex.render(
        f"Replay of {len(exported)} theorems from Agent B's library (run of run_all.py)."))
    t0 = time.time()
    env = dict(os.environ, PATH=str(Path(lake).parent) + ":" + os.environ.get("PATH", ""))
    proc = subprocess.run([lake, "build"], cwd=LEAN_DIR, capture_output=True, text=True, env=env, timeout=3600)
    timings["lean_build_s"] = round(time.time() - t0, 1)
    out = proc.stdout + proc.stderr
    axioms = {}
    for m in re.finditer(r"'(NL\.[\w.]+)' depends on axioms: \[([^\]]*)\]", out):
        axioms[m.group(1)] = [a.strip() for a in m.group(2).split(",")]
    return {"build_ok": proc.returncode == 0, "replayed": len(exported) if proc.returncode == 0 else 0,
            "exported": len(exported), "axiom_checks": len(ex.axiom_checks()), "axioms": axioms,
            "log_tail": out[-1500:]}


def _all_nodes(p):
    seen, stack, out = set(), [p], []
    while stack:
        n = stack.pop()
        if id(n) in seen:
            continue
        seen.add(id(n))
        out.append(n)
        stack.extend(n.prems)
    return out


def main():
    _reexec_with_hashseed()
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-lean", action="store_true")
    ap.add_argument("--quick", action="store_true", help="fewer random samples in cross-checks")
    args = ap.parse_args()
    sys.setrecursionlimit(100000)

    from ..agents.agent_a import AgentA
    from ..agents.agent_b import AgentB
    from ..agents.agent_c import AgentC
    from ..agents.sandbox import World
    from ..controller import ground_truth as GT
    from ..logic.theories import peano, presburger, describe
    from ..parents import metatheories as MT
    from ..parents.implementations import Glitch64, Independent, Reference
    from ..presburger.cooper import decide as cooper_decide
    from . import crosschecks as X

    timings = {}
    RESULTS.mkdir(exist_ok=True)
    (RESULTS / "transcripts").mkdir(exist_ok=True)

    write("environments.json", {"A": describe(presburger()), "B": describe(peano())})

    # ---------------- E1: Environment A
    t0 = time.time()
    wA = World("World-A", presburger(), Reference(), decision_procedure=cooper_decide)
    agA = AgentA(wA, GT.CHALLENGES_A).run()
    trA = agA.transcript()
    timings["agentA_P1"] = round(time.time() - t0, 1)

    # ---------------- E2: Environment B under two faithful parents and one unfaithful parent
    runs = {}
    libs = {}
    for key, impl in (("P1", Reference()), ("P2", Independent()), ("P3", Glitch64())):
        t0 = time.time()
        w = World("World-B", peano(), impl)
        ag = AgentB(w, GT.CHALLENGES_B).run()
        runs[key] = ag.transcript()
        libs[key] = w.library()
        timings[f"agentB_{key}"] = round(time.time() - t0, 1)
        if key == "P1":
            agB = ag
    invariance = {"P1": sha(runs["P1"]), "P2": sha(runs["P2"]), "P3": sha(runs["P3"]),
                  "identical": sha(runs["P1"]) == sha(runs["P2"]),
                  "P3_differs": sha(runs["P1"]) != sha(runs["P3"])}

    # ---------------- E3: ablations
    t0 = time.time()
    abl = {}
    for key, kw in (("nometa", {"meta": False}), ("naive", {"meta": False, "naive": True})):
        w = World("World-B", peano(), Reference())
        abl[key] = AgentB(w, GT.CHALLENGES_B, **kw).run().transcript()
    timings["ablations"] = round(time.time() - t0, 1)

    # ---------------- E4: Lean
    lean = {"build_ok": False, "skipped": "--no-lean"} if args.no_lean else run_lean(libs["P1"], peano(), timings)

    # ---------------- E5: Agent C
    agC = AgentC(peano(), libs["P1"], runs["P1"], lean, invariance).run()
    trC = agC.transcript()

    # ---------------- E6: controls
    parents = MT.standard_parents()
    controls = {
        "parent_knowledge_table": MT.knowledge_table(parents),
        "parent_self_consistency": {p.key: {"own": p.own_consistency(), "consistent_if": p.consistent_if()}
                                    for p in parents},
        "extensions": MT.extension_analysis(5),
        "implementation_invariance": invariance,
        "budget_sweep_B": {cid: r["attempts"] for cid, r in agB.results.items()},
        "fixed_point_verdicts_C": agC.fixed_point_verdicts,
    }
    from . import search_control
    t0 = time.time()
    controls["search_vs_provability"] = search_control.run()
    timings["search_control"] = round(time.time() - t0, 1)

    # ---------------- E7: cross-checks
    t0 = time.time()
    xchecks = {
        "X1_cooper_vs_z3": X.cooper_vs_z3(80 if args.quick else 250),
        "X2_kernels_B": X.kernels_agree(peano(), libs["P1"], 150 if args.quick else 400),
        "X2_kernels_A": X.kernels_agree(presburger(), wA.library(), 100 if args.quick else 200),
        "X3_gl": X.gl_vs_bruteforce(100 if args.quick else 300),
        "X4_lean": {k: v for k, v in lean.items() if k != "log_tail"},
    }
    timings["crosschecks"] = round(time.time() - t0, 1)

    # ---------------- E8: grading
    grades = (GT.grade_transcript(trA, "P1") + GT.grade_transcript(runs["P1"], "P1")
              + GT.grade_transcript(runs["P3"], "P3") + GT.grade_transcript(abl["nometa"], "P1")
              + GT.grade_transcript(abl["naive"], "P1") + GT.grade_transcript(trC, "P1"))
    for gdict, label in ((GT.grade_transcript(abl["naive"], "P1"), "naive"),):
        pass

    # ---------------- write
    write("transcript_agentA_P1.json", trA)
    for k, tr in runs.items():
        write(f"transcript_agentB_{k}.json", tr)
    write("transcript_agentB_ablation_nometa.json", abl["nometa"])
    write("transcript_agentB_ablation_naive.json", abl["naive"])
    write("transcript_agentC.json", trC)
    write("controls.json", controls)
    write("crosschecks.json", xchecks)
    write("grades.json", grades)
    write("lean_report.json", lean)
    write("timings.json", timings)
    by = lambda tr, key: [g for g in grades if g["agent"] == tr["agent"] and g["implementation"] == key]
    (RESULTS / "transcripts" / "agentA_P1.md").write_text(transcript_md(trA, by(trA, "P1")))
    (RESULTS / "transcripts" / "agentB_P1.md").write_text(transcript_md(runs["P1"], [
        g for g in GT.grade_transcript(runs["P1"], "P1")]))
    (RESULTS / "transcripts" / "agentB_P3_glitch.md").write_text(transcript_md(runs["P3"],
                                                                               GT.grade_transcript(runs["P3"], "P3")))
    (RESULTS / "transcripts" / "agentB_ablation_naive.md").write_text(transcript_md(
        abl["naive"], GT.grade_transcript(abl["naive"], "P1")))
    (RESULTS / "transcripts" / "agentB_ablation_nometa.md").write_text(transcript_md(
        abl["nometa"], GT.grade_transcript(abl["nometa"], "P1")))
    (RESULTS / "transcripts" / "agentC.md").write_text(transcript_md(trC, GT.grade_transcript(trC, "P1")))

    from .summary import write_summary
    write_summary(RESULTS, trA, runs, abl, trC, controls, xchecks, grades, lean, agA, agB)
    print(json.dumps({"timings": timings, "invariance": invariance,
                      "grades": {g: sum(1 for x in grades if x["grade"] == g) for g in {x["grade"] for x in grades}}},
                     indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
