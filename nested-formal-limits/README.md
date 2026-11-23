# Nested formal environments: can a mathematician inside a formal system detect a stronger "parent"?

A computational experiment with three formal environments, artificial mathematicians that see only their own
environment, deterministic proof checkers, and machine-checked parent-level results in Lean 4.

**Read the [REPORT](REPORT.md)** for the design, results, answers to the research questions,
literature review, and the novelty assessment. Generated results live in [`results/`](results/)
(start with [`results/SUMMARY.md`](results/SUMMARY.md)); agent transcripts are in
[`results/transcripts/`](results/transcripts/).

## Layout

| path | what it is |
|---|---|
| `nfl/logic/syntax.py` | first-order terms/formulas, capture-avoiding substitution, α-equivalence, parser |
| `nfl/logic/kernel.py` | **trusted proof checker** (classical natural deduction with equality, ~300 lines) |
| `nfl/logic/kernel2.py` | an independently written second checker (locally nameless, string arithmetic) |
| `nfl/logic/theories.py` | explicit axioms: Environment A = Presburger arithmetic, Environment B = Peano arithmetic |
| `nfl/prover/` | proof-producing tactics: Σ1-completeness (Δ0 decision with proofs), rewriting + induction, theory exploration |
| `nfl/presburger/` | Cooper's quantifier elimination; definability analysis (ultimately periodic sets) |
| `nfl/modal/gl.py` | provability logic GL: decision procedure with checkable certificates, fixed points |
| `nfl/agents/` | the sandbox (`World`), Agent A, Agent B, Agent C, evidence levels, citable theorems |
| `nfl/parents/` | parent implementations (P1 faithful, P2 faithful + independent, P3 unfaithful) and parent metatheories |
| `nfl/controller/ground_truth.py` | the controller's ground truth and claim grading (agents never import it) |
| `nfl/experiments/` | `run_all.py` (everything), cross-checks, summary rendering |
| `nfl/lean_export.py` | exports B's axioms and agent proofs to Lean for independent re-checking |
| `lean/NestedLimits/` | Lean 4: deep embedding of B, soundness w.r.t. ℕ, `consistent : ¬ Derives [] ⊥`, reflection, replay |
| `tests/` | pytest suite (kernel rejection tests, kernel agreement, Cooper vs brute force/Z3, GL, isolation audit, invariance) |

## Reproducing

Requirements: Python ≥ 3.10 (tested on 3.13). Optional: `z3-solver` (cross-check X1), `pytest`, and a Lean 4
toolchain (tested with v4.19.0, Lean core only, no Mathlib).

```bash
cd nested-formal-limits
pip install z3-solver pytest          # optional
PYTHONHASHSEED=0 python -m pytest -q tests

# full experiment (≈ 3 min of Python + the Lean build; the runner re-execs itself with PYTHONHASHSEED=0)
python -m nfl.experiments.run_all            # add --no-lean to skip Lean, --quick for fewer samples

# the Lean development on its own
cd lean && lake build                        # prints `#print axioms` for NL.soundness / consistent / reflection
```

Everything is deterministic (seeded); the child's transcripts under the two faithful parents are compared
byte-for-byte by SHA-256.

## What the agents are (and are not)

The "artificial mathematicians" are deterministic symbolic programs, not language models. They generate their
own conjectures (theory exploration), attempt proofs with budgets, record failures, classify statements by
logical form, and form hypotheses with explicit evidence levels
(`KERNEL`, `DECIDED`, `INTERNAL_META`, `CONDITIONAL`, `EMPIRICAL`, `SPECULATIVE`). No claim is accepted on an
agent's say-so: kernel claims are re-checked by a second independent checker and (for a sample) by Lean; GL
claims carry certificates checked by a separate checker. See REPORT §8 for what this design can and cannot show.
