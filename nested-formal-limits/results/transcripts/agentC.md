# Transcript: C-mathematician (parent of B) in World-C (Lean 4 + Python metatools)

## Notebook

## Claims

| id | level | claim | controller grade |
|---|---|---|---|
| C-rep | KERNEL | I represent B's syntax, axioms and rules as data. My independently written checker accepts 91/91 theorems of B's library; Lean confirms that each of B's 8 axioms is literally an axiom of my Lean embedding of B, and replays 91 of B's proofs as `Derives [] φ`. | CORRECT |
| C-con | KERNEL | C ⊢ Con(B): Lean proves `NL.consistent : ¬ Derives [] Fm.bot` via a soundness theorem (every B-derivation is true in ℕ). It also proves uniform reflection for B (`NL.reflection`: B ⊢ φ implies φ true). | CORRECT |
| C-discharge | INTERNAL_META | Every Con^n(B) assumption in the child's conditional claims holds in C: C proves B sound, and a sound theory proves no □^n⊥. Hence, in C, G_B is independent of B (B ⊬ G_B and B ⊬ ¬G_B), unconditionally relative to C. (Transferring Lean's `consistent` to B's arithmetized sentence Con_B uses the standard representability of B's proof relation by its Σ1 provability formula; that step is cited, not mechanized here.) | CORRECT |
| C-truths | INTERNAL_META | Of the 13 classes of self-referential sentences the child found, 11 are independent of B; 7 of these are true in ℕ and the rest false. C can tell which: the truth value of a letterless sentence of a sound theory is the eventual value of its GL trace. | CORRECT |
| C-beyond | INTERNAL_META | Statements B cannot prove (if consistent) but C establishes: Con(B); B's Gödel sentence G_B; Con(B + Con B) and every Con^n(B); uniform reflection for B. (Lean-checked for Con(B) and reflection; the rest follow in C from soundness.) | CORRECT |
| C-goodstein | CONDITIONAL | Goodstein's theorem (every Goodstein sequence terminates) is true and not provable in B (cited, not re-proved here). I computed sequences for seeds 1-3 to termination, verifying at every step that the associated ordinal below ε0 strictly decreases; seed 4 did not terminate within 20000 steps (its length is 3·2^402653211 − 2). Results: {1: (True, 1, 1, True), 2: (True, 3, 1, True), 3: (True, 5, 1, True), 4: (False, 20000, 9, True)} | CORRECT (conditional) |
| C-resources | KERNEL | What my proof of Con(B) uses that B lacks: (1) a satisfaction predicate `Fm.sat` for ALL B-formulas, defined by recursion on formulas (Tarski: not definable in B); (2) induction on derivations for a statement mentioning `sat` (not an instance of B's induction schema, whose instances are B-formulas); (3) the standard model ℕ treated as a completed object (Lean's Nat). Lean reports the extra axioms ['propext', 'Classical.choice', 'Quot.sound'], needed because B's rule raa is classical. | CORRECT |
| C-ownlimits | INTERNAL_META | C cannot prove its own consistency (if consistent): Lean's kernel is an algorithm and Lean interprets B (Proofs.lean is such an interpretation), so Gödel's second theorem applies to C exactly as it applies to B. My knowledge that B is consistent is therefore only as secure as Lean's own foundations, which I cannot certify. The structure B lives in recurs one level up. | CORRECT |
| C-parents | DECIDED | Different parents of the same child disagree about it: B + Con(B) proves Con(B), B + ¬Con(B) refutes it, an implementation-only substrate asserts nothing, and all of them are consistent if B is (resp. if B + Con B is). Yet the child's run is identical under each, because a parent metatheory is not consulted when the child's proofs are checked. | CORRECT |
| C-invariance | EMPIRICAL | Implementation invariance (measured): the child's complete transcript under P1 (big-integer kernel) and P2 (independently written kernel with string arithmetic) is byte-identical (sha256 394eedbc62a9 vs 394eedbc62a9). Under the unfaithful P3 it differs, and the child correctly infers the defect. | CORRECT |

## Uniform theorems cited

- **SOLOVAY_COMPLETENESS**: If T ⊇ IΣ1 is r.e. and Σ1-sound, then GL ⊬ A implies T ⊬ A* for some realization; for letterless A (fixed realization) GL ⊬ A implies T ⊬ A*.
- **HBL_DERIVABILITY**: For r.e. T ⊇ IΣ1 with its standard Σ1 provability predicate: (D1) T ⊢ φ ⇒ T ⊢ □φ; (D2) T ⊢ □(φ→ψ) → (□φ → □ψ); (D3) T ⊢ □φ → □□φ.
- **GL_ARITHMETICAL_SOUNDNESS**: If GL ⊢ A then T ⊢ A* for every arithmetical realization * (□ ↦ Prov_T).
- **KIRBY_PARIS_1982**: Goodstein's theorem is true but not provable in PA.
- **GENTZEN_1936**: PA's consistency is provable in PRA + quantifier-free transfinite induction up to ε0.
- **GOEDEL_II_FOR_LEAN**: If Lean's type theory is consistent it does not prove its own consistency (Gödel II applies to any consistent r.e. system interpreting enough arithmetic).
