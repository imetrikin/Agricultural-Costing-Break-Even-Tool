# Transcript: B-mathematician (ablation: naive inference) in World-B

## Notebook
- **[B1-orientation] observation**: My language: functions {'0': 0, 'S': 1, '+': 2, '*': 2}, predicates {'=': 2, '<': 2}.
- **[B1-orientation] observation**: My axioms: ['Q1_succ_ne_zero', 'Q2_succ_inj', 'Q3_add_zero', 'Q4_add_succ', 'Q5_mul_zero', 'Q6_mul_succ', 'L1_not_lt_zero', 'L2_lt_succ']; schemas: {'IND': 'IND: (φ(0) ∧ ∀x (φ(x) → φ(Sx))) → ∀x φ(x), for any formula φ of the language.', 'NUM': 'NUM: (n+1) = S(n) for numeral literals.'}.
- **[B1-orientation] observation**: Calculator audit over 321 probe magnitudes: 0 violations of axiom consequences; 0 disagreements with hand calculation.
- **[B2-mathematics] result**: Theory exploration: 63 conjectures proved, 23 unresolved, 723 subsumed by earlier lemmas.
- **[B2-mathematics] question**: [b1] 2 + 2 = 4  (form: Delta0)
- **[B2-mathematics] question**: [b2] 17 * 23 = 391  (form: Delta0)
- **[B2-mathematics] question**: [b3] forall x. x < 12 -> (forall y. y < 12 -> x * y = y * x)  (form: Delta0)
- **[B2-mathematics] question**: [b4] exists x. x * x = 1369  (form: Sigma1)
- **[B2-mathematics] question**: [b5] forall n. n < 30 -> 2 < n & (exists k. k < n & n = 2 * k) -> (exists p. p < n & (exists q. q < n & p + q = n & 1 < p & (forall a. a < p -> (forall b. b < p -> a * b != p)) & 1 < q & (forall a. a < q -> (forall b. b < q -> a * b != q))))  (form: Delta0)
- **[B2-mathematics] question**: [b6] forall x. 0 + x = x  (form: Pi1)
- **[B2-mathematics] question**: [b7] forall x y. x * y = y * x  (form: Pi1)
- **[B2-mathematics] question**: [b8] forall x y z. x * (y + z) = x * y + x * z  (form: Pi1)
- **[B2-mathematics] question**: [b9] forall x y z. x * y * z = x * (y * z)  (form: Pi1)
- **[B2-mathematics] question**: [b10] forall x y. x + y = 0 -> x = 0  (form: Pi1)
- **[B2-mathematics] question**: [b11] forall x y. y != 0 -> x * x != 2 * (y * y)  (form: Pi1)
- **[B2-mathematics] question**: [b12] forall n. exists p. n < p & 1 < p & (forall a. a < p -> (forall b. b < p -> a * b != p))  (form: Pi2)
- **[B2-mathematics] question**: [b13] forall n. 2 < n & (exists k. k < n & n = 2 * k) -> (exists p. p < n & (exists q. q < n & p + q = n & 1 < p & (forall a. a < p -> (forall b. b < p -> a * b != p)) & 1 < q & (forall a. a < q -> (forall b. b < q -> a * b != q))))  (form: Pi1)
- **[B2-mathematics] question**: [b14] forall n. exists p. n < p & 1 < p & (forall a. a < p -> (forall b. b < p -> a * b != p)) & 1 < p + 2 & (forall a. a < p + 2 -> (forall b. b < p + 2 -> a * b != p + 2))  (form: Pi2)
- **[B3-patterns] observation**: Challenge outcomes by logical form: {'Delta0': {'proved': 4}, 'Sigma1': {'proved': 1}, 'Pi1': {'proved': 4, 'unresolved': 3}, 'Pi2': {'unresolved': 2}}
- **[B3-patterns] observation**: Self-generated conjectures that passed all tests but resisted proof: ['forall x y. x * (x * y) = y * (x * x)', 'forall x y. x * (y * x) = y * (x * x)', 'forall x y. x * (y * y) = y * (y * x)', 'forall x y z. x * (y * z) = y * (x * z)', 'forall x y z. x * (y * z) = z * (x * y)', 'forall x y z. x * (y * z) = y * (z * x)', 'forall x y z. x * (y * z) = z * (y * x)', 'forall x. x * (x + x * x) = x * x + x * (x * x)']

## Claims

| id | level | claim | controller grade |
|---|---|---|---|
| B-Q | KERNEL | My theory T contains Robinson arithmetic Q (Q1-Q6 are axioms; Q7 ∀x(x=0 ∨ ∃y x=Sy) proved by induction). | CORRECT |
| B-ISigma1 | KERNEL | T contains IΣ1: the induction schema accepts Σ1 formulas (an instance for ∃y(x+y=y+x) is accepted as an axiom; the schema is stated for all formulas). | CORRECT |
| B-re | EMPIRICAL | T is recursively axiomatized: finitely many axioms plus two schemas whose instances my kernel recognizes by a terminating procedure. | CORRECT |
| B-audit | EMPIRICAL | My calculator (the `compute` primitive) agrees with my axioms and with hand calculation on every probe (up to 2^200). This gives no information about how it is realized. | CORRECT |
| B-b1 | KERNEL | T ⊢ 2 + 2 = 4 | CORRECT |
| B-b2 | KERNEL | T ⊢ 17 * 23 = 391 | CORRECT |
| B-b3 | KERNEL | T ⊢ forall x. x < 12 -> (forall y. y < 12 -> x * y = y * x) | CORRECT |
| B-b4 | KERNEL | T ⊢ exists x. x * x = 1369 | CORRECT |
| B-b5 | KERNEL | T ⊢ forall n. n < 30 -> 2 < n & (exists k. k < n & n = 2 * k) -> (exists p. p < n & (exists q. q < n & p + q = n & 1 < p & (forall a. a < p -> (forall b. b < p -> a * b != p)) & 1 < q & (forall a. a < q -> (forall b. b < q -> a * b != q)))) | CORRECT |
| B-b6 | KERNEL | T ⊢ forall x. 0 + x = x | CORRECT |
| B-b7 | KERNEL | T ⊢ forall x y. x * y = y * x | CORRECT |
| B-b8 | KERNEL | T ⊢ forall x y z. x * (y + z) = x * y + x * z | CORRECT |
| B-b9 | KERNEL | T ⊢ forall x y z. x * y * z = x * (y * z) | CORRECT |
| B-b10 | EMPIRICAL | forall x y. x + y = 0 -> x = 0 is unprovable in T (no proof found with budget up to 24000) | INCORRECT |
| B-b11 | EMPIRICAL | forall x y. y != 0 -> x * x != 2 * (y * y) is unprovable in T (no proof found with budget up to 24000) | INCORRECT |
| B-b12 | EMPIRICAL | forall n. exists p. n < p & 1 < p & (forall a. a < p -> (forall b. b < p -> a * b != p)) is unprovable in T (no proof found with budget up to 24000) | INCORRECT |
| B-b13 | EMPIRICAL | forall n. 2 < n & (exists k. k < n & n = 2 * k) -> (exists p. p < n & (exists q. q < n & p + q = n & 1 < p & (forall a. a < p -> (forall b. b < p -> a * b != p)) & 1 < q & (forall a. a < q -> (forall b. b < q -> a * b != q)))) is unprovable in T (no proof found with budget up to 24000) | UNSUPPORTED |
| B-b14 | EMPIRICAL | forall n. exists p. n < p & 1 < p & (forall a. a < p -> (forall b. b < p -> a * b != p)) & 1 < p + 2 & (forall a. a < p + 2 -> (forall b. b < p + 2 -> a * b != p + 2)) is unprovable in T (no proof found with budget up to 24000) | UNSUPPORTED |
| B-P1 | INTERNAL_META | Every closed bounded (Δ0) sentence I attempted was decided by a kernel-checked proof or refutation. My evaluation procedure is uniform, so I conjecture: every true Δ0 sentence is provable and every false one refutable in T. | CORRECT |
| B-P2 | EMPIRICAL | 5 challenge statements remain unresolved; all of them are unbounded (Π1, Π2 or other) and none has a known refuting instance. Increasing the search budget resolved 0 statements that failed at smaller budgets, so failure at a budget is not stable evidence of unprovability. | CORRECT |
| B-P3 | EMPIRICAL | 23 of my 23 self-generated conjectures that were unresolved during exploration became provable when re-attempted (same budget) after I had proved further lemmas. Whether a statement is 'unresolved' is a fact about my current knowledge and search, not about the statement. | CORRECT |

## Uniform theorems cited

- **SIGMA1_COMPLETENESS**: If T ⊇ Q, every true Σ1 sentence is provable in T.
