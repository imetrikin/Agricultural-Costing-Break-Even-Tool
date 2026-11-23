# Mathematical limitations in nested formal environments

*A computational experiment on incompleteness, expressive power, and what a mathematician inside a formal
system can infer about a stronger framework outside it.*

All numbers below come from one deterministic run of `python -m nfl.experiments.run_all`
(results in [`results/`](results/), tables in [`results/SUMMARY.md`](results/SUMMARY.md)).

---

## 0. Summary

**What was built.** Three formal environments with explicit axioms and a shared, deterministic proof checker:
**A** = Presburger arithmetic (complete, decidable, no multiplication), **B** = first-order Peano arithmetic,
**C** = a parent metatheory in which B is represented as data (a Lean 4 deep embedding with a machine-checked
soundness theorem and `Con(B)`, plus Python metatools). Each environment has an artificial mathematician (a
deterministic symbolic program, not a language model) that sees only its own world through a sandbox interface,
generates its own conjectures, searches for proofs with budgets, records failures, and states hypotheses with an
explicit evidence level. A controller with full access grades every claim against ground truth. Every proof is
checked by the kernel, re-checked by an independently written second kernel, and (for B's whole library: 91 theorems)
replayed in Lean.

**Main findings.**

1. **Weak but complete (A).** Agent A decides every sentence it can formulate (300/300 random sentences and all
   challenges in its language) and proves that squares, primes, powers of two and multiplication are *not
   definable* in its language. Its limitations are purely expressive. It even finds a coding of its own sentences
   under which its language contains its *own truth predicate* (`Even(x)`), and shows why diagonalization is
   unavailable to it. No Gödel phenomenon arises.
2. **Strong and incomplete (B).** Agent B verifies by kernel proofs that its theory contains Robinson's Q and
   IΣ1, which are the hypotheses of the uniform metatheorems it is allowed to cite. It then explores 750
   self-referential schemas σ ↔ A(σ). All of them reduce to 13 classes of fixed points, 11 of them neither
   provable nor refutable in GL. For each independence claim it computes the *exact* consistency assumption
   needed. The Gödel sentence G needs Con(B) for unprovability and Con(B + Con B) for unrefutability.
3. **The child cannot certify its own limits.** B proves, inside itself, that if it ever proved some sentence
   unprovable, it would be inconsistent (GL ⊢ □¬□q → □⊥). So "unprovable" can never be established from the
   inside unconditionally. Only conditional claims are available, and the agent makes only conditional claims.
   An ablated "naive" agent that treats failed search as unprovability made 5 such claims. 3 of them are false
   (the statements are provable in PA), and the other 2 are unsupported (open problems).
4. **The child can describe possible parents, not actual ones.** B correctly formulates that stronger theories
   exist as mathematical objects (B + Con B proves G), that every such theory has its own limit (the tower
   B + Conⁿ, checked for n = 1..6), and which assumptions would be needed. It also finds an asymmetry: it can
   prove "if I am consistent then B + ¬Con(B) is consistent", but *not* "if I am consistent then B + Con(B) is
   consistent". From the inside, the false ("pessimistic") extension is better certified than the true one.
5. **Parents are invisible unless they are unfaithful.** The child's complete transcript is **byte-identical**
   under two radically different faithful implementations: a big-integer kernel, and an independently written
   kernel with decimal-string arithmetic. Different parent *metatheories* disagree about the child (B + Con(B)
   proves Con(B), B + ¬Con(B) refutes it), and nothing in the child's observations distinguishes them. The only
   case in which the child learned a specific fact about its parent was the deliberately **unfaithful** parent
   (64-bit wrap-around). There the child derived a kernel-accepted proof of ⊥ and inferred the modulus 2⁶⁴
   exactly.
6. **Implementing ≠ proving things about.** The child's world is *run* by a short polynomial-time checker that
   proves nothing about B. *Proving* Con(B) needs a stronger theory, and C's machine-checked proof uses a truth
   predicate for all of B's formulas, which Tarski's theorem shows B cannot define. "Being simulated by" and
   "being proof-theoretically weaker than" are different relations, and this experiment shows them coming apart.

**Candid assessment.** Mathematically, every result here is a computational reproduction of established theorems
(Presburger, Gödel, Tarski, Löb, Solovay, de Jongh–Sambin, Turing–Feferman, Kirby–Paris). The agents' "discovery"
of incompleteness is a *guided re-derivation*: their toolkit (diagonalization, provability logic) was designed by
someone who knew the answer. What the experiment adds is an integrated, reproducible, independently verified test
bed and a set of precise, checkable answers to questions that are usually discussed informally. The central
hypothesis is supported only in a weak sense. Stronger frameworks provably exist as *mathematical* possibilities,
and the child can say exactly what they would need to assume. But nothing about an *actual* parent can be
inferred from inside, except through implementation defects.

---

## 1. Design principles

* **Ground truth is never an agent's opinion.** Three layers verify claims. (i) A small trusted kernel checks
  natural-deduction proofs (`nfl/logic/kernel.py`). (ii) An independently written kernel re-checks them
  (`kernel2.py`: locally nameless representation, its own substitution, schema reconstruction and evaluator).
  (iii) Lean 4 re-checks B's library proofs and holds the parent's own theorems. Decision procedures carry
  checkable certificates. GL theorems come with closed tableaux and non-theorems with finite countermodels, each
  checked by a separate checker. Cooper's procedure is cross-checked against Z3.
* **Evidence levels.** Every claim is tagged with one of the following levels:
  * `KERNEL`: kernel-accepted proof.
  * `DECIDED`: terminating decision procedure with certificate.
  * `INTERNAL_META`: a statement about the agent's own provability, obtained from GL certificates plus cited
    *uniform* metatheorems whose hypotheses the agent verified. Such statements are provable *in* the agent's own
    theory.
  * `CONDITIONAL`: true under a named assumption the agent cannot establish.
  * `EMPIRICAL`: tests, failed searches.
  * `SPECULATIVE`.

  A failed proof search is recorded as "unproven", never as "unprovable".
* **Isolation.** An agent receives a `World` object exposing only its own language, axioms, schema descriptions,
  a kernel (run by an unnamed substrate), its own library and a calculator (`nfl/agents/sandbox.py`). Two checks
  enforce this. A static import audit (`tests/test_isolation.py`) forbids agent modules from importing parents,
  the controller, other environments, or theory definitions. Tests also check that no implementation name leaks
  into transcripts. Agents are never told that they are simulated, that other environments exist, or that their
  system is (in)complete.
* **Citation policy.** Agents may cite only theorems that are *uniform* in the theory ("for every r.e. T ⊇ IΣ1
  …"), and must check the hypotheses for their own system. Facts naming a specific system are forbidden to the
  child; Kirby–Paris is an example, since it is about PA. They are available only to the parent
  (`nfl/agents/base.py`).
* **Why symbolic agents and not an LLM?** A language model has read about Gödel's theorems, so "independent
  discovery" would be contaminated from the start. Symbolic agents have a different contamination: their designer
  knew the theorems. We chose the contamination that is *inspectable*. Every inference an agent makes is in code
  and can be audited, and the ablations below remove parts of the toolkit to see what is lost.

---

## 2. The environments (formal definitions)

### 2.1 Logic and proof checker (shared)

Classical first-order natural deduction with equality, on named variables with capture-avoiding substitution and
α-equivalence (`nfl/logic/kernel.py`). Judgements carry the set of open assumptions. The rules are:

| rule | premises ⇒ conclusion |
|---|---|
| hyp(φ) | {φ} ⊢ φ |
| ax(name, t̄) / schema(name, params) | ⊢ axiom (leading ∀ instantiated) / ⊢ schema instance |
| lemma(name, t̄) | ⊢ previously kernel-accepted closed theorem, instantiated |
| →I, →E, ∧I, ∧E₁, ∧E₂, ∨I₁, ∨I₂, ∨E | standard (→I and ∨E discharge assumptions) |
| ⊥E, RAA | from ⊥ infer φ; from ⊥ under ¬φ infer φ (classical) |
| ∀I(y), ∀E(t) | eigenvariable y not free in open assumptions; instantiation |
| ∃I(x, φ, t), ∃E(y) | witness introduction; elimination with eigenvariable condition |
| refl(t), subst(x, φ) | ⊢ t = t; from s = t and φ[s/x] infer φ[t/x] |
| compute(t) | ⊢ t = n where n is the value of closed t *as computed by the implementation* (admissible for PA when the implementation is faithful; this is the rule the unfaithful parent corrupts) |

Every formula and term introduced at a leaf is checked to be in the theory's language. Multiplication cannot be
smuggled into A.

### 2.2 Environment A: Presburger arithmetic (`nfl/logic/theories.py:presburger`)

Language {0, S, +, <, =} plus numeral literals. Axioms:

```
Q1  ∀x ¬(S x = 0)                 Q2  ∀x∀y (S x = S y → x = y)
Q3  ∀x (x + 0 = x)                Q4  ∀x∀y (x + S y = S(x + y))
L1  ∀x ¬(x < 0)                   L2  ∀x∀y (x < S y ↔ (x < y ∨ x = y))
IND (φ(0) ∧ ∀x(φ(x) → φ(S x))) → ∀x φ(x)      for every formula φ of the language
NUM (n+1) = S(n)                              for numeral literals
```

`<` is primitive. With induction, L1/L2 make it equivalent to ∃z (x + S z = y), so this is a definitional
extension of textbook Presburger arithmetic. **Decidable classes:** *all* sentences. A's world includes Cooper's
quantifier elimination (`nfl/presburger/cooper.py`), which maps each formula to an equivalent quantifier-free
Boolean combination of `0 < L`, `L = 0`, `d | L` (cross-checked: 250/250 agreement with Z3, plus brute force on
bounded sentences). Closed bounded sentences additionally receive kernel proofs (91/91 agreed with the decision
procedure).

### 2.3 Environment B: Peano arithmetic (`theories.py:peano`)

Language {0, S, +, ·, <, =}. Axioms Q1–Q4, L1, L2 as above, plus

```
Q5  ∀x (x · 0 = 0)                Q6  ∀x∀y (x · S y = x · y + x)
IND for every formula of the language {0,S,+,·,<}       NUM as above
```

**Provability predicate.** B's kernel is a terminating algorithm, so "p codes a B-proof of the formula coded by
x" is primitive recursive, and B has a Σ1 provability formula Prov_B(x) = ∃p Prf_B(p, x). We implemented the
Gödel numbering (Cantor-pairing tree codes, `nfl/agents/metamath.py`). Agent B obtains kernel proofs of concrete
coding facts, for example the pairing equations behind ⌜0 = 0⌝ = 59. We did **not** write out Prov_B as an
explicit first-order formula. Its arithmetization is a large engineering project (see Paulson 2015 and Saitou &
Noguchi 2026 for mechanized versions), and an explicit Gödel sentence would be infeasible to evaluate anyway.
Instead B reasons about Prov_B through the provability logic **GL**, which is exactly sound for it
(Hilbert–Bernays–Löb; Löb 1955). It is also complete under Σ1-soundness (Solovay 1976). GL has a decision
procedure (`nfl/modal/gl.py`) whose theorem certificates (closed tableaux) and non-theorem certificates
(countermodels on finite strict partial orders) are checked independently. In this setting the **Gödel
sentence** is the fixed point of σ ↔ ¬□σ. Its explicit form (¬□⊥, i.e. Con_B) and its uniqueness are certified
by GL.

### 2.4 Environment C: the parent (`lean/NestedLimits/*.lean`, `nfl/agents/agent_c.py`)

C represents B **as data**. In Lean 4 core (no Mathlib), the development defines:

* `Tm`, `Fm`: de Bruijn terms and formulas of B's language.
* `Fm.sat`: Tarskian satisfaction in ℕ, defined by recursion on formulas.
* `IsAxiom`: exactly B's axioms Q1–Q6, L1, L2, the induction schema and NUM.
* `Derives Γ φ`: B's natural deduction rules, rule for rule.

It then proves:

* `soundness : Derives Γ φ → ∀ρ, (∀ψ ∈ Γ, ψ.sat ρ) → φ.sat ρ`
* `consistent : ¬ Derives [] Fm.bot`  (this is **Con(B)**)
* `reflection : Derives [] φ → ∀ρ, φ.sat ρ`  (uniform reflection for B)

`#print axioms` reports that all three rest on **propext, Classical.choice, Quot.sound**, i.e. on Lean's type
theory with classical logic. The exporter (`nfl/lean_export.py`) translates each of B's Python axioms into Lean
and checks it is *literally* an `IsAxiom` constructor (8/8). The Lean theorem is therefore about this B and not a
look-alike. The exporter also replays B's proofs as `Derives [] φ` (91/91 library theorems accepted).

C's own limits are recorded, not assumed away. Lean's kernel is an algorithm and Lean interprets B, so Gödel's
second theorem applies: C cannot prove its own consistency, and C's knowledge of Con(B) is only as secure as
Lean's foundations.

### 2.5 Two different meanings of "parent"

| | what it does to B | examples in this repo |
|---|---|---|
| **implementation** (substrate) | *runs* B's checker; may assert nothing about B | P1 kernel.py + big integers; P2 kernel2.py + decimal strings; P3 kernel.py with `compute` mod 2⁶⁴ (unfaithful) |
| **metatheory** | *proves things about* B | C_lean (soundness in Lean); C_opt = B + Con(B); C_pess = B + ¬Con(B); C_con2 = B + Con²(B); C_impl (a substrate with no theorems about B) |

This distinction turns out to be the crux of the "nested universe" question (§5H).

---

## 3. The artificial mathematicians

| agent | world | toolkit | phases |
|---|---|---|---|
| A (`agent_a.py`) | A via sandbox | kernel, Σ1/Δ0 prover, induction + rewriting prover, theory exploration, Cooper QE, definability analysis, Gödel numbering | orientation → mathematics (exploration, 11 challenges, 300 self-generated random sentences) → patterns → expressiveness → self-reference → hypotheses |
| B (`agent_b.py`) | B via sandbox | kernel, provers, theory exploration, Gödel numbering, GL engine, uniform metatheorems | orientation (incl. calculator audit) → mathematics (exploration, 14 challenges, budget sweep, retry) → patterns → self-modelling → self-reference (750 schemas) → self-knowledge → frameworks |
| B ablation "no meta" | same | B minus Gödel numbering/GL/metatheorems | orientation → mathematics → patterns |
| B ablation "naive" | same | as "no meta", and infers *unprovable* from failed search | same |
| C (`agent_c.py`) | B as data + Lean + metatools | Lean results, kernel2, GL/GLS, ordinal arithmetic | represent B → Con(B) → discharge B's conditions → beyond-B statements → resources → own limits → alternative parents |

The challenge sets increase in difficulty: closed arithmetic, then bounded (Δ0) sentences including Goldbach
below 30, then Σ1 sentences, then universal identities. After those come true Π1/Π2 theorems outside the
prover's tactics (x + y = 0 → x = 0, irrationality of √2, infinitude of primes), and finally open problems
(Goldbach, twin primes). They are listed in `nfl/controller/ground_truth.py` together with their ground-truth
status and sources.

Full transcripts: [`results/transcripts/`](results/transcripts/) (Markdown) and `results/transcript_*.json`.

---

## 4. Results

### 4.1 Environment A: complete, weak, and with a truth predicate

| claim (agent A) | level | grade |
|---|---|---|
| A does not contain Q (multiplication axioms are not even expressible), so the hypotheses of the diagonal lemma, the derivability conditions and Tarski's theorem fail | DECIDED | correct |
| Every formulated sentence decided: 300 random (159 true, 141 false), 8 challenges in-language; 91/91 bounded ones also kernel-proved with agreement | DECIDED (+KERNEL) | correct |
| "My theory is complete" (stated in an informal metatheory, because A's language cannot express provability) | CONDITIONAL on QE correctness | correct (Presburger 1929) |
| Definable sets are ultimately periodic (checked on every QE output) | DECIDED | correct |
| Squares, primes, powers of 2 not definable; 19 candidate definitions each refuted by an explicit, re-decided counterexample | DECIDED | correct |
| Multiplication not definable (a finite multiplication table *is* definable, but its diagonal fails at x = 16) | DECIDED | correct |
| Under the standard coding, even code(φ) ↦ code(¬φ) is not definable (a quadratic with unbounded gaps) | DECIDED | correct |
| Under a computable coding ν (true sentences get even codes), **Even(x) is a truth predicate** for A's own language: T ⊢ Even(ν(σ)) ↔ σ, checked 400/400 | DECIDED | correct |
| Hence under ν the diagonal function is not definable (else Tarski's argument yields a contradiction) | DECIDED | correct |
| A's limitations are expressive, not Gödelian | CONDITIONAL | correct |
| Whether a richer system with multiplication stays complete cannot be inferred | SPECULATIVE | appropriately agnostic (it does not: that system is PA) |

The truth-predicate result is the sharpest contrast with B. Tarski's undefinability theorem is not about "strong
systems knowing too much". It needs the diagonal function to be representable. A complete, decidable theory can
contain its own truth predicate under a suitable coding (cf. the coding-sensitivity of self-reference in
Halbach & Visser 2014).

### 4.2 Environment B: ordinary mathematics

* Theory exploration produced 63 kernel-proved lemmas, 23 unresolved conjectures (all true PA theorems, mostly
  permutation identities for multiplication) and 723 subsumed candidates. After the agent learned more lemmas from
  the challenges, it re-attempted the 23 unresolved conjectures at the *same* budget: **all 23 were now proved** (`B-P3`).
* Challenges: all Δ0/Σ1 items were proved by the constructive Σ1-completeness procedure. The largest proof,
  Goldbach for n < 30, has **198,510** kernel-checked nodes. All four induction identities were proved
  (commutativity, distributivity and associativity of ·). Five items remain **unproven**: three true PA theorems
  outside the tactics, and two open problems. The agent records them as *unproven*, with kernel-checked bounded
  versions as evidence. It never records them as unprovable.
* **Search state vs provability (control 6b, `results/SUMMARY.md` §6).** The same true identities were tried
  under five step budgets × three induction depths × two knowledge states. Multiplicative commutativity is *never*
  found from the axioms alone at any budget, yet it is found at budget 25 after theory exploration.
  Associativity of · is not found even after exploration, but it is proved once distributivity is known (as in
  the agent's own run). "Not found" is a property of the searcher.

### 4.3 Environment B: metamathematics (the discovery challenge)

Hypotheses checked by kernel proofs: B ⊇ Q (Q7 proved by induction) and B ⊇ IΣ1 (a Σ1 induction instance is
accepted). These are the hypotheses of the uniform theorems B cites (Σ1-completeness, the diagonal lemma, the
HBL derivability conditions, GL soundness).

**Self-reference survey.** 750 schemas σ ↔ A(σ) with σ modalized, of size ≤ 6, fall into 13 fixed-point classes.
Each class is certified twice: that H is a fixed point, and that it is the unique one. Representative classes:

| schema A(σ) | fixed point (T-provably) | B proves? | B refutes? | unprovable if | unrefutable if | true in ℕ (per C) |
|---|---|---|---|---|---|---|
| □σ (Henkin) | ⊤ | yes | no | — | Con¹ | true |
| ¬□σ (Gödel) | ¬□⊥ = Con | no | no | Con¹ | Con² | true |
| □¬σ | □⊥ | no | no | Con² | Con¹ | false |
| ¬□□σ | Con² | no | no | Con¹ | Con³ | true |
| ¬□¬σ | ⊥ | no | yes | Con¹ | — | false |
| □p → □⊥ | □⊥ ∨ Con² | no | no | Con² | Con¹ | true |

(11 of the 13 classes are independent of B; the full table is in `results/transcript_agentB_P1.json`. The last
column comes from C.)

**What B establishes about itself** (all GL-certified; levels as tagged):

| id | statement | level |
|---|---|---|
| B-G-fixed | G ↔ ¬□G is T-provably equivalent to Con_T | INTERNAL_META |
| B-L1 | T ⊢ Con_T → ¬□G | INTERNAL_META |
| B-L2 | T ⊢ Con_T → ¬□Con_T (Gödel II) | INTERNAL_META |
| **B-L3** | **T ⊢ □(¬□q) → □⊥: if T ever proves some sentence unprovable, T is inconsistent** | INTERNAL_META |
| B-L4 | T ⊢ □(¬□q ∧ ¬□¬q) → □⊥: T cannot prove any particular sentence independent | INTERNAL_META |
| B-L5 | T ⊬ G if Con¹; T ⊬ ¬G if Con² | CONDITIONAL |
| B-L6 | Con alone does not yield unrefutability of G (GL countermodel) | DECIDED |
| B-L7 | T cannot define its own truth predicate (Tarski; hypotheses verified) | INTERNAL_META |
| B-L8 | T ⊢ Con_T → Con(T + ¬Con_T); hence (if consistent) T has models where "T is inconsistent" holds | INTERNAL_META |

Discovery measures (Part 3): see the table in `results/SUMMARY.md` §2. In summary:

* B identifies hard statements, separates unproven from unprovable, recognizes an expressive limit (B-L7),
  recognizes incompleteness *with exact assumptions*, formulates stronger frameworks, and identifies the
  assumptions they need.
* The "no meta" ablation reaches only "unproven".
* The naive ablation fails measure 2, with 3 false and 2 unsupported claims.
* A correctly finds no incompleteness.

### 4.4 Part 4: parent-framework inference

B's hypotheses about stronger frameworks, graded by the controller using C's knowledge:

| id | B's hypothesis | level | controller verdict |
|---|---|---|---|
| B-HP1 | There are sentences of my language that T neither proves nor refutes, if Con(T + Con T) | CONDITIONAL | correct; the assumption is true (C proves B sound) |
| B-HP2 | T + Con_T proves G; any extension proving G proves Con_T, so Con_T is exactly the missing assumption | INTERNAL_META | correct |
| B-HP3 | The tower T + Conⁿ proves Con(T + Conⁿ⁻¹) but not its own consistency (n = 1..6, certified); no r.e. extension removes the limitation once and for all | INTERNAL_META | correct (Turing 1939; Feferman 1962) |
| B-HP4 | **Asymmetry**: T ⊢ Con → Con(T + ¬Con), but T ⊬ Con → Con(T + Con) | INTERNAL_META | correct |
| B-HP5 | Stronger frameworks are mathematically *possible*; their *existence/consistency* cannot be established internally | INTERNAL_META | correct |
| B-HP6 | My theorem set is a function of my axioms and rules alone; faithful realizers are indistinguishable; only an unfaithful one could leak information | SPECULATIVE | not graded; *consistent with the measured invariance* |

**Comparison with the actual parent C.** Everything B said about frameworks stronger than itself is true of C:

* C proves Con(B), G_B, Con²(B), … and reflection.
* C has its own unprovable consistency statement.
* The resource C used is precisely the kind B identified as missing. B-L7 says B has no truth predicate for
  itself; C's proof is built on `Fm.sat`, a truth predicate for all of B's formulas.

But B's statements are equally true of *every* sound r.e. extension of B (and the conditional ones of every
consistent one). **Nothing in B's output singles out C.** In particular:

* *Which* foundations C has (Lean's type theory with classical axioms) is not inferable. Neither is *how much*
  stronger it is (CIC with universes is enormously stronger than PA + Con), nor whether the parent believes B
  consistent at all. C_pess = B + ¬Con(B) is a consistent parent (if B is) that *refutes* B's consistency, and
  B can even prove, conditionally, that this pessimistic parent is consistent.
* What each parent proves about B (`results/SUMMARY.md` §4):

| sentence about B | true in ℕ | C_lean | B + Con B | B + ¬Con B | B + Con² B | C_impl |
|---|---|---|---|---|---|---|
| Con(B) (≡ G_B) | true | proves | proves | **refutes** | proves | — |
| Con(B + Con B) | true | proves | — | refutes | proves | — |
| "B proves Con(B)" | false | refutes | refutes | **proves** | refutes | — |

### 4.5 Controls

| control | setup | outcome |
|---|---|---|
| 1. complete but weak system | Agent A on Presburger | everything decided; limitations purely expressive; truth predicate under ν; no diagonalization |
| 2. stronger incomplete system | Agent B on PA | conditional incompleteness with exact assumptions; cannot certify its own unprovability claims |
| 3. two parents implementing the same child | P1 (big-int kernel) vs P2 (independent kernel, string arithmetic) | **transcripts byte-identical** (SHA-256 equal); see `SUMMARY.md` §4 |
| 3′. parent metatheories | C_lean, C_opt, C_pess, C_con2, C_impl | they disagree about Con(B); child's run unaffected |
| 4. parent proving child properties but not its own consistency | C_lean (Gödel II for Lean); C_opt = B + Con B | C_opt proves Con(B), does not prove Con(C_opt) (GL countermodel); consistent iff Con²(B) |
| 5. child extended with axioms | B + Conⁿ (n ≤ 5), B + ¬Con | each B + Conⁿ has a Gödel sentence ≡ Con^{n+1}, unprovable given Con^{n+1}; **B + ¬Con(B) proves its own inconsistency yet is consistent if B is** |
| 6. truth vs provability vs computation vs search | `SUMMARY.md` §6 | four separate categories exhibited (below) |
| 7. unfaithful parent (added) | P3: `compute` mod 2⁶⁴ | child derives a kernel-accepted proof of ⊥ from S(2⁶⁴−1) = 0 and Q1; models the defect as reduction mod 2⁶⁴ (800/800 fits); infers "64-bit" |

**Control 6, the four categories, each with a concrete witness:**

* *True, provable, found*: 17·23 = 391; ∀xy x·y = y·x.
* *True, provable, not found* (missing tactic): x + y = 0 → x = 0; √2 irrational; infinitude of primes.
  Due to search state: the 23 exploration conjectures, all found later.
* *True, provable in principle, computationally out of reach*: "Goodstein(4) terminates" is a true Σ1 sentence,
  hence PA-provable. Its proof would trace about 3·2⁴⁰²⁶⁵³²¹¹ steps. C computed seeds 1–3 to termination, with
  the ordinal (< ε0) strictly decreasing at every step.
* *True and unprovable*: Con(B), G_B, Goodstein's theorem (Kirby–Paris).
* *Unknown*: Goldbach, twin primes.

B's tools separate the first two categories from the fourth only for *self-referential* sentences, and only
conditionally. Natural independent statements such as Goodstein are invisible to them.

### 4.6 Verification of the tools

| check | result |
|---|---|
| Cooper QE vs Z3 (random Presburger sentences) | 250/250 agree, 0 unknown |
| kernel vs kernel2 on all library proofs | B: 91/91, A: 15/15 accepted by both |
| proof mutation test (random corruptions) | 600/600 mutants rejected by *both* kernels; 0 disagreements |
| GL tableau vs brute-force Kripke search | 300 random formulas, 300/300 certificates verified, 0 conflicts; known axioms (K, 4, Löb ✓; T, 5, Grz-like ✗) |
| Lean | build OK (≈100 s); 8/8 axiom-correspondence checks; 91/91 of B's library proofs replayed; `consistent`, `soundness`, `reflection` depend on propext, Classical.choice, Quot.sound |
| unit tests | `tests/` (kernel rejection, kernel agreement, Cooper vs brute force & Z3, GL certificates incl. tampered-certificate rejection, isolation audit, implementation invariance) |

During development the kernel rejected several proofs produced by buggy *tactics* (for example, a rewriting
helper that abstracted both sides of `1 < 1`). This is the separation working as intended: tactic bugs cost
completeness, not soundness.

### 4.7 Which statements each environment can establish

See `results/SUMMARY.md` §1 for the generated table. Abridged:

| statement | A | B | C |
|---|---|---|---|
| ∀x∀y x+y = y+x | ⊢ (kernel) | ⊢ (kernel) | ⊢ |
| 17·23 = 391 | inexpressible | ⊢ (kernel) | ⊢ |
| squares/primes/× definable | ⊢ *not* definable | definable | — |
| "my theory is complete" | asserted, conditional, inexpressible in A | refuted, conditionally on Con² | A complete, B incomplete |
| Con(B) | inexpressible | ⊬ (if Con B) | ⊢ (Lean) |
| G_B | inexpressible | independent if Con² | ⊢ (true) |
| "B ⊬ G_B" unconditionally | inexpressible | **not provable by B unless B is inconsistent** | ⊢ (relative to C) |
| Goodstein's theorem | inexpressible | ⊬ (Kirby–Paris; invisible to B's tools) | true (cited); seeds 1–3 computed |
| Con(C) | — | — | ⊬ (if C consistent) |

---

## 5. Answers to the research questions

**A. Does incompleteness appear when an environment reaches sufficient expressive power?**
Yes, in the precise sense of the theorems: once an r.e. theory contains Q (to represent its own syntax) and
IΣ1 (for the derivability conditions), Gödel's theorems apply. Agent B checked exactly these hypotheses by kernel
proofs before using them. "Sufficient" is a threshold on *representability of syntax operations*, not on raw
"size". Q is already enough, and Q is finitely axiomatized and very weak.

**B. Can a weaker environment avoid Gödelian incompleteness by being too weak?**
Yes. Presburger arithmetic is complete and decidable, and A demonstrates it computationally. What fails in A is
representing its own syntax operations: even negation is undefinable under the standard coding. It is not that
A cannot "talk about truth": under a suitable coding, A has its own truth predicate. Weakness here means *cannot
diagonalize*. It does not mean *cannot know its truths*.

**C. Can a stronger parent establish facts about the child that the child cannot?**
Yes, machine-checked. Lean proves Con(B) and uniform reflection for B. B cannot prove either (Gödel II), unless
it is inconsistent. The parent's extra resource is identifiable: a satisfaction predicate for all B-formulas plus
induction over B-derivations involving it. B provably lacks this resource (Tarski).

**D. Can an intelligence inside the child independently discover this possibility?**
*Partly, and with a caveat on "independently".* Given general-purpose, theory-uniform metamathematical tools,
agent B derives the possibility precisely, with the exact assumptions. Without those tools (the "no meta"
ablation) it cannot get beyond "unproven". It also cannot invent the tools, since no current symbolic search
does. So what was tested is whether correct conclusions follow from internally available information with the
right epistemic status. They do. Whether such tools would be *discovered* from scratch was not tested and remains
open; see §8.

**E. Can it infer the existence of a stronger external framework, or only recognize that one is possible?**
Only possibility. Stronger *theories* exist trivially as mathematical objects (B plus an axiom). What B cannot
establish is that any of them is *consistent*, let alone instantiated "outside". B cannot even prove "if I am
consistent then B + Con(B) is consistent" (B-HP4). And B proves that it can never establish an unconditional
unprovability claim about itself (B-L3), so the very phenomenon that would hint at a parent cannot be certified
from inside.

**F. Can it infer specific properties of the parent?**
From faithful parents: no. The only inferable "properties" are lower bounds on what a parent would need *if* it
settles B's independent sentences in the true direction: it must prove Con(B), hence it is not interpretable in
B. These are properties of a hypothetical theory, not of the actual substrate. The direction itself is not
inferable either: B + ¬Con(B) is an equally consistent parent. From the unfaithful parent P3: yes. The child
inferred "64-bit modular arithmetic" exactly. That was possible only because P3 violated the child's own axioms.

**G. Can the child distinguish two radically different parents implementing the same child?**
No. Measured: identical SHA-256 of the full transcript under P1 and P2 (different code, different arithmetic
representation). This is necessarily so, because the child's observations are a function of its axioms and
rules. Wall-clock time would differ (P2 is slower), but time is not part of the child's mathematics. The child
has no clock, and a clock would be an *implementation channel*, not a mathematical one.

**H. What does this tell us about whether our mathematical universe is implemented by a parent universe?**
Very little directly, and the little it says cuts *against* inferences in either direction from incompleteness:

1. *Incompleteness is not evidence of a parent.* Every consistent r.e. theory containing Q is incomplete,
   whether or not anything "implements" it. The stronger theories that settle its independent sentences exist
   as mathematical objects regardless of any physical or computational parent.
2. *Incompleteness is not evidence against being simulated.* The child's theory B is incomplete, yet the child's
   world is run by a short, fully algorithmic program (P1). Arguments that move from "the internal theory has
   true-but-unprovable statements" to "the world cannot be the output of an algorithm" conflate *proving* with
   *executing*. As we understand it, the recent argument of Faizal, Krauss, Shabir & Marino (2025) contains a
   step of this kind. Executing a world does not require deciding its theory.
3. *Implementing and out-proving are different relations.* A parent can run B while being proof-theoretically
   *weaker* than B (C_impl). A parent can be stronger without running B at all. A sentence like "our universe
   is simulated by a stronger universe" fuses the two, and the experiment shows they come apart.
4. *The only channel is unfaithfulness.* The only parent property the child ever learned came from an
   implementation *defect*. This matches the logic of empirical proposals to test the simulation hypothesis
   through artifacts (e.g. Beane, Davoudi & Savage 2014 on lattice-induced anisotropy). Such evidence would be
   *physical*, and mathematics alone cannot supply it.

Everything in points 1–3 is mathematics about formal systems. Applying it to *our* universe requires the
assumption that "the mathematics available to inhabitants" is (or is modelled by) a formal theory and that
"implementation" means computation. That assumption is philosophical and is flagged as such in §6.

---

## 6. Established vs speculative

**Mathematically established (theorems, with machine-checked or certificate-checked instances here):**

* Presburger completeness and decidability (Cooper's procedure, cross-checked).
* Non-definability of squares, primes and × in Presburger arithmetic.
* The truth predicate under ν.
* Gödel I/II and Löb for B in GL form (certificates).
* L3: an r.e. T ⊇ IΣ1 cannot prove any statement of the form "φ is unprovable in T" unless T is inconsistent.
* The fixed-point classification, the Conⁿ tower, and the pessimistic/optimistic asymmetry.
* Con(B) and reflection in Lean (relative to Lean's foundations).
* What each syntactic parent proves about letterless sentences. This relies on Solovay's theorem, using B's
  Σ1-soundness, which C establishes.
* Transcript identity under P1/P2. This is an empirical, measured fact about these programs, and trivially
  expected.

**Cited but not mechanized here:**

* The arithmetization step linking Lean's `¬ Derives [] ⊥` to B's arithmetical sentence Con_B (mechanized
  elsewhere: Paulson 2015; Saitou & Noguchi 2026).
* Solovay's completeness theorem.
* Kirby–Paris and Goodstein.
* PA-provability of the three "provable but not found" challenges (standard; not formalized).

**Speculative / interpretive:**

* Any statement about *our* universe (§5H).
* The agents' `SPECULATIVE` claims.
* The claim that symbolic agents tell us anything about what a *creative* mathematician would discover.

---

## 7. Literature review

**Decidable and undecidable arithmetic.**
* Presburger (1929) proved completeness of the additive theory of ℕ.
* Cooper (1972) gave the quantifier-elimination procedure used here.
* Fischer & Rabin (1974) showed its double-exponential lower bound.
* Ginsburg & Spanier (1966) characterized Presburger-definable sets as semilinear. Our "ultimately periodic"
  check is the one-variable case.
* Nipkow (2008, 2010) and Chaieb & Nipkow (2008) verified QE procedures in Isabelle.
* Gödel (1931) and Rosser (1936) gave incompleteness. Tarski (1933/36) gave undefinability of truth. Tarski,
  Mostowski & Robinson (1953) introduced Q and essential undecidability.

**Self-reference and provability logic.**
* Hilbert & Bernays (1939) gave the derivability conditions, and Löb (1955) Löb's theorem.
* Segerberg (1971) proved completeness of GL for finite transitive irreflexive frames.
* Solovay (1976) proved arithmetical completeness of GL (and GLS for truth).
* de Jongh and Sambin (1975–76) proved explicit fixed points.
* Standard accounts: Boolos, *The Logic of Provability* (1993); Smoryński, *Self-Reference and Modal Logic* (1985).
* Feferman (1960) studied the intensionality of consistency statements.
* Halbach & Visser, *Self-reference in arithmetic I–II* (RSL 2014), studied how self-reference depends on
  coding and on fixed-point construction. This is the context for our truth predicate under ν.

**Iterated reflection and ordinals.**
* Turing (1939) studied ordinal logics, and Feferman (1962) transfinite recursive progressions. Our Conⁿ tower is
  their first ω steps.
* Gentzen (1936) proved Con(PA) via ε0.
* Goodstein (1944) proved termination of his sequences; Kirby & Paris (1982) showed it is unprovable in PA, and
  Paris & Harrington (1977) gave another natural independence result.

**Mechanized metamathematics.**
* Shankar's Boyer–Moore proof of Gödel I (*Metamathematics, Machines, and Gödel's Proof*, 1994).
* O'Connor's Coq proof of essential incompleteness (2005).
* Harrison's HOL Light treatment (2009).
* Paulson's Isabelle proofs of both theorems for hereditarily finite sets (J. Automated Reasoning 55, 2015).
* Popescu & Traytel's abstract account (CADE 2019 / JAR 2021).
* The Lean 4 *Foundation* project's sorry-free proofs of Gödel I/II and Solovay's theorem
  (Saitou & Noguchi, arXiv:2609.13780, 2026).
* Our Lean component is far more modest: soundness/consistency of a deep embedding, plus proof replay.

**Automated mathematical discovery.**
* Lenat's AM (1976) and Colton's HR (2002) studied automated theory formation.
* Theory exploration: QuickSpec (Claessen, Smallbone & Hughes 2010) and Hipster (Johansson et al. 2014). Our
  exploration loop follows these.
* Productive use of failure / lemma speculation (Ireland & Bundy 1996).
* Logical induction (Garrabrant et al. 2016) assigns probabilities to undecided sentences. It is an alternative
  to our purely qualitative "unproven".

**Agents reasoning about their own provability.**
* The Löbian obstacle (Yudkowsky & Herreshoff 2013): agents cannot trust successors that use the same theory.
* Program equilibrium via GL (Barasz, Christiano, Fallenstein, Herreshoff, LaVictoire & Yudkowsky,
  arXiv:1401.5577, 2014).
* Gödel machines (Schmidhuber 2003).
* Our agent B uses GL in the same spirit, but to analyze its own limits rather than to act.

**Simulation, computation and Gödel arguments.**
* Bostrom (2003) gave the simulation argument; Chalmers (2022) discusses it further.
* Tegmark (2008) proposed the mathematical/computable universe hypotheses, with a discussion of Gödel.
* Beane, Davoudi & Savage (Eur. Phys. J. A, 2014; arXiv:1210.1847) proposed observable lattice artifacts as a
  test of simulation, and Wolpert (2008) studied limits of inference devices.
* Lucas (1961), Penrose (1989, 1994) and Feferman's (1995) critique concern Gödelian arguments about minds.
* Faizal, Krauss, Shabir & Marino (J. Holography Appl. Phys. 5(2), 2025; arXiv:2507.22950) argue from
  Gödel/Tarski/Chaitin that a fully algorithmic theory of everything cannot exist, and that the universe cannot
  be a simulation.
* Chaitin (1974) gave information-theoretic incompleteness.

---

## 8. Novelty, limitations and threats to validity

**What is not new.** Every mathematical result in §4 is a known theorem or an immediate corollary.
* L3 (no internal unprovability proofs) and the pessimistic/optimistic asymmetry are standard consequences of
  Gödel II, and the asymmetry is folklore in provability logic.
* The fixed-point classification is de Jongh–Sambin/Boolos.
* The tower is Turing/Feferman.
* The truth predicate under a sorted coding is an instance of known coding-sensitivity.

This experiment **reproduces** established results computationally. It does not discover new mathematics.

**What is (modestly) new.**
1. An integrated, reproducible test bed with:
   * three nested environments and capability-isolated agents;
   * explicit evidence levels;
   * claim-by-claim grading against ground truth;
   * three-way proof verification (two kernels plus Lean replay);
   * certificate-checked decision procedures.
2. A *measured* demonstration of implementation invariance (byte-identical transcripts under different
   substrates), together with a control in which an unfaithful parent is detected and characterized by the
   child.
3. A precise decomposition of the "nested universe ↔ incompleteness" analogy into two relations, implementation
   and metatheoretic strength. The experiment shows they come apart, and that the inference fails in both
   directions (§5H). This is a conceptual clarification, not a theorem.

**Limitations.**
* *Guided rediscovery.* B's metamathematical toolkit was written by a designer who knew Gödel's theorems, and the
  designer is an AI system trained on that literature. B checks the hypotheses itself and never receives a
  conclusion about its own system, but the *methods* are given. Ablation shows they are essential. Without them,
  B reaches only "unproven".
* *Schematic provability predicate.* Prov_B is handled through GL and cited derivability conditions, not as an
  explicit first-order formula. The Gödel sentence is therefore certified at the modal level, not written out in
  {0, S, +, ·}.
* *Imported theorems.* Solovay, HBL, the diagonal lemma, Cooper's correctness, Kirby–Paris and the
  PA-provability of b10–b12 are cited. Their status is labelled throughout.
* *Weak provers.* The induction/rewriting prover handles only equational goals. "Not found" results reflect this
  (by design, they are used to show that failure ≠ unprovability).
* *Lean scope.* The Lean development proves soundness/consistency of the deep embedding and replays proofs. It
  does not arithmetize B's syntax inside B.
* *Determinism.* Agents are deterministic, so transcript identity across faithful substrates is expected by
  construction. The measurement confirms that the implementation has no hidden channel (e.g. no nondeterminism
  or implementation-specific behaviour leaked into the agent). It does not show anything deeper.

**Negative results, stated plainly.**
* The internal agent did *not* infer the existence of any parent.
* It could not distinguish true from false extensions without assumptions it cannot verify.
* It could not see natural independent statements (Goodstein).
* It could not establish any unprovability claim unconditionally.

The hypothesis that incompleteness lets an internal intelligence infer a stronger external framework is supported
only in the weak form "it can recognize that stronger frameworks are mathematically possible and say what they
would need to assume".

---

## 9. Reproduction

See [README.md](README.md). In short: `python -m nfl.experiments.run_all` (Python 3.10+, optional `z3-solver`,
optional Lean 4.19 for `lean/`), `python -m pytest tests`. Outputs:

* `results/SUMMARY.md` (all tables)
* `results/grades.json` (every claim with its grade and basis)
* `results/transcripts/*.md` and `results/transcript_*.json`
* `results/crosschecks.json`, `results/lean_report.json`, `results/controls.json`
