/-
  Environment C, part 2: Environment B's axioms and natural-deduction rules,
  represented *inside* the parent, and the parent's theorems about them:

    * `soundness`   : every B-derivation is true in the standard model ℕ
    * `consistent`  : B does not derive ⊥                       (Con(B))
    * `reflection`  : B ⊢ φ  implies  φ is true                 (uniform reflection for B)

  The rules mirror the Python kernel (nfl/logic/kernel.py) rule-for-rule, with
  contexts carried top-down (lists) and variables as de Bruijn indices, so that
  proofs produced by the Python agents can be replayed here (see Replay.lean).
-/
import NestedLimits.Basic

namespace NL
open Tm Fm

/-- The axioms of B (exactly those in nfl/logic/theories.py:peano). -/
inductive IsAxiom : Fm → Prop where
  | q1 : IsAxiom (.all (.imp (.eq (.succ (.var 0)) .zero) .bot))
  | q2 : IsAxiom (.all (.all (.imp (.eq (.succ (.var 1)) (.succ (.var 0))) (.eq (.var 1) (.var 0)))))
  | q3 : IsAxiom (.all (.eq (.add (.var 0) .zero) (.var 0)))
  | q4 : IsAxiom (.all (.all (.eq (.add (.var 1) (.succ (.var 0))) (.succ (.add (.var 1) (.var 0))))))
  | q5 : IsAxiom (.all (.eq (.mul (.var 0) .zero) .zero))
  | q6 : IsAxiom (.all (.all (.eq (.mul (.var 1) (.succ (.var 0))) (.add (.mul (.var 1) (.var 0)) (.var 1)))))
  | l1 : IsAxiom (.all (.imp (.lt (.var 0) .zero) .bot))
  | l2 : IsAxiom (.all (.all (.and
          (.imp (.lt (.var 1) (.succ (.var 0))) (.or (.lt (.var 1) (.var 0)) (.eq (.var 1) (.var 0))))
          (.imp (.or (.lt (.var 1) (.var 0)) (.eq (.var 1) (.var 0))) (.lt (.var 1) (.succ (.var 0)))))))
  /-- induction schema, for every formula (parameters allowed) -/
  | ind (p : Fm) : IsAxiom (.imp (.and (p.subst0 .zero) (.all (.imp p (p.subst succ0)))) (.all p))
  /-- numeral literals: (n+1) = S(n) -/
  | numAx (n : Nat) : IsAxiom (.eq (num (n+1)) (.succ (num n)))

/-- Natural deduction for B with explicit contexts. -/
inductive Derives : List Fm → Fm → Prop where
  | hyp   {Γ : List Fm} {φ : Fm} : φ ∈ Γ → Derives Γ φ
  | ax    {Γ : List Fm} {φ : Fm} : IsAxiom φ → Derives Γ φ
  | impI  {Γ : List Fm} {φ ψ : Fm} : Derives (φ :: Γ) ψ → Derives Γ (.imp φ ψ)
  | impE  {Γ : List Fm} {φ ψ : Fm} : Derives Γ (.imp φ ψ) → Derives Γ φ → Derives Γ ψ
  | andI  {Γ : List Fm} {φ ψ : Fm} : Derives Γ φ → Derives Γ ψ → Derives Γ (.and φ ψ)
  | andE1 {Γ : List Fm} {φ ψ : Fm} : Derives Γ (.and φ ψ) → Derives Γ φ
  | andE2 {Γ : List Fm} {φ ψ : Fm} : Derives Γ (.and φ ψ) → Derives Γ ψ
  | orI1  {Γ : List Fm} {φ ψ : Fm} : Derives Γ φ → Derives Γ (.or φ ψ)
  | orI2  {Γ : List Fm} {φ ψ : Fm} : Derives Γ ψ → Derives Γ (.or φ ψ)
  | orE   {Γ : List Fm} {φ ψ χ : Fm} : Derives Γ (.or φ ψ) → Derives (φ :: Γ) χ → Derives (ψ :: Γ) χ → Derives Γ χ
  | botE  {Γ : List Fm} {φ : Fm} : Derives Γ .bot → Derives Γ φ
  | raa   {Γ : List Fm} {φ : Fm} : Derives (.imp φ .bot :: Γ) .bot → Derives Γ φ
  | allI  {Γ : List Fm} {φ : Fm} : Derives (Γ.map Fm.shift) φ → Derives Γ (.all φ)
  | allE  {Γ : List Fm} {φ : Fm} (t : Tm) : Derives Γ (.all φ) → Derives Γ (φ.subst0 t)
  | exI   {Γ : List Fm} {φ : Fm} (t : Tm) : Derives Γ (φ.subst0 t) → Derives Γ (.ex φ)
  | exE   {Γ : List Fm} {φ χ : Fm} : Derives Γ (.ex φ) → Derives (φ :: Γ.map Fm.shift) χ.shift → Derives Γ χ
  | refl  {Γ : List Fm} (t : Tm) : Derives Γ (.eq t t)
  | subst {Γ : List Fm} {φ : Fm} (s t : Tm) : Derives Γ (.eq s t) → Derives Γ (φ.subst0 s) → Derives Γ (φ.subst0 t)

/-! ### Every axiom is true in ℕ -/

theorem IsAxiom.sound {φ : Fm} (h : IsAxiom φ) (ρ : Nat → Nat) : φ.sat ρ := by
  cases h with
  | q1 => intro a h; simp [Fm.sat, Tm.eval, scons] at h
  | q2 => intro a b h; simp [Fm.sat, Tm.eval, scons] at h ⊢; omega
  | q3 => intro a; simp [Fm.sat, Tm.eval, scons]
  | q4 => intro a b; simp [Fm.sat, Tm.eval, scons]; omega
  | q5 => intro a; simp [Fm.sat, Tm.eval, scons]
  | q6 => intro a b; simp [Fm.sat, Tm.eval, scons, Nat.mul_succ]
  | l1 => intro a h; simp [Fm.sat, Tm.eval, scons] at h
  | l2 => intro a b; simp [Fm.sat, Tm.eval, scons]; omega
  | ind p =>
    intro ⟨h0, hs⟩ a
    induction a with
    | zero => exact (Fm.sat_subst0 p .zero ρ).mp h0
    | succ k ih => exact (Fm.sat_succ0 p k ρ).mp (hs k ih)
  | numAx n => simp [Fm.sat, Tm.eval, num_eval]

/-! ### Soundness, consistency, reflection -/

theorem soundness {Γ : List Fm} {φ : Fm} (d : Derives Γ φ) :
    ∀ ρ : Nat → Nat, (∀ ψ ∈ Γ, ψ.sat ρ) → φ.sat ρ := by
  induction d with
  | hyp h => intro ρ hΓ; exact hΓ _ h
  | ax h => intro ρ _; exact h.sound ρ
  | impI _ ih => intro ρ hΓ hφ; exact ih ρ (fun ψ hm => by
      cases hm with
      | head => exact hφ
      | tail _ h => exact hΓ ψ h)
  | impE _ _ ih1 ih2 => intro ρ hΓ; exact (ih1 ρ hΓ) (ih2 ρ hΓ)
  | andI _ _ ih1 ih2 => intro ρ hΓ; exact ⟨ih1 ρ hΓ, ih2 ρ hΓ⟩
  | andE1 _ ih => intro ρ hΓ; exact (ih ρ hΓ).1
  | andE2 _ ih => intro ρ hΓ; exact (ih ρ hΓ).2
  | orI1 _ ih => intro ρ hΓ; exact Or.inl (ih ρ hΓ)
  | orI2 _ ih => intro ρ hΓ; exact Or.inr (ih ρ hΓ)
  | orE _ _ _ ih ih1 ih2 =>
    intro ρ hΓ
    cases ih ρ hΓ with
    | inl h => exact ih1 ρ (fun ψ hm => by
        cases hm with
        | head => exact h
        | tail _ hm => exact hΓ ψ hm)
    | inr h => exact ih2 ρ (fun ψ hm => by
        cases hm with
        | head => exact h
        | tail _ hm => exact hΓ ψ hm)
  | botE _ ih => intro ρ hΓ; exact False.elim (ih ρ hΓ)
  | @raa Γ φ _ ih =>
    intro ρ hΓ
    exact Classical.byContradiction (fun hn => ih ρ (fun ψ hm => by
      cases hm with
      | head => exact hn
      | tail _ hm => exact hΓ ψ hm))
  | @allI Γ φ _ ih =>
    intro ρ hΓ a
    apply ih (scons a ρ)
    intro ψ hm
    rcases List.mem_map.mp hm with ⟨χ, hχ, rfl⟩
    exact (Fm.sat_shift χ a ρ).mpr (hΓ χ hχ)
  | @allE Γ φ t _ ih =>
    intro ρ hΓ
    exact (Fm.sat_subst0 φ t ρ).mpr (ih ρ hΓ (t.eval ρ))
  | @exI Γ φ t _ ih =>
    intro ρ hΓ
    exact ⟨t.eval ρ, (Fm.sat_subst0 φ t ρ).mp (ih ρ hΓ)⟩
  | @exE Γ φ χ _ _ ih1 ih2 =>
    intro ρ hΓ
    obtain ⟨a, ha⟩ := ih1 ρ hΓ
    have := ih2 (scons a ρ) (fun ψ hm => by
      cases hm with
      | head => exact ha
      | tail _ hm =>
        rcases List.mem_map.mp hm with ⟨θ, hθ, rfl⟩
        exact (Fm.sat_shift θ a ρ).mpr (hΓ θ hθ))
    exact (Fm.sat_shift χ a ρ).mp this
  | refl t => intro ρ _; rfl
  | @subst Γ φ s t _ _ ih1 ih2 =>
    intro ρ hΓ
    have e : s.eval ρ = t.eval ρ := ih1 ρ hΓ
    have h := (Fm.sat_subst0 φ s ρ).mp (ih2 ρ hΓ)
    rw [e] at h
    exact (Fm.sat_subst0 φ t ρ).mpr h

/-- Con(B): Environment B does not prove ⊥. -/
theorem consistent : ¬ Derives [] .bot := fun d =>
  soundness d (fun _ => 0) (fun _ h => nomatch h)

/-- Uniform reflection for B: whatever B proves is true in ℕ (under every assignment). -/
theorem reflection {φ : Fm} (d : Derives [] φ) (ρ : Nat → Nat) : φ.sat ρ :=
  soundness d ρ (fun _ h => nomatch h)

/-- B is not inconsistent in the weaker sense either: it never proves both φ and ¬φ. -/
theorem no_contradiction (φ : Fm) : ¬ (Derives [] φ ∧ Derives [] (.imp φ .bot)) := fun ⟨h1, h2⟩ =>
  consistent (.impE h2 h1)

/-! ### Weakening (needed to use stored lemmas inside larger contexts) -/

theorem Derives.weaken {Γ : List Fm} {φ : Fm} (d : Derives Γ φ) :
    ∀ {Δ : List Fm}, (∀ ψ ∈ Γ, ψ ∈ Δ) → Derives Δ φ := by
  induction d with
  | hyp h => intro Δ hs; exact .hyp (hs _ h)
  | ax h => intro Δ _; exact .ax h
  | impI _ ih => intro Δ hs; exact .impI (ih (fun ψ hm => by
      cases hm with
      | head => exact List.Mem.head _
      | tail _ h => exact List.Mem.tail _ (hs ψ h)))
  | impE _ _ ih1 ih2 => intro Δ hs; exact .impE (ih1 hs) (ih2 hs)
  | andI _ _ ih1 ih2 => intro Δ hs; exact .andI (ih1 hs) (ih2 hs)
  | andE1 _ ih => intro Δ hs; exact .andE1 (ih hs)
  | andE2 _ ih => intro Δ hs; exact .andE2 (ih hs)
  | orI1 _ ih => intro Δ hs; exact .orI1 (ih hs)
  | orI2 _ ih => intro Δ hs; exact .orI2 (ih hs)
  | orE _ _ _ ih ih1 ih2 =>
    intro Δ hs
    refine .orE (ih hs) (ih1 ?_) (ih2 ?_) <;>
    · intro ψ hm
      cases hm with
      | head => exact List.Mem.head _
      | tail _ h => exact List.Mem.tail _ (hs ψ h)
  | botE _ ih => intro Δ hs; exact .botE (ih hs)
  | raa _ ih => intro Δ hs; exact .raa (ih (fun ψ hm => by
      cases hm with
      | head => exact List.Mem.head _
      | tail _ h => exact List.Mem.tail _ (hs ψ h)))
  | allI _ ih =>
    intro Δ hs
    exact .allI (ih (fun ψ hm => by
      rcases List.mem_map.mp hm with ⟨χ, hχ, rfl⟩
      exact List.mem_map.mpr ⟨χ, hs χ hχ, rfl⟩))
  | allE t _ ih => intro Δ hs; exact .allE t (ih hs)
  | exI t _ ih => intro Δ hs; exact .exI t (ih hs)
  | exE _ _ ih1 ih2 =>
    intro Δ hs
    refine .exE (ih1 hs) (ih2 ?_)
    intro ψ hm
    cases hm with
    | head => exact List.Mem.head _
    | tail _ h =>
      rcases List.mem_map.mp h with ⟨χ, hχ, rfl⟩
      exact List.Mem.tail _ (List.mem_map.mpr ⟨χ, hs χ hχ, rfl⟩)
  | refl t => intro Δ _; exact .refl t
  | subst s t _ _ ih1 ih2 => intro Δ hs; exact .subst s t (ih1 hs) (ih2 hs)

theorem Derives.ofNil {Γ : List Fm} {φ : Fm} (d : Derives [] φ) : Derives Γ φ :=
  d.weaken (fun _ h => nomatch h)

end NL
