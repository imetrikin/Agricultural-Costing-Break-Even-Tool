/-
  Environment C (the "parent" metatheory), part 1: a deep embedding of the
  syntax and standard semantics of Environment B (first-order Peano arithmetic
  in the language {0, S, +, *, <, =} with numeral literals).

  Terms and formulas use de Bruijn indices.  Only Lean 4 core is used.
-/

namespace NL

inductive Tm where
  | var  : Nat → Tm
  | zero : Tm
  | succ : Tm → Tm
  | add  : Tm → Tm → Tm
  | mul  : Tm → Tm → Tm
  | lit  : Nat → Tm          -- numeral literal (the Python side only uses positive literals)
  deriving DecidableEq, Repr

inductive Fm where
  | eq  : Tm → Tm → Fm
  | lt  : Tm → Tm → Fm
  | bot : Fm
  | imp : Fm → Fm → Fm
  | and : Fm → Fm → Fm
  | or  : Fm → Fm → Fm
  | all : Fm → Fm
  | ex  : Fm → Fm
  deriving DecidableEq, Repr

/-- numeral: 0 is the constant, n+1 is a literal -/
def num : Nat → Tm
  | 0 => .zero
  | n+1 => .lit (n+1)

/-- extend an assignment by a new value for index 0 -/
def scons (a : Nat) (ρ : Nat → Nat) : Nat → Nat
  | 0 => a
  | n+1 => ρ n

def Tm.eval (ρ : Nat → Nat) : Tm → Nat
  | .var n => ρ n
  | .zero => 0
  | .succ t => t.eval ρ + 1
  | .add a b => a.eval ρ + b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ
  | .lit n => n

/-- Tarskian satisfaction in the standard model ℕ.  Defining this by recursion
    on formulas is exactly the resource B lacks (Tarski: B cannot define its
    own truth predicate). -/
def Fm.sat : Fm → (Nat → Nat) → Prop
  | .eq a b, ρ => a.eval ρ = b.eval ρ
  | .lt a b, ρ => a.eval ρ < b.eval ρ
  | .bot, _ => False
  | .imp p q, ρ => p.sat ρ → q.sat ρ
  | .and p q, ρ => p.sat ρ ∧ q.sat ρ
  | .or p q, ρ => p.sat ρ ∨ q.sat ρ
  | .all p, ρ => ∀ a, p.sat (scons a ρ)
  | .ex p, ρ => ∃ a, p.sat (scons a ρ)

/-! ### Parallel substitution -/

def Tm.subst (σ : Nat → Tm) : Tm → Tm
  | .var n => σ n
  | .zero => .zero
  | .succ t => .succ (t.subst σ)
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .mul a b => .mul (a.subst σ) (b.subst σ)
  | .lit n => .lit n

def Tm.shift (t : Tm) : Tm := t.subst (fun n => .var (n+1))

def up (σ : Nat → Tm) : Nat → Tm
  | 0 => .var 0
  | n+1 => (σ n).shift

def Fm.subst (σ : Nat → Tm) : Fm → Fm
  | .eq a b => .eq (a.subst σ) (b.subst σ)
  | .lt a b => .lt (a.subst σ) (b.subst σ)
  | .bot => .bot
  | .imp p q => .imp (p.subst σ) (q.subst σ)
  | .and p q => .and (p.subst σ) (q.subst σ)
  | .or p q => .or (p.subst σ) (q.subst σ)
  | .all p => .all (p.subst (up σ))
  | .ex p => .ex (p.subst (up σ))

def Fm.shift (p : Fm) : Fm := p.subst (fun n => .var (n+1))

/-- substitution of `t` for index 0 (other indices move down by one) -/
def inst0 (t : Tm) : Nat → Tm
  | 0 => t
  | n+1 => .var n

def Fm.subst0 (p : Fm) (t : Tm) : Fm := p.subst (inst0 t)

/-- x ↦ S x for index 0, other indices unchanged (used by the induction schema) -/
def succ0 : Nat → Tm
  | 0 => .succ (.var 0)
  | n+1 => .var (n+1)

/-! ### Substitution lemmas -/

theorem Tm.eval_subst (σ : Nat → Tm) (ρ : Nat → Nat) (t : Tm) :
    (t.subst σ).eval ρ = t.eval (fun n => (σ n).eval ρ) := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [Tm.subst, Tm.eval, ih]
  | add a b iha ihb => simp [Tm.subst, Tm.eval, iha, ihb]
  | mul a b iha ihb => simp [Tm.subst, Tm.eval, iha, ihb]
  | lit n => rfl

theorem Tm.eval_shift (a : Nat) (ρ : Nat → Nat) (t : Tm) :
    t.shift.eval (scons a ρ) = t.eval ρ := by
  unfold Tm.shift
  rw [Tm.eval_subst]
  rfl

theorem up_eval (σ : Nat → Tm) (a : Nat) (ρ : Nat → Nat) :
    (fun n => (up σ n).eval (scons a ρ)) = scons a (fun n => (σ n).eval ρ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [up, scons, Tm.eval_shift]

theorem Fm.sat_subst (p : Fm) : ∀ (σ : Nat → Tm) (ρ : Nat → Nat),
    (p.subst σ).sat ρ ↔ p.sat (fun n => (σ n).eval ρ) := by
  induction p with
  | eq a b => intro σ ρ; simp [Fm.subst, Fm.sat, Tm.eval_subst]
  | lt a b => intro σ ρ; simp [Fm.subst, Fm.sat, Tm.eval_subst]
  | bot => intro σ ρ; simp [Fm.subst, Fm.sat]
  | imp p q ihp ihq => intro σ ρ; simp [Fm.subst, Fm.sat, ihp, ihq]
  | and p q ihp ihq => intro σ ρ; simp [Fm.subst, Fm.sat, ihp, ihq]
  | or p q ihp ihq => intro σ ρ; simp [Fm.subst, Fm.sat, ihp, ihq]
  | all p ih =>
    intro σ ρ
    simp only [Fm.subst, Fm.sat]
    constructor
    · intro h a; have := (ih (up σ) (scons a ρ)).mp (h a); rwa [up_eval] at this
    · intro h a; apply (ih (up σ) (scons a ρ)).mpr; rw [up_eval]; exact h a
  | ex p ih =>
    intro σ ρ
    simp only [Fm.subst, Fm.sat]
    constructor
    · intro ⟨a, h⟩; refine ⟨a, ?_⟩; have := (ih (up σ) (scons a ρ)).mp h; rwa [up_eval] at this
    · intro ⟨a, h⟩; refine ⟨a, ?_⟩; apply (ih (up σ) (scons a ρ)).mpr; rw [up_eval]; exact h

theorem Fm.sat_shift (p : Fm) (a : Nat) (ρ : Nat → Nat) :
    p.shift.sat (scons a ρ) ↔ p.sat ρ := by
  unfold Fm.shift
  rw [Fm.sat_subst]
  rfl

theorem Fm.sat_subst0 (p : Fm) (t : Tm) (ρ : Nat → Nat) :
    (p.subst0 t).sat ρ ↔ p.sat (scons (t.eval ρ) ρ) := by
  unfold Fm.subst0
  rw [Fm.sat_subst]
  have : (fun n => (inst0 t n).eval ρ) = scons (t.eval ρ) ρ := by
    funext n; cases n <;> rfl
  rw [this]

theorem Fm.sat_succ0 (p : Fm) (a : Nat) (ρ : Nat → Nat) :
    (p.subst succ0).sat (scons a ρ) ↔ p.sat (scons (a+1) ρ) := by
  rw [Fm.sat_subst]
  have : (fun n => (succ0 n).eval (scons a ρ)) = scons (a+1) ρ := by
    funext n; cases n <;> rfl
  rw [this]

theorem num_eval (n : Nat) (ρ : Nat → Nat) : (num n).eval ρ = n := by
  cases n <;> rfl

end NL
