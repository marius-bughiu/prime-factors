import PrimeFactors.SquareClassPrivateRows
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! A positive point on the target conic can be missed by every ordinary
continued-fraction convergent, including after indefinitely many periods. -/
namespace PrimeFactors.TargetNormConvergents

open SquareClassPrivateRows
set_option maxRecDepth 4096

/-- When A=a²+1 the complete-quotient recurrence enters (offset a,
denominator 1) on its first step, and stays there with partial quotient 2a. -/
theorem fixed_denominators (a n : ℕ) :
    denominators (a^2+1) a n a 1 = List.replicate n 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [denominators, Nat.div_one, Nat.mul_one, Nat.add_sub_cancel,
      Nat.add_sub_cancel_left, List.replicate_succ, ih]

theorem period_one (a n : ℕ) (positive : 0<a) :
    denominators (a^2+1) (a^2+1).sqrt n 0 1 = List.replicate n 1 := by
  have root : (a^2+1).sqrt = a := (Nat.eq_sqrt'.mpr (by
    constructor <;> nlinarith)).symm
  cases n with
  | zero => rfl
  | succ n =>
    simp only [root, denominators, Nat.add_zero, Nat.div_one, Nat.mul_one, Nat.sub_zero,
      Nat.add_sub_cancel_left, List.replicate_succ, fixed_denominators]

/-- Running through an arbitrary number of complete periods never exposes
a denominator equal to twice a square, for any positive a. -/
theorem no_target_scan (a n : ℕ) (positive : 0<a) {v : ℕ}
    (hv : v ∈ denominators (a^2+1) (a^2+1).sqrt n 0 1) (t : ℕ) : v ≠ 2*t^2 := by
  rw [period_one _ _ positive] at hv
  have := List.eq_of_mem_replicate hv
  omega

/-- Standard consecutive convergents for [a; 2a, 2a, ...], starting at
(1,0), (a,1). The second pair is the current numerator and denominator. -/
def continuants (a : ℤ) : ℕ → (ℤ × ℤ) × (ℤ × ℤ)
  | 0 => ((1,0),(a,1))
  | n+1 =>
      let (prev,curr) := continuants a n
      (curr,(2*a*curr.1+prev.1, 2*a*curr.2+prev.2))

private def step (a : ℤ) (z : ℤ × ℤ) : ℤ × ℤ :=
  (a*z.1+(a^2+1)*z.2, z.1+a*z.2)

private def norm (a : ℤ) (z : ℤ × ℤ) : ℤ := z.1^2-(a^2+1)*z.2^2

private theorem norm_step (a : ℤ) (z : ℤ × ℤ) : norm a (step a z) = -norm a z := by
  dsimp [norm,step]
  ring

private theorem advances (a : ℤ) (n : ℕ) :
    (continuants a n).2 = step a (continuants a n).1 := by
  induction n with
  | zero => simp [continuants,step]
  | succ n ih =>
    generalize h : continuants a n = z at ih ⊢
    rcases z with ⟨prev,curr⟩
    simp only [continuants,h] at *
    rw [ih]
    apply Prod.ext <;> dsimp [step] <;> ring

/-- Exactly alternating norms for all ordinary convergents, at all budgets. -/
theorem convergent_norm (a : ℤ) (n : ℕ) :
    let z := (continuants a n).2
    z.1^2 - (a^2+1)*z.2^2 = (-1)^(n+1) := by
  change norm a (continuants a n).2 = _
  induction n with
  | zero => simp [norm,continuants]
  | succ n ih =>
    rw [advances a (n+1),norm_step,pow_succ _ (n+1)]
    change -norm a (continuants a n).2 = _
    rw [ih,mul_neg_one]

/-- At a=u², the first intermediate convergent [a;1]=(a+1)/1 gives the
requested positive norm 2u². Its partial quotient 1 lies strictly below 2a. -/
theorem first_intermediate (u : ℕ) (positive : 0<u) :
    1 < 2*u^2 ∧ (u^2+1)^2 = (u^4+1)*1^2+2*u^2 := by
  constructor
  · nlinarith [Nat.pow_pos positive (n:=2)]
  · ring

/-- Substitution in the family also gives a full-width integer. -/
theorem full_width :
    let a : ℕ := (2^512 - 2)^2
    2^2047 ≤ a^2+1 ∧ a^2+1 < 2^2048 := by decide +kernel

/-- All 26 bits of this product come from two distinct 13-bit primes. -/
theorem balanced_example :
    Nat.Prime 5449 ∧ Nat.Prime 6793 ∧ 5449*6793=78^4+1 ∧
    2^12≤5449 ∧ 5449<6793 ∧ 6793<2^13 ∧
    2^25≤(37015057:ℕ) ∧ 37015057<2^26 ∧ 78^4+1=(37015057:ℕ) := by norm_num

private def phase697 (o d : ℕ) : Prop :=
  (o=0 ∧ d=1) ∨ (o=26 ∧ d=21) ∨ (o=16 ∧ d=21) ∨ (o=26 ∧ d=1)

private theorem cycle697 (n o d : ℕ) (state : phase697 o d) :
    ∀ v ∈ denominators 697 26 n o d, v=1 ∨ v=21 := by
  induction n generalizing o d with
  | zero => simp [denominators]
  | succ n ih =>
    rcases state with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp only [denominators,List.mem_cons] <;> intro v hv <;>
      rcases hv with rfl|tail
    all_goals first | decide | exact ih _ _ (by unfold phase697; decide) _ tail

theorem example697_scan (n v : ℕ) (hv : v ∈ denominators 697 (Nat.sqrt 697) n 0 1) :
    ∀ t : ℕ, v ≠ 2*t^2 := by
  obtain one|twen := cycle697 n 0 1 (Or.inl ⟨rfl,rfl⟩) v hv
  all_goals intro t; omega

theorem example697_intermediate :
    Nat.Prime 17 ∧ Nat.Prime 41 ∧ 17*41=(697:ℕ) ∧ (Nat.sqrt 697)+1=27 ∧
    27^2=(697:ℕ)*1^2+2*4^2 ∧ (27:ℕ).Coprime 1 ∧ (26+26)/21=(2:ℕ) := by decide +kernel

end PrimeFactors.TargetNormConvergents
