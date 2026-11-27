import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-! The quadratic character on units induced to a modulus divisible by
every prime in the discriminant. A negative prime value is an obstruction
for the original discriminant even when it contains an unknown square factor. -/
namespace PrimeFactors.DiscriminantJacobiCharacter

def modulus (d : ℕ) : ℕ := 120*d

def sign (d a : ℕ) : ℤ := if a.Coprime (modulus d) then jacobiSym d a else 0

theorem sign_of_unit {d a : ℕ} (unit : a.Coprime (modulus d)) :
    sign d a=jacobiSym d a := if_pos unit

private theorem odd_unit {d a : ℕ} (unit : a.Coprime (modulus d)) : Odd a := by
  have h := Nat.prime_two.coprime_iff_not_dvd.mp
    (unit.symm.of_dvd_left (show 2 ∣ modulus d from ⟨60*d,by unfold modulus; ring⟩))
  exact Nat.odd_iff.mpr (by omega)

theorem sign_mul (d a b : ℕ) : sign d (a*b)=sign d a*sign d b := by
  by_cases ha : a.Coprime (modulus d)
  · by_cases hb : b.Coprime (modulus d)
    · rw [sign_of_unit (Nat.coprime_mul_iff_left.mpr ⟨ha,hb⟩),sign_of_unit ha,sign_of_unit hb]
      exact jacobiSym.mul_right' _ (odd_unit ha).pos.ne' (odd_unit hb).pos.ne'
    · have bad : ¬(a*b).Coprime (modulus d) := fun h => hb (Nat.coprime_mul_iff_left.mp h).2
      rw [show sign d (a*b)=0 from if_neg bad,show sign d b=0 from if_neg hb,mul_zero]
  · have bad : ¬(a*b).Coprime (modulus d) := fun h => ha (Nat.coprime_mul_iff_left.mp h).1
    rw [show sign d (a*b)=0 from if_neg bad,show sign d a=0 from if_neg ha,zero_mul]

theorem sign_period (d a : ℕ) : sign d (a%modulus d)=sign d a := by
  have cop : (a%modulus d).Coprime (modulus d) ↔ a.Coprime (modulus d) := by
    unfold Nat.Coprime
    rw [← Nat.gcd_rec,Nat.gcd_comm]
  by_cases h : a.Coprime (modulus d)
  · rw [sign,if_pos (cop.mpr h),sign,if_pos h]
    have small : 4*d ∣ modulus d := ⟨30,by unfold modulus; ring⟩
    rw [jacobiSym.mod_right' d (odd_unit (cop.mpr h)),Nat.mod_mod_of_dvd _ small]
    exact (jacobiSym.mod_right' d (odd_unit h)).symm
  · simp [sign,cop,h]

theorem support {d a : ℕ} : sign d a ≠ 0 ↔ a.Coprime (modulus d) := by
  by_cases h : a.Coprime (modulus d)
  · have cd := h.symm.of_dvd_left (show d ∣ modulus d from dvd_mul_left ..)
    have nz : jacobiSym (d:ℤ) a ≠ 0 := jacobiSym.ne_zero (by simpa using cd.gcd_eq_one)
    exact ⟨fun _ => h,fun _ => sign_of_unit h ▸ nz⟩
  · simp [sign,h]

theorem values (d a : ℕ) : sign d a=0 ∨ sign d a=1 ∨ sign d a= -1 := by
  by_cases h : a.Coprime (modulus d)
  · rw [sign_of_unit h]
    exact jacobiSym.trichotomy (d:ℤ) a
  · simp [sign,h]

noncomputable def realSign (d : ℕ) : ℕ →* ℝ where
  toFun a := (sign d a : ℝ)
  map_one' := by rw [sign_of_unit (Nat.coprime_one_left _),jacobiSym.one_right,Int.cast_one]
  map_mul' a b := by simp only [sign_mul,Int.cast_mul]

theorem real_support (d a : ℕ) : realSign d a ≠ 0 ↔ a.Coprime (modulus d) := by
  change (sign d a:ℝ) ≠ 0 ↔ _
  rw [Int.cast_ne_zero]
  exact support

theorem real_values (d a : ℕ) : realSign d a= -1 ∨ realSign d a=0 ∨ realSign d a=1 := by
  change (sign d a:ℝ)= -1 ∨ (sign d a:ℝ)=0 ∨ (sign d a:ℝ)=1
  rcases values d a with h|h|h <;> norm_num [h]

/-- A negative input, however large, gives a negative prime inside one
period by complete multiplicativity of the denominator Jacobi symbol. -/
theorem negative_prime_in_period {d a : ℕ} (pos : 0 < d) (negative : sign d a= -1) :
    ∃ ℓ < modulus d, ℓ.Prime ∧ sign d ℓ= -1 := by
  have reduced := (sign_period d a).trans negative
  have unit := support.mp (show sign d (a%modulus d) ≠ 0 by omega)
  have nz : 0 < a%modulus d := by have := Nat.odd_iff.mp (odd_unit unit); omega
  obtain ⟨ℓ,prime,factor,bad⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one
    ((sign_of_unit unit).symm.trans reduced)
  exact ⟨ℓ,(Nat.le_of_dvd nz factor).trans_lt (Nat.mod_lt _ (by unfold modulus; omega)),
    prime,(sign_of_unit (unit.of_dvd_left factor)).trans bad⟩

/-- A Dirichlet character including all the excluded nonunits in its level. -/
noncomputable def character (d : ℕ) (pos : 0 < d) : DirichletCharacter ℤ (modulus d) := by
  letI : Fact (1 < modulus d) := ⟨by unfold modulus; omega⟩
  letI : NeZero (modulus d) := ⟨by unfold modulus; omega⟩
  exact {
    toFun := fun x => sign d x.val
    map_one' := by rw [ZMod.val_one]; simp [sign]
    map_mul' := by intro x y; rw [ZMod.val_mul,sign_period,sign_mul]
    map_nonunit' := by
      intro x hx
      by_contra h
      apply hx
      have unit := (ZMod.isUnit_iff_coprime x.val (modulus d)).mpr (support.mp h)
      rwa [ZMod.natCast_zmod_val] at unit }

theorem character_nat (d a : ℕ) (pos : 0 < d) :
    character d pos (a : ZMod (modulus d)) = sign d a := by
  change sign d (a : ZMod (modulus d)).val = _
  rw [ZMod.val_natCast,sign_period]

theorem nonprincipal_of_negative {d a : ℕ} (pos : 0 < d) (negative : sign d a= -1) :
    character d pos ≠ 1 := by
  have unit := support.mp (show sign d a ≠ 0 by omega)
  intro principal
  have evaluated := character_nat d a pos
  rw [principal,MulChar.one_apply ((ZMod.isUnit_iff_coprime a _).mpr unit),negative] at evaluated
  omega

/-- A negative character entry supplies an odd prime coprime to the whole
discriminant, with the original discriminant nonsquare at that prime. -/
theorem prime_obstruction {d ℓ : ℕ} (prime : ℓ.Prime) (negative : sign d ℓ= -1) :
    ℓ ≠ 2 ∧ ℓ.Coprime d ∧ ¬IsSquare ((d:ℕ):ZMod ℓ) := by
  letI : Fact ℓ.Prime := ⟨prime⟩
  have unit := support.mp (show sign d ℓ ≠ 0 by omega)
  have odd := odd_unit unit
  have c := unit.symm.of_dvd_left (show d ∣ modulus d from dvd_mul_left ..)
  have jac : jacobiSym (d:ℤ) ℓ= -1 := (sign_of_unit unit).symm.trans negative
  exact ⟨by have := Nat.odd_iff.mp odd; omega,c.symm,by
    simpa using ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp jac⟩

end PrimeFactors.DiscriminantJacobiCharacter
