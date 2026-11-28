import PrimeFactors.QuarticLocalClassification
import Mathlib.NumberTheory.SumTwoSquares

/-! The quartic local tests at all finite moduli reduce to a residue modulo
sixteen and a single square-existence question at the original odd input. -/

namespace PrimeFactors.QuarticLocalSquareCriterion

open QuarticLocalClassification (Tests)

private theorem square_of_support {n : ℕ} (support : ∀ p, p.Prime → p∣n → p%4=1) :
    IsSquare (-1 : ZMod n) := by
  induction n using Nat.recOnPrimeCoprime with
  | h0 => exact False.elim (by have := support 2 Nat.prime_two (dvd_zero _); omega)
  | hp p e prime =>
    cases e with
    | zero => rw [pow_zero]; exact ⟨0,Subsingleton.elim ..⟩
    | succ k =>
      letI : Fact p.Prime := ⟨prime⟩
      have split := support p prime (dvd_pow_self p (Nat.succ_ne_zero k))
      have unit : ((-1 : ℤ) : ZMod p)≠0 := by simp
      have lift := isSquare_primePow_iff_of_unit (by omega : p≠2) (-1) unit k
      simpa only [Int.cast_neg,Int.cast_one] using
        lift.mpr (by simpa only [Int.cast_neg,Int.cast_one] using ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p%4≠3))
  | h a b _ _ cop left right =>
    exact ZMod.isSquare_neg_one_mul cop
      (left fun p prime div => support p prime (dvd_mul_of_dvd_left div b))
      (right fun p prime div => support p prime (dvd_mul_of_dvd_right div a))

/-- For odd inputs, including repeated prime factors, -1 is a square exactly
when every prime divisor is 1 modulo four. -/
theorem square_iff {n : ℕ} (odd : Odd n) :
    IsSquare (-1 : ZMod n) ↔ ∀ p, p.Prime → p∣n → p%4=1 := by
  refine ⟨?_,square_of_support⟩
  intro square p prime div
  have other : p≠2 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr div)
  have parity := prime.eq_two_or_odd.resolve_left other
  have residue := prime.mod_four_ne_three_of_dvd_isSquare_neg_one div square
  omega

/-- The input N determines both predicates. The second predicate asks only
for the existence of a square root modulo N. -/
theorem tests_iff {n : ℕ} (odd : Odd n) : Tests n ↔
    (n%16=1 ∨ n%16=5) ∧ IsSquare (-1 : ZMod n) := by
  rw [QuarticLocalClassification.all_iff odd,square_iff odd]

/-- Each condition can hold when the other fails. 2257 satisfies both
even though it has no integer representation at denominator one. -/
theorem examples : (438:ZMod 2257)^2 = -1 ∧ (2257:ℕ)%16=1 ∧
    (401:ZMod 2173)^2 = -1 ∧ (2173:ℕ)%16=13 ∧
    (2773:ℕ)%16=5 ∧ ¬IsSquare (-1:ZMod 2773) := by
  refine ⟨by decide +kernel,by decide,by decide +kernel,by decide,by decide,?_⟩
  intro root
  have bad := (square_iff (by decide : Odd 2773)).mp root 47 (by decide) (by decide)
  exact (by decide : ¬(47:ℕ)%4=1) bad

end PrimeFactors.QuarticLocalSquareCriterion
