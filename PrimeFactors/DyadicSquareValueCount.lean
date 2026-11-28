import Mathlib.Data.Real.Basic
import PrimeFactors.PrimePowerCount
import PrimeFactors.PrimePowerSumFilter

/-! Distinct square values, including zero, modulo powers of two. -/

namespace PrimeFactors.DyadicSquareValueCount

open private PrimeFactors.digit_val PrimeFactors.count_digits from PrimeFactors.PrimePowerCount

noncomputable section

/-- Count each value once, regardless of its number of roots. -/
def count (j : ℕ) : ℕ := Nat.card {x : ZMod (2^j) // IsSquare x}

private theorem image_count (j : ℕ) :
    count j = (Finset.univ.image (fun x : ZMod (2^j) => x*x)).card := by
  classical
  rw [count, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  exact exists_congr fun _ => eq_comm

theorem at_two : count 1 = 2 := by rw [image_count]; decide +kernel

theorem at_four : count 2 = 2 := by rw [image_count]; decide +kernel

private theorem square_mod_eight (n : ℕ) :
    (n*n)%8 = 0 ∨ (n*n)%8 = 1 ∨ (n*n)%8 = 4 := by
  rw [Nat.mul_mod]
  have h := Nat.mod_lt n (by decide : 0<8)
  generalize n%8 = v at *
  interval_cases v <;> decide

private theorem odd_square_class (k : ℕ) (x : ZMod (2^(k+3))) :
    firstPrimeDigit 2 (k+2) x = 1 ∧ IsSquare x ↔ x.val%8=1 := by
  have digit : firstPrimeDigit 2 (k+2) x = 1 ↔ x.val%2=1 := by
    rw [← (ZMod.val_injective 2).eq_iff, PrimeFactors.digit_val]
    rfl
  rw [digit]
  constructor
  · rintro ⟨odd, y, hy⟩
    have div : 8 ∣ 2^(k+3) := by rw [pow_add]; exact dvd_mul_left ..
    have shape := square_mod_eight y.val
    have eq : x.val%8=(y.val*y.val)%8 := by rw [hy,ZMod.val_mul,Nat.mod_mod_of_dvd _ div]
    omega
  · intro low
    obtain ⟨r,h⟩ := PrimePowerSumFilter.normalizing_unit low (k+3)
    exact ⟨by omega, r, by simpa only [ZMod.natCast_zmod_val] using h.symm⟩

private noncomputable def oneClassEquiv (k : ℕ) :
    Fin (2^k) ≃ {x : ZMod (2^(k+3)) // x.val%8=1} where
  toFun i := ⟨((8*i.val+1 : ℕ) : ZMod (2^(k+3))), by
    have lt : 8*i.val+1 < 2^(k+3) := by rw [pow_add]; have := i.isLt; omega
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt lt]; omega⟩
  invFun x := ⟨x.val.val/8, by
    have lt := x.val.val_lt
    have expand : 2^(k+3) = 2^k*8 := pow_add ..
    omega⟩
  left_inv i := by
    apply Fin.ext
    have lt : 8*i.val+1 < 2^(k+3) := by rw [pow_add]; have := i.isLt; omega
    change (((8*(i:ℕ)+1 : ℕ) : ZMod (2^(k+3))).val)/8 = i.val
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt lt]; omega
  right_inv x := by
    apply Subtype.ext
    change ((8*(x.val.val/8)+1 : ℕ) : ZMod (2^(k+3))) = x.val
    rw [show 8*(x.val.val/8)+1=x.val.val by have := x.property; omega, ZMod.natCast_zmod_val]

private theorem step (k : ℕ) : count (k+3) = count (k+1) + 2^k := by
  classical
  have odd : Nat.card {x : ZMod (2^(k+3)) //
      firstPrimeDigit 2 (k+2) x = 1 ∧ IsSquare x} = 2^k :=
    (Nat.card_congr (Equiv.subtypeEquivRight (odd_square_class k))).trans
      ((Nat.card_congr (oneClassEquiv k).symm).trans (by simp))
  unfold count
  rw [PrimeFactors.count_digits (k+2) IsSquare]
  change (∑ r : Fin 2, _) = _
  rw [Fin.sum_univ_two, card_squares_zero_digit (p:=2) (k+1),odd]

/-- The odd squares at level j+2 form one residue class modulo eight.
The even squares correspond to all square values at level j. -/
theorem recurrence {j : ℕ} (positive : 1≤j) :
    count (j+2) = count j + 2^(j-1) := by
  obtain ⟨k,rfl⟩ : ∃ k, j=k+1 := ⟨j-1,by omega⟩
  simpa using step k

theorem six_mul {j : ℕ} (positive : 1≤j) :
    6*count j = 2^j + (if j%2=0 then 8 else 10) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    match j with
    | 0 => omega
    | 1 => norm_num [at_two]
    | 2 => norm_num [at_four]
    | k+3 =>
      have prev := ih (k+1) (by omega) (by omega)
      rw [step, show (k+3)%2=(k+1)%2 by omega, pow_add]
      rw [pow_succ] at prev
      omega

theorem closed {j : ℕ} (positive : 1≤j) :
    count j = (2^j + (if j%2=0 then 8 else 10))/6 := by
  have := six_mul positive
  omega

/-- The error in the limiting density is positive and at most five thirds
divided by the modulus. -/
theorem density {j : ℕ} (positive : 1≤j) :
    1/6 < (count j:ℝ)/(2:ℝ)^j ∧ (count j:ℝ)/(2:ℝ)^j ≤ 1/6+(5/3)/(2:ℝ)^j := by
  have h := six_mul positive
  have powpos : 0 < (2:ℝ)^j := by positivity
  constructor
  · apply (lt_div_iff₀ powpos).mpr
    have bound : (2:ℝ)^j < 6*(count j:ℝ) := by
      exact_mod_cast (show 2^j < 6*count j by split at h <;> omega)
    linarith
  · apply (div_le_iff₀ powpos).mpr
    rw [add_mul,div_mul_cancel₀ _ powpos.ne']
    have : 6*(count j:ℝ) ≤ (2:ℝ)^j+10 := by
      exact_mod_cast (show 6*count j ≤ 2^j+10 by split at h <;> omega)
    linarith

theorem at_256 : count 8=44 := by rw [closed (by decide)]; decide

end

end PrimeFactors.DyadicSquareValueCount
