import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

namespace PrimeFactors.PowerFactorScale

/-- A rank 2m+1 Taylor lattice at precision R^(2m) has diagonal
R^(2m), R^(2m-1), …, R, 1. The X-weights are X^m,…,1,…,X^m. -/
theorem determinant_exponents (m : ℕ) :
    (∑ j ∈ Finset.range (2*m+1), j) = m*(2*m+1) ∧
    2*(∑ j ∈ Finset.range (m+1), j) = m*(m+1) := by
  constructor
  · have h := Finset.sum_range_id_mul_two (2*m+1)
    rw [Nat.add_sub_cancel] at h
    apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
    calc _ = (2*m+1)*(2*m) := h
         _ = _ := by ring
  · have h := Finset.sum_range_id_mul_two (m+1)
    simpa [mul_comm] using h

/-- Squared integer form of the sufficient LLL bound for the search. The
external LLL theorem supplies the norm estimate; this theorem checks the
public scales with no floating-point arithmetic, even in high dimension. -/
theorem sufficient {m e q X : ℕ} (size : 2*m+1 ≤ 2^q) (coord : X^2 ≤ 2^2049)
    (budget : q*(2*m+1)+m*(2*m+1)+2049*(m*(m+1)) < e*(2*m*(2*m+1))) :
    (2*m+1)^(2*m+1) * 2^(m*(2*m+1)) * X^(2*(m*(m+1))) <
      (2^e)^(2*m*(2*m+1)) := by
  have h1 := Nat.pow_le_pow_left size (2*m+1)
  have h2 := Nat.pow_le_pow_left coord (m*(m+1))
  have h := Nat.mul_le_mul (Nat.mul_le_mul_right (2^(m*(2*m+1))) h1) h2
  rw [← pow_mul X] at h
  refine h.trans_lt ?_
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_mul]
  exact Nat.pow_lt_pow_right (by decide) budget

/-- Explicit exponents for every balanced 2048-bit odd input, ranging
from quadratic to degree 4096. The largest dimensions are only bounds. -/
theorem target_scales : ∀ entry ∈ ([(1,685,2),(2,616,3),(3,587,3),(4,571,4),
    (8,544,5),(32,521,7),(512,514,11),(2048,513,13)] : List (ℕ × ℕ × ℕ)),
    let m := entry.1
    let e := entry.2.1
    let q := entry.2.2
    2*m+1 ≤ 2^q ∧ q*(2*m+1)+m*(2*m+1)+2049*(m*(m+1)) < e*(2*m*(2*m+1)) := by
  decide +kernel

end PrimeFactors.PowerFactorScale
