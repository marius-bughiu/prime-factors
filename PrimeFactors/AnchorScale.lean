import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- Multiplying a phase after a failed calibration stays on the original half interval. -/
theorem salieAnchor_no_wrap {x z e step : ℝ} (hx : 0 ≤ x) (he : 0 ≤ step)
    (err : |z-x| ≤ e) (small : z < 3*e) (budget : step*e ≤ 17/256) :
    0 ≤ step*x ∧ step*x < 1/2 := by
  have h := (abs_le.mp err).1
  have xx : x < 4*e := by linarith
  have upper := mul_le_mul_of_nonneg_left xx.le he
  exact ⟨mul_nonneg he hx, by linarith⟩

/-- A positive measured phase below a quarter admits a dyadic rescaling into an eighth to a quarter. -/
theorem salieAnchor_dyadic {z : ℝ} (pos : 0 < z) (upper : z ≤ 1/4) :
    ∃ j : ℕ, 1/8 < 2^j*z ∧ 2^j*z ≤ 1/4 := by
  have den : 0 < 4*z := by positivity
  have size : 1 ≤ 1/(4*z) := (le_div_iff₀ den).mpr (by linarith)
  obtain ⟨j, lo, hi⟩ := exists_nat_pow_near size (by norm_num : (1:ℝ) < 2)
  have lower := (div_lt_iff₀ den).mp hi
  have higher := (le_div_iff₀ den).mp lo
  rw [pow_succ] at lower
  exact ⟨j, by linarith, by linarith⟩

/-- The calibrated orientation has enough room for both the sign and nearest-integer test. -/
theorem salieAnchor_central {x z e c : ℝ} (cc : 0 ≤ c) (err : |z-x| ≤ e)
    (resolved : 3*e ≤ z) (lower : 1/8 ≤ c*z) (upper : c*z ≤ 1/4) :
    1/12 ≤ c*x ∧ c*x ≤ 3/8 := by
  obtain ⟨lo, hi⟩ := abs_le.mp err
  have left := mul_le_mul_of_nonneg_left (show 2*z ≤ 3*x by linarith) cc
  have right := mul_le_mul_of_nonneg_left (show 3*x ≤ 4*z by linarith) cc
  constructor <;> linarith

/-- The oriented residual identifies the common positive phase, even if each sample is reflected. -/
theorem salieAnchor_round {x w : ℝ} {k : ℤ} (lo : 1/12 ≤ x) (hi : x ≤ 3/8)
    (sign : Bool) (err : |w - ((k : ℝ) + if sign then x else -x)| ≤ 17/256) :
    |w-(k : ℝ)| < 1/2 ∧ ((k : ℝ) < w ↔ sign = true) := by
  cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte, iff_false, iff_true, not_lt] at * <;>
    obtain ⟨a, b⟩ := abs_le.mp err <;> constructor <;> first | (apply abs_lt.mpr; constructor <;> linarith) | linarith

/-- Exact directed residues for the two signs in the modular lift. -/
theorem salieAnchor_signed {m y k N A : ℤ} (sign : Bool)
    (lift : m*y = k*N + if sign then A else -A) :
    A ≡ (if sign then -(k*N) else k*N) [ZMOD m] := by
  cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;>
    apply Int.modEq_iff_dvd.mpr
  · exact ⟨y, by linarith⟩
  · exact ⟨-y, by rw [mul_neg]; linarith⟩

/-- Two endpoints based on the same measured phase differ by at most the certified width. -/
theorem salieAnchor_interval {lo hi S N z e : ℝ} (hlo : (z-e)*N ≤ S*lo)
    (hhi : S*hi ≤ (z+e)*N) : S*(hi-lo) ≤ 2*e*N := by linarith

/-- Replacing each failed calibration by a public multiplier at least as large as the
removed prime maintains the product bound needed by the small-root algorithm. -/
theorem salieAnchor_budget {required omitted kept step : ℕ} {failures : ℕ}
    (enough : required ≤ omitted*kept) (perProbe : omitted ≤ step^failures) :
    required ≤ kept * step^failures := by
  rw [Nat.mul_comm kept]
  exact enough.trans (Nat.mul_le_mul_right _ perProbe)

/-- The smallest usable listed prime already gives enough product size when raised to the 42nd power. -/
example : 2^1007 < (16776547 : ℕ)^42 ∧ 16777213 < (2 : ℕ)^24 := by decide +kernel

end PrimeFactors
