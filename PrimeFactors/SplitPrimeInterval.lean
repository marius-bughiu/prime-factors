import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Finite interval arithmetic for ordinary and split prime counts. The
endpoint estimates and the comparison between a normalized Chebyshev increment
and the weighted prime sum are hypotheses. The arithmetic is independent of the
source of either estimate. -/

namespace PrimeFactors.SplitPrimeInterval

open Finset

set_option exponentiation.threshold 2048

/-- The coarse logarithm bounds hold throughout the 1024-bit factor range. -/
theorem log_1024 {p : ℕ} (low : 2^1023 ≤ p) (high : p ≤ 2^1024) :
    708 ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 710 := by
  have lo : (2 : ℝ)^1023 ≤ p := by exact_mod_cast low
  have hi : (p : ℝ) ≤ (2 : ℝ)^1024 := by exact_mod_cast high
  have a := Real.log_le_log (show 0 < (2 : ℝ)^1023 by positivity) lo
  have b := Real.log_le_log (lt_of_lt_of_le (by positivity) lo) hi
  rw [Real.log_pow] at a b
  norm_num1 at a b
  constructor
  · linarith only [a, Real.log_two_gt_d9]
  · linarith only [b, Real.log_two_lt_d9]

/-- Bounds on each prime's logarithm sandwich the weighted count. This works
with any finite selection of primes; no independence assumption enters. -/
theorem log_bounds (s : Finset ℕ) {a b : ℝ}
    (low : ∀ p ∈ s, a ≤ Real.log (p : ℝ)) (high : ∀ p ∈ s, Real.log (p : ℝ) ≤ b) :
    a * s.card ≤ ∑ p ∈ s, Real.log (p : ℝ) ∧
      (∑ p ∈ s, Real.log (p : ℝ)) ≤ b * s.card := by
  constructor
  · simpa only [sum_const, nsmul_eq_mul, mul_comm a] using sum_le_sum low
  · simpa only [sum_const, nsmul_eq_mul, mul_comm b] using sum_le_sum high

/-- Endpoint values use the normalization with main term x/m. The nonnegative
remainder accounts for all contributions to the increment other than the
weighted prime count θ. Endpoint and remainder errors share the budget E. -/
theorem weighted_interval {m H : ℕ} {lo hi ψlo ψhi θ a b E₀ E₁ R E : ℝ}
    (mpos : 0 < m) (left : |ψlo - lo/m| ≤ E₀) (right : |ψhi - hi/m| ≤ E₁)
    (rem : 0 ≤ ψhi-ψlo-θ) (rem_bound : ψhi-ψlo-θ ≤ R)
    (budget : E₀+E₁+R ≤ E) (low : a*H ≤ θ) (high : θ ≤ b*H) :
    (m : ℝ)*a*H ≤ (hi-lo) + m*E ∧ (hi-lo) ≤ (m : ℝ)*b*H + m*E := by
  have mpos' : (0 : ℝ) < m := by exact_mod_cast mpos
  have wl := abs_le.mp left
  have wr := abs_le.mp right
  have width : (m : ℝ) * (hi/m - lo/m) = hi-lo := by field_simp
  constructor
  · have h : a*H ≤ (hi/m-lo/m) + E := by linarith
    have hs := mul_le_mul_of_nonneg_left h mpos'.le
    rwa [mul_add, width, ← mul_assoc] at hs
  · have h : hi/m - lo/m ≤ b*H + E := by linarith
    have hs := mul_le_mul_of_nonneg_left h mpos'.le
    rwa [width, mul_add, ← mul_assoc] at hs

/-- The two endpoint coefficients and the omitted weighted terms fit in
the stated total error, even at the maximum family size. -/
theorem coefficient_budget :
    (2*(121*(512*355)+21007)+710)*2^512 ≤ (2 : ℕ)^538 := by decide +kernel

/-- A common bound on each normalized endpoint discrepancy and an upper bound
on the remainder suffice for the error premise of `weighted_interval`. -/
theorem normalized_error {k : ℕ} {E₀ E₁ R : ℝ} (bits : k ≤ 512)
    (left : E₀ ≤ (121*(k*355)+21007 : ℝ)*2^512)
    (right : E₁ ≤ (121*(k*355)+21007 : ℝ)*2^512) (rem : R ≤ 710*2^512) :
    E₀+E₁+R ≤ 2^538 := by
  have kbound : (k : ℝ) ≤ 512 := by exact_mod_cast bits
  have cap : (2*(121*(512*355)+21007)+710)*2^512 ≤ (2 : ℝ)^538 := by
    exact_mod_cast coefficient_budget
  norm_num1 at left right rem cap ⊢
  linarith

/-- For m=65536 the interval hypotheses control the actual ratio of the two
integer prime counts, even at the minimum permitted width. -/
theorem counts {W : ℝ} {H P : ℕ} (width : (2 : ℝ)^1020 ≤ W)
    (hBelow : (65536 : ℝ)*708*H ≤ W+65536*2^538)
    (hAbove : W ≤ (65536 : ℝ)*710*H+65536*2^538)
    (pBelow : (708 : ℝ)*P ≤ W+2^538) (pAbove : W ≤ (710 : ℝ)*P+2^538) :
    65000*H ≤ P ∧ P ≤ 66000*H ∧ 2^994 ≤ H := by
  norm_num1 at width hBelow hAbove pBelow pAbove
  refine ⟨?_,?_,?_⟩
  · have h : (65000 : ℝ)*H ≤ P := by linarith
    exact_mod_cast h
  · have h : (P : ℝ) ≤ 66000*H := by linarith
    exact_mod_cast h
  · have h : (2 : ℝ)^994 ≤ H := by norm_num1; linarith
    exact_mod_cast h

/-- For degrees 2^k with k≤480, the normalized remainder is small enough
to preserve this uniform lower bound for a width of at least 2^1020. -/
theorem lower_many {W : ℝ} {k H : ℕ} (bits : k ≤ 480) (width : (2 : ℝ)^1020 ≤ W)
    (count : W ≤ (2 : ℝ)^k*710*H+(2 : ℝ)^k*2^538) :
    2^(1010-k) ≤ H := by
  have err : (2 : ℝ)^k * 2^538 ≤ 2^1018 := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have enough : (710 : ℝ)*2^1010+2^1018 ≤ 2^1020 := by norm_num1
  have ex : k+(1010-k)=1010 := by omega
  have product : (2 : ℝ)^k*710*2^(1010-k) = 710*2^1010 := by
    rw [mul_comm ((2 : ℝ)^k) 710, mul_assoc, ← pow_add, ex]
  have h : (2 : ℝ)^k*710*(2 : ℝ)^(1010-k) ≤ (2 : ℝ)^k*710*H := by linarith
  have final := le_of_mul_le_mul_left h (by positivity)
  exact_mod_cast final

/-- Once k≥488 the normalized remainder dominates the possible increase
in the upper bound from the main term, for widths at most 2^1024. -/
theorem upper_many {W : ℝ} {k H : ℕ} (bits : 488 ≤ k) (width : W ≤ (2 : ℝ)^1024)
    (count : (2 : ℝ)^k*708*H ≤ W+(2 : ℝ)^k*2^538) :
    H ≤ 2^529 := by
  have d : (2 : ℝ)^1024 ≤ 2^k * 2^536 := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have maxWidth : (2 : ℝ)^536 + 2^538 ≤ 708*2^529 := by norm_num1
  have h : (2 : ℝ)^k*(708*H) ≤ 2^k*(2^536+2^538) := by
    rw [← mul_assoc, mul_add]
    linarith
  have small := le_of_mul_le_mul_left h (by positivity)
  have final : (H : ℝ) ≤ 2^529 := by linarith only [small, maxWidth]
  exact_mod_cast final

theorem lower_400 {W : ℝ} {H : ℕ} (width : (2 : ℝ)^1020 ≤ W)
    (count : W ≤ (2 : ℝ)^400*710*H+(2 : ℝ)^400*2^538) : 2^610 ≤ H :=
  lower_many (k := 400) (by decide) width count

theorem upper_512 {W : ℝ} {H : ℕ} (width : W ≤ (2 : ℝ)^1024)
    (count : (2 : ℝ)^512*708*H ≤ W+(2 : ℝ)^512*2^538) : H ≤ 2^529 :=
  upper_many (k := 512) (by decide) width count

end PrimeFactors.SplitPrimeInterval
