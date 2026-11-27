import PrimeFactors.FareyWrap
import Mathlib.NumberTheory.Harmonic.Bounds

/-! A finite upper bound on the sum over scale products uv ≤ L and common
multipliers d ≤ H. The bound includes every positive integer u and v. -/
namespace PrimeFactors.SquareScaleHarmonicBound

open Finset

noncomputable def weight (H L : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 H, ∑ u ∈ Icc 1 L, ∑ v ∈ Icc 1 (L/u),
    (H:ℝ)/((d:ℝ)*Real.sqrt ((u:ℝ)*(v:ℝ)))

private theorem sqrt_sum (m : ℕ) : ∑ v ∈ Icc 1 m, 1/Real.sqrt (v:ℝ) ≤ 2*Real.sqrt m := by
  have idx : ∑ v ∈ Icc 1 m, 1/Real.sqrt (v:ℝ) =
      ∑ i ∈ range m, 1/Real.sqrt ((i:ℝ)+1) := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [sum_Icc_succ_top (by omega : 1≤m+1),sum_range_succ,ih,Nat.cast_succ]
  exact idx.trans_le (FareyWrap.reciprocal_sqrt_sum m)

private theorem reciprocal (n : ℕ) : ∑ u ∈ Icc 1 n, 1/(u:ℝ) = (harmonic n : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

private theorem row (L u : ℕ) :
    ∑ v ∈ Icc 1 (L/u), 1/Real.sqrt ((u:ℝ)*(v:ℝ)) ≤ (2*Real.sqrt L)*(1/(u:ℝ)) := by
  have floor : ((L/u:ℕ):ℝ) ≤ (L:ℝ)/(u:ℝ) := Nat.cast_div_le
  have limit := Real.sqrt_le_sqrt floor
  rw [Real.sqrt_div (Nat.cast_nonneg L)] at limit
  calc
    _ = (1/Real.sqrt (u:ℝ))*∑ v ∈ Icc 1 (L/u), 1/Real.sqrt (v:ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro v _
      simp only [Real.sqrt_mul (Nat.cast_nonneg u),one_div,mul_inv_rev]
      ring
    _ ≤ (1/Real.sqrt (u:ℝ))*(2*(Real.sqrt L / Real.sqrt u)) :=
      mul_le_mul_of_nonneg_left ((sqrt_sum _).trans (mul_le_mul_of_nonneg_left limit (by norm_num))) (by positivity)
    _ = _ := by
      conv_rhs => rw [←Real.mul_self_sqrt (Nat.cast_nonneg u)]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

/-- The analytic estimate separates the two independent harmonic sums. -/
theorem harmonic_bound (H L : ℕ) : weight H L ≤
    2*(H:ℝ)*Real.sqrt L*(harmonic H:ℝ)*(harmonic L:ℝ) := by
  have outer : ∑ d ∈ Icc 1 H, (H:ℝ)/d = (H:ℝ)*(harmonic H:ℝ) := by
    rw [←reciprocal,mul_sum]
    simp only [mul_one_div]
  unfold weight
  calc
    _ ≤ ∑ d ∈ Icc 1 H, ((H:ℝ)/d)*∑ u ∈ Icc 1 L, (2*Real.sqrt L)*(1/(u:ℝ)) := by
      apply sum_le_sum
      intro d _
      rw [mul_sum]
      apply sum_le_sum
      intro u _
      calc
        _ = ((H:ℝ)/d)*∑ v ∈ Icc 1 (L/u), 1/Real.sqrt ((u:ℝ)*(v:ℝ)) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro v _
          simp only [div_eq_mul_inv,mul_inv_rev]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (row L u) (by positivity)
    _ = _ := by
      rw [←sum_mul,←mul_sum,reciprocal,outer]
      ring

private theorem harmonic_nonneg (m : ℕ) : 0≤(harmonic m:ℝ) := by rw [←reciprocal]; positivity

theorem log_bound (H L : ℕ) : weight H L ≤
    2*(H:ℝ)*Real.sqrt L*(1+Real.log H)*(1+Real.log L) := by
  have pair := mul_le_mul (harmonic_le_one_add_log H) (harmonic_le_one_add_log L)
    (harmonic_nonneg L) ((harmonic_nonneg H).trans (harmonic_le_one_add_log H))
  apply (harmonic_bound H L).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left pair
    (show 0 ≤ 2*(H:ℝ)*Real.sqrt L by positivity)

private theorem power_harmonic (k : ℕ) : (harmonic (2^k):ℝ) ≤ 1+(k:ℝ) := by
  have bound := harmonic_le_one_add_log (2^k)
  rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at bound
  have two : Real.log 2 ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  linarith only [bound,mul_le_mul_of_nonneg_left two (Nat.cast_nonneg k)]

set_option exponentiation.threshold 4096 in
/-- Finite bound at the full prime height and the proposed scale cutoff. -/
theorem full_width : weight (2^1024) (2^40) ≤ 2*(2:ℝ)^1024*(2:ℝ)^20*1025*41 := by
  have h : (harmonic (2^1024):ℝ) ≤ 1025 := (power_harmonic 1024).trans_eq (by norm_num)
  have l : (harmonic (2^40):ℝ) ≤ 41 := (power_harmonic 40).trans_eq (by norm_num)
  have rt : Real.sqrt (((2^40:ℕ):ℝ)) = (2:ℝ)^20 := by
    rw [show (2^40:ℕ)=(2^20)^2 by decide +kernel,Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg _),
      Nat.cast_pow,Nat.cast_ofNat]
  have bound := harmonic_bound (2^1024) (2^40)
  rw [rt,Nat.cast_pow,Nat.cast_ofNat] at bound
  apply bound.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul h l (harmonic_nonneg _) (by norm_num)) (show 0≤2*(2:ℝ)^1024*(2:ℝ)^20 by positivity)

/-- Dyadic height and an even exponent in the scale budget give an integral square root. -/
theorem dyadic_width (h b : ℕ) : weight (2^h) (2^(2*b)) ≤
    2*(2:ℝ)^h*(2:ℝ)^b*((h:ℝ)+1)*(2*(b:ℝ)+1) := by
  have hcap : (harmonic (2^h):ℝ) ≤ (h:ℝ)+1 := by
    simpa only [add_comm] using power_harmonic h
  have bcap : (harmonic (2^(2*b)):ℝ) ≤ 2*(b:ℝ)+1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, add_comm] using power_harmonic (2*b)
  have rt : Real.sqrt ((2:ℝ)^(2*b)) = (2:ℝ)^b := by
    rw [Nat.mul_comm 2 b, pow_mul, Real.sqrt_sq (by positivity)]
  have bound := harmonic_bound (2^h) (2^(2*b))
  simp only [Nat.cast_pow, Nat.cast_ofNat, rt] at bound
  apply bound.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul hcap bcap (harmonic_nonneg _) (by positivity))
    (show 0 ≤ 2*(2:ℝ)^h*(2:ℝ)^b by positivity)

end PrimeFactors.SquareScaleHarmonicBound
