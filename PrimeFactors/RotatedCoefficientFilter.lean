import PrimeFactors.CircularCoefficientFilter
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Cancelling coefficients on a rotated circle

Taking the real part of the root-of-unity filter introduces a cosine at each
surviving exponent. A rotation can eliminate a chosen collection of exponents
before normalization by the radius. We use real coefficients throughout.
-/

namespace PrimeFactors.RotatedCoefficientFilter

open Finset Complex
open CircularCoefficientFilter (retained)

private theorem phase (n N : ℕ) (θ : ℝ) :
    (exp (-((N : ℂ) * θ * I)) * exp ((θ : ℂ) * I) ^ n).re =
      Real.cos (((n : ℝ) - N) * θ) := by
  rw [← exp_nat_mul, ← exp_add]
  have arg : -((N : ℂ) * θ * I) + n * ((θ : ℂ) * I) =
      (((((n : ℝ) - N) * θ : ℝ) : ℂ) * I) := by push_cast; ring
  rw [arg, exp_re]
  simp

/-- The weighted real sum from M rotated samples. For a target N choose s
with M dividing N+s and divide by M*r^N. -/
theorem finite_filter {M : ℕ} {z : ℂ} (hz : IsPrimitiveRoot z M)
    (S : Finset ℕ) (a : ℕ → ℝ) (r θ : ℝ) (N s : ℕ) :
    (exp (-((N : ℂ) * θ * I)) *
      ∑ j ∈ range M, (z ^ j) ^ s *
        ∑ n ∈ S, (a n : ℂ) * (((r : ℂ) * exp ((θ : ℂ) * I)) * z ^ j) ^ n).re =
      (M : ℝ) * ∑ n ∈ S.filter (fun n => M ∣ n + s),
        (a n * r ^ n) * Real.cos (((n : ℝ) - N) * θ) := by
  rw [CircularCoefficientFilter.finite_filter hz]
  rw [mul_left_comm, ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
    Finset.mul_sum, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_pow]
  have regroup : exp (-((N : ℂ) * θ * I)) *
      ((a n : ℂ) * ((r : ℂ) ^ n * exp ((θ : ℂ) * I) ^ n)) =
      ((a n * r ^ n : ℝ) : ℂ) * (exp (-((N : ℂ) * θ * I)) * exp ((θ : ℂ) * I) ^ n) := by
    push_cast
    ring
  rw [regroup, Complex.re_ofReal_mul, phase]

noncomputable def angle (M v : ℕ) : ℝ := Real.pi / (2 * (2 : ℝ) ^ v * M)

/-- Precisely the odd multiples of 2^v have zero cosine at this rotation. -/
theorem cancellation_iff {M : ℕ} (mp : 0 < M) (j v : ℕ) :
    Real.cos ((j : ℝ) * M * angle M v) = 0 ↔
      ∃ k : ℤ, (j : ℤ) = (2 * k + 1) * 2 ^ v := by
  rw [Real.cos_eq_zero_iff]
  apply exists_congr
  intro k
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast mp.ne'
  let scale := Real.pi / (2 * (2 : ℝ) ^ v)
  have positive : 0 < scale := by dsimp [scale]; positivity
  have lhs : (j : ℝ) * M * angle M v = j * scale := by
    dsimp [angle, scale]
    field_simp
    ring
  have rhs : (2 * (k : ℝ) + 1) * Real.pi / 2 = ((2 * k + 1) * (2 : ℝ) ^ v) * scale := by
    dsimp [scale]
    field_simp
    ring
  rw [lhs, rhs, mul_left_inj' positive.ne']
  norm_cast

theorem first_earlier {M : ℕ} (mp : 0 < M) :
    Real.cos ((M : ℝ) * angle M 0) = 0 := by
  simpa using (cancellation_iff mp 1 0).mpr ⟨0, by norm_num⟩

/-- The fourth step is the only earlier one with nonzero divisor sum at 323. -/
theorem support323 :
    (Icc 1 7).filter (fun j => retained 3 (323 - j * 42) ≠ 0) = {4} := by decide +kernel

theorem earlier323 {j : ℕ} (lo : 1 ≤ j) (hi : j ≤ 7) :
    (retained 3 (323 - j * 42) : ℝ) * Real.cos ((j : ℝ) * 42 * angle 42 2) = 0 := by
  by_cases zero : retained 3 (323 - j * 42) = 0
  · simp [zero]
  have mem : j ∈ (Icc 1 7).filter (fun t => retained 3 (323 - t * 42) ≠ 0) := mem_filter.mpr ⟨mem_Icc.mpr ⟨lo, hi⟩, zero⟩
  rw [support323, mem_singleton] at mem
  subst j
  apply mul_eq_zero_of_right
  simpa using (cancellation_iff (by decide : 0 < 42) 4 2).mpr ⟨0, by norm_num⟩

/-- Independent primality and product checks for every recovered sum in the panel. -/
theorem panel_factors :
    [(323, 17, 19), (391, 17, 23), (493, 17, 29), (527, 17, 31), (437, 19, 23), (551, 19, 29)].all
      (fun (n, p, q) => decide (Nat.Prime p ∧ Nat.Prime q ∧ p * q = n)) = true := by decide +kernel

end PrimeFactors.RotatedCoefficientFilter
