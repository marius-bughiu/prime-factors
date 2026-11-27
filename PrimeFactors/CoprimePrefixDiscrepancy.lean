import PrimeFactors.NegativeCharacterPrimeCover
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Sqrt

/-! An elementary discrepancy bound for the number of positive integers
through X that are coprime to a fixed modulus. -/
namespace PrimeFactors.CoprimePrefixDiscrepancy

open ArithmeticFunction Finset NegativeCharacterPrimeCover
open scoped ArithmeticFunction

/-- Möbius inversion expresses the count as a sum of integer quotients. -/
theorem expansion (X : ℕ) {M : ℕ} (pos : 0 < M) :
    ((units M X).card : ℝ) = ∑ d ∈ M.divisors, (μ d : ℝ) * (X/d : ℕ) := by
  have indicator (n : ℕ) : (if n.Coprime M then (1:ℝ) else 0) =
      ∑ d ∈ M.divisors, if d ∣ n then (μ d : ℝ) else 0 := by
    have eq : M.divisors.filter (· ∣ n) = (n.gcd M).divisors := by
      ext d
      simp [Nat.mem_divisors, pos.ne', (Nat.gcd_pos_of_pos_right n pos).ne',
        Nat.dvd_gcd_iff, and_comm]
    rw [←sum_filter, eq]
    have inv := congrArg (fun f : ArithmeticFunction ℤ => f (n.gcd M)) coe_zeta_mul_moebius
    simp only [coe_zeta_mul_apply, one_apply] at inv
    by_cases h : n.gcd M = 1 <;> simp only [Nat.Coprime, h, if_true, if_false] at inv ⊢ <;>
      exact_mod_cast inv.symm
  calc
    _ = ∑ n ∈ Icc 1 X, if n.Coprime M then (1:ℝ) else 0 := by simp [units]
    _ = _ := by
      simp_rw [indicator]
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [←sum_filter, Nat.Icc_succ_left 0 X, sum_const, Nat.Ioc_filter_dvd_card_eq_div,
        nsmul_eq_mul, mul_comm]

private theorem density (X : ℕ) {M : ℕ} (pos : 0 < M) :
    (X : ℝ)*M.totient/M = ∑ d ∈ M.divisors, (μ d : ℝ) * ((X : ℝ)/d) := by
  have period : (units M M).card = M.totient := by
    simpa only [units, Nat.add_comm 1 M, Nat.Ico_succ_right, @Nat.coprime_comm M] using
      Nat.filter_coprime_Ico_eq_totient M 1
  rw [←period, expansion M pos, mul_sum, div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro d hd
  have dp : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have mp : (M:ℝ) ≠ 0 := by exact_mod_cast pos.ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) dp]
  field_simp
  ring

/-- Each rounded division costs at most one and each Möbius weight has
absolute value at most one. -/
theorem discrepancy_le_divisors (X : ℕ) {M : ℕ} (pos : 0 < M) :
    |((units M X).card : ℝ) - (X : ℝ)*M.totient/M| ≤ M.divisors.card := by
  rw [expansion X pos, density X pos, ←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ _d ∈ M.divisors, (1:ℝ) := by
      apply sum_le_sum
      intro d hd
      have dp := Nat.pos_of_mem_divisors hd
      have hi : (X:ℝ)/d < ((X/d : ℕ) : ℝ)+1 := by
        apply (div_lt_iff₀ (by exact_mod_cast dp : (0:ℝ)<d)).mpr
        exact_mod_cast (by simpa only [Nat.mul_comm d] using Nat.lt_mul_div_succ X dp)
      have floorError : |((X/d : ℕ):ℝ)-(X:ℝ)/d| ≤ 1 := by
        have lo := Nat.cast_div_le (α:=ℝ) (m:=X) (n:=d)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have mu : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n:=d))
      rw [←mul_sub, abs_mul]
      simpa using mul_le_mul mu floorError (abs_nonneg _) zero_le_one
    _ = _ := by simp

/-- A divisor or its complementary divisor lies at most at the square root. -/
theorem divisors_le_two_sqrt (M : ℕ) : M.divisors.card ≤ 2*M.sqrt := by
  let S := Icc 1 M.sqrt
  have cover : M.divisors ⊆ S ∪ S.image (M/·) := by
    intro d hd
    have dp := Nat.pos_of_mem_divisors hd
    obtain ⟨k, eq⟩ := Nat.dvd_of_mem_divisors hd
    have kp : 0 < k := by
      have nonzero := (Nat.mem_divisors.mp hd).2
      by_contra! h
      simp_all
    rcases le_total d k with low | high
    · apply mem_union_left
      exact mem_Icc.mpr ⟨dp, Nat.le_sqrt'.mpr (by rw [eq, pow_two]; exact Nat.mul_le_mul_left d low)⟩
    · apply mem_union_right
      refine mem_image.mpr ⟨k, mem_Icc.mpr ⟨kp, Nat.le_sqrt'.mpr ?_⟩, ?_⟩
      · rw [eq, pow_two]
        exact Nat.mul_le_mul_right k high
      · rw [eq, Nat.mul_div_cancel _ kp]
  have bound := (card_le_card cover).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left (card_image_le (s:=S) (f:=(M/·))) S.card))
  simpa [S, Nat.card_Icc, two_mul] using bound

/-- The main term uses the exact totient density, uniformly in X. -/
theorem discrepancy (X : ℕ) {M : ℕ} (pos : 0 < M) :
    |((units M X).card : ℝ) - (X : ℝ)*M.totient/M| ≤ 2*Real.sqrt M := by
  apply (discrepancy_le_divisors X pos).trans
  have count : (M.divisors.card : ℝ) ≤ 2*(M.sqrt : ℝ) := by exact_mod_cast divisors_le_two_sqrt M
  exact count.trans (mul_le_mul_of_nonneg_left
    (Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' M)) (by norm_num))

end PrimeFactors.CoprimePrefixDiscrepancy
