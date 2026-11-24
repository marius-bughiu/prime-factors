import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- The excess above the geometric minimum obeys both an asymmetric and a
symmetric bound. The latter allows slopes to be counted by their product
even if the two unknown positive factors have very different sizes. -/
theorem exceptionalWeight_slack {u v p q E : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hp : 0 < p) (hq : 0 < q) (error : |u * q - v * p| ≤ E) :
    let z := Real.sqrt (u * v * p * q)
    0 ≤ u * q + v * p - 2 * z ∧
      u * q + v * p - 2 * z ≤ E ^ 2 / (u * q) ∧
      u * q + v * p - 2 * z ≤ E ^ 2 / (4 * z) := by
  let z := Real.sqrt (u * v * p * q)
  have zpos : 0 < z := by dsimp [z]; positivity
  have zs : z ^ 2 = u * v * p * q := Real.sq_sqrt (by positivity)
  have am : 2 * z ≤ u * q + v * p := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ 2 * z) (by positivity : 0 ≤ u * q + v * p)).mp
    nlinarith only [zs, sq_nonneg (u * q - v * p)]
  have ep := (abs_nonneg (u * q - v * p)).trans error
  have errSq := sq_le_sq.mpr (show |u * q - v * p| ≤ |E| by rwa [abs_of_nonneg ep])
  have identity : (u * q + v * p - 2 * z) * (u * q + v * p + 2 * z) =
      (u * q - v * p) ^ 2 := by nlinarith only [zs]
  have slack := sub_nonneg.mpr am
  change 0 ≤ u * q + v * p - 2 * z ∧ _ ∧ _
  refine ⟨slack, (le_div_iff₀ (mul_pos hu hq)).mpr ?_, (le_div_iff₀ (by positivity : 0 < 4 * z)).mpr ?_⟩
  · have bound : u * q ≤ u * q + v * p + 2 * z := by linarith [mul_pos hv hp]
    exact (mul_le_mul_of_nonneg_left bound slack).trans (identity.le.trans errSq)
  · have bound : 4 * z ≤ u * q + v * p + 2 * z := by linarith
    exact (mul_le_mul_of_nonneg_left bound slack).trans (identity.le.trans errSq)

/-- Strictly smaller error than either positive factor rules out zero or
opposite signs for a nonzero pair of integer weights. -/
theorem exceptionalWeight_same_sign {u v p q : ℤ} (hp : 0 < p) (hq : 0 < q)
    (nonzero : u ≠ 0 ∨ v ≠ 0) (small : |u * q - v * p| < min p q) :
    (0 < u ∧ 0 < v) ∨ (u < 0 ∧ v < 0) := by
  have classify (a x : ℤ) (hx : 0 < x) :
      a = 0 ∧ a * x = 0 ∨ 0 < a ∧ x ≤ a * x ∨ a < 0 ∧ a * x ≤ -x := by
    rcases lt_trichotomy a 0 with neg | eq | pos
    · have bound := mul_le_mul_of_nonneg_right (show a ≤ -1 by omega) hx.le
      exact Or.inr (Or.inr ⟨neg, by simpa using bound⟩)
    · exact Or.inl ⟨eq, by rw [eq, zero_mul]⟩
    · have bound := mul_le_mul_of_nonneg_right (show 1 ≤ a by omega) hx.le
      exact Or.inr (Or.inl ⟨pos, by simpa using bound⟩)
  obtain ⟨low, high⟩ := abs_lt.mp small
  rcases classify u q hq with z | plus | minus <;>
    rcases classify v p hp with z' | plus' | minus' <;> omega

/-- A stationary unit residue s of p modulo r fixes the weighted trace
modulo r². Multiplying by s avoids modular division in the statement. -/
theorem exceptionalWeight_stationary_trace {p q u v s r : ℤ} (unit : IsCoprime r p)
    (residue : p ≡ s [ZMOD r]) (root : v * p ^ 2 ≡ u * (p * q) [ZMOD r]) :
    s * (u * q + v * p) ≡ u * (p * q) + v * s ^ 2 [ZMOD r ^ 2] := by
  have h₁ : r ∣ p - s := Int.modEq_iff_dvd.mp residue.symm
  have h₂ : r ∣ u * q - v * p := by
    apply unit.dvd_of_dvd_mul_left
    convert Int.modEq_iff_dvd.mp root using 1
    ring
  have h₃ : r ∣ u * q - v * s := by
    convert dvd_add h₂ (dvd_mul_of_dvd_right h₁ v) using 1
    ring
  apply Int.modEq_iff_dvd.mpr
  convert mul_dvd_mul h₁ h₃ using 1 <;> ring

/-- At N = 15049 the normalized weights (2, 3) have signed gap −5.
The stationary residue 1 modulo 5 fixes the trace 601 modulo 25. -/
theorem exceptionalWeight_small_example :
    let p : ℤ := 101
    let q : ℤ := 149
    let u : ℤ := 2
    let v : ℤ := 3
    p * q = 15049 ∧ u * q - v * p = -5 ∧ (v * p ^ 2 ≡ u * (p * q) [ZMOD 5]) ∧
      u * q + v * p = 601 ∧ (u * q + v * p ≡ 1 [ZMOD 25]) := by decide +kernel

end PrimeFactors
