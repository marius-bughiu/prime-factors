import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace PrimeFactors

/-- The exact quadratic character autocorrelation of two distinct shifts
over a finite field of odd characteristic. -/
theorem phaseCharacters_shift_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (odd : ringChar F ≠ 2) {a b : F} (distinct : a ≠ b) :
    ∑ x : F, quadraticChar F ((x+a)*(x+b)) = -1 := by
  classical
  let e := ((Equiv.addRight b).trans (Equiv.inv F)).trans
    ((Equiv.mulLeft₀ (a-b) (sub_ne_zero.mpr distinct)).trans (Equiv.addLeft (1:F)))
  have eval (x : F) : e x = 1 + (a-b)*(x+b)⁻¹ := rfl
  have term (x : F) : quadraticChar F ((x+a)*(x+b)) =
      quadraticChar F (e x) - (if x= -b then 1 else 0) := by
    by_cases h : x= -b
    · subst x
      simp [eval]
    · have ne : x+b ≠ 0 := by simpa [eq_neg_iff_add_eq_zero] using h
      have identity : (x+a)*(x+b) = (x+b)^2 * e x := by
        rw [eval]
        field_simp
        ring
      have square : quadraticChar F ((x+b)^2) = 1 :=
        (quadraticChar_one_iff_isSquare (pow_ne_zero 2 ne)).mpr (IsSquare.sq _)
      rw [identity, map_mul, square, one_mul, if_neg h, sub_zero]
  simp_rw [term]
  rw [Finset.sum_sub_distrib, Equiv.sum_comp e, quadraticChar_sum_zero odd]
  simp

/-- The Walsh coefficients of a bounded table have squared mass at most
one. A uniform normalized hybrid bound on its monomials then gives the
factor 2^(k/2) in the magnitude bound, with no independence assumption on
the actual observed feature signs. -/
theorem phaseCharacters_walsh_transfer {k : ℕ} (c : Finset (Fin k) → ℝ)
    (wave : Finset (Fin k) → ℂ) {D : ℝ}
    (energy : (∑ s, (c s)^2) ≤ 1) (hybrid : ∀ s, ‖wave s‖ ≤ D) :
    ‖∑ s, (c s : ℂ)*wave s‖^2 ≤ (2:ℝ)^k * D^2 := by
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Finset (Fin k) => (1:ℝ)) (fun s => |c s|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_finset,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat, sq_abs] at cauchy
  have weights : (∑ s, |c s|)^2 ≤ (2:ℝ)^k :=
    cauchy.trans (by simpa using mul_le_mul_of_nonneg_left energy (by positivity : 0 ≤ (2:ℝ)^k))
  have upper := norm_sum_le (Finset.univ : Finset (Finset (Fin k))) (fun s => (c s : ℂ)*wave s)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at upper
  have terms := Finset.sum_le_sum fun s (_ : s ∈ (Finset.univ : Finset (Finset (Fin k)))) =>
    mul_le_mul_of_nonneg_left (hybrid s) (abs_nonneg (c s))
  rw [← Finset.sum_mul] at terms
  have square := mul_self_le_mul_self (norm_nonneg _) (upper.trans terms)
  rw [← sq, ← sq, mul_pow] at square
  exact square.trans (mul_le_mul_of_nonneg_right weights (sq_nonneg D))

/-- Equality of two ternary Jacobi values from their product and zero
patterns. This counts feature collisions without rounding either zero. -/
theorem phaseCharacters_ternary (a b : ℤ) (ha : a= -1 ∨ a=0 ∨ a=1)
    (hb : b= -1 ∨ b=0 ∨ b=1) :
    2*(if a=b then 1 else 0) =
      (if a≠0 ∧ b≠0 then 1 else 0) + a*b + 2*(if a=0 ∧ b=0 then 1 else 0) := by
  rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;> decide

/-- For the local collision formulas, multiplying twice the collision
probability by pq gives one of these numerators. -/
theorem phaseCharacters_collision_cap {p q : ℕ} (pMin : 3 ≤ p) (ordered : p ≤ q)
    (balanced : q ≤ 2*p) :
    9 ≤ 2*p+2*q ∧ q+3 ≤ 3*p ∧ p+3 ≤ 3*q := by omega

/-- Numerators in the 1024-bit-prime calculation, after the common
denominator 2^1023 and the harmonic upper bound of 1421. -/
theorem phaseCharacters_finite_estimates :
    1421*512^2*2^256+2*512+4 < (2:ℕ)^(1023-738) ∧
    1421*1024^2*2^512+2*1024+4 < (2:ℕ)^(1023-480) ∧
    1421*1536^2*2^768+2*1536+4 < (2:ℕ)^(1023-223) ∧
    1421*1900^2*2^950+2*1900+4 < (2:ℕ)^(1023-40) := by decide +kernel

end PrimeFactors
