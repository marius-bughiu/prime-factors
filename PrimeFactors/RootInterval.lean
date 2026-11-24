import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- A scaled modular square in a translated interval gives an ordinary quadratic
whose constant term is an unknown multiple of the public modulus. -/
theorem rootInterval_lift {N c v b r s j k : ℤ}
    (square : N ∣ (c+v)^2-1) (linear : 2*b*c = r+N*j)
    (constant : b*(c^2-1) = s+N*k) :
    ∃ t : ℤ, b*v^2+r*v+s = N*t := by
  obtain ⟨w, hw⟩ := square
  refine ⟨b*w-j*v-k, ?_⟩
  linear_combination b*hw - v*linear - constant

/-- All admissible multiples lie within the radius used by the decoder. -/
theorem rootInterval_lift_range {N b v r s t M : ℤ}
    (hb : 0 ≤ b) (hv : |v| ≤ M) (eqn : b*v^2+r*v+s = N*t) :
    |N*t-s| ≤ b*M^2 + |r| * M := by
  rw [← eqn, add_sub_cancel_right]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg hb, abs_of_nonneg (sq_nonneg v)]
    exact mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith [(abs_le.mp hv).1])
      (abs_le.mp hv).2) hb
  · simpa only [abs_mul] using mul_le_mul_of_nonneg_left hv (abs_nonneg r)

/-- A sufficiently short lift range contains at most one multiple. -/
theorem rootInterval_unique {N t u s E : ℤ} (short : 2*E < N)
    (ht : |N*t-s| ≤ E) (hu : |N*u-s| ≤ E) : t = u := by
  have ordered {i j : ℤ} (lt : i < j) (hi : |N*i-s| ≤ E)
      (hj : |N*j-s| ≤ E) : False := by
    have gap : 1 ≤ j-i := by omega
    have hN : 0 ≤ N := by linarith [(abs_nonneg (N*i-s))]
    have := mul_le_mul_of_nonneg_left gap hN
    linarith [(abs_le.mp hi).1, (abs_le.mp hj).2]
  rcases lt_trichotomy t u with h | h | h
  · exact (ordered h ht hu).elim
  · exact h
  · exact (ordered h hu ht).elim

/-- At a lift, the integer discriminant is a square; either quadratic root
can be checked by multiplication and a gcd. -/
theorem rootInterval_discriminant {N b v r s t : ℤ}
    (eqn : b*v^2+r*v+s = N*t) :
    r^2-4*b*(s-N*t) = (2*b*v+r)^2 := by rw [← eqn]; ring

/-- Two square bounds on the coefficients imply the cube-root radius
guarantee without square roots or divisions. -/
theorem rootInterval_cube_bound {N M b r : ℝ}
    (hn : 0 < N) (hm : 0 < M) (hb : b^2*M ≤ N)
    (hr : r^2 ≤ N*M) (small : 64*M^3 ≤ N) :
    2*(b*M^2+|r| * M) < N := by
  have h₁ : (b*M^2)^2 ≤ N*M^3 := by
    calc (b*M^2)^2 = (b^2*M)*M^3 := by ring
         _ ≤ N*M^3 := by gcongr
  have h₂ : (|r| * M)^2 ≤ N*M^3 := by
    calc (|r| * M)^2 = r^2*M^2 := by rw [mul_pow, sq_abs]
         _ ≤ (N*M)*M^2 := by gcongr
         _ = N*M^3 := by ring
  have small' := mul_le_mul_of_nonneg_left small hn.le
  have bound (z : ℝ) (hz : z^2 ≤ N*M^3) : 8*z ≤ N := by
    by_contra! bad
    have prod := mul_pos (sub_pos.mpr bad) (show 0 < 8*z+N by linarith)
    nlinarith only [prod, hz, small']
  linarith [bound _ h₁, bound _ h₂]

end PrimeFactors
