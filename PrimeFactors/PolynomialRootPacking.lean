import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace PrimeFactors.PolynomialRootPacking

open Polynomial
open scoped BigOperators

/-- All roots across all square-root classes of one modulus constrain the
Vandermonde determinant. The modulus can be composite or non-squarefree. -/
theorem power_dvd_differences {k : ℕ} {A N : ℤ} (v : Fin k → ℤ)
    (root : ∀ i, A ∣ (v i)^2-N) :
    A^(∑ j : Fin k, (j : ℕ)/2) ∣
      ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (v j-v i) := by
  classical
  choose q hq using root
  let P : Fin k → ℤ[X] := fun j => (X^2-C N)^((j:ℕ)/2)*X^((j:ℕ)%2)
  have mon : Monic (X^2-C N) := monic_X_pow_sub_C N (by decide)
  have deg (j : Fin k) : (P j).natDegree=j := by
    dsimp [P]
    rw [(mon.pow _).natDegree_mul (monic_X.pow _), mon.natDegree_pow,
      natDegree_X_pow_sub_C, natDegree_X_pow]
    omega
  have leading (j : Fin k) : Monic (P j) := (mon.pow _).mul (monic_X.pow _)
  let T : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun i j => (q i)^((j:ℕ)/2)*(v i)^((j:ℕ)%2)
  have columns : Matrix.of (fun i j => (P j).eval (v i)) =
      Matrix.of (fun (i j : Fin k) => A^((j:ℕ)/2)*T i j) := by
    ext i j
    simp [T, P, hq i, mul_pow, mul_assoc]
  rw [← Matrix.det_vandermonde, Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v P deg leading,
    columns, Matrix.det_mul_row, ← Finset.prod_pow_eq_pow_sum]
  exact dvd_mul_right _ _

/-- Replacing the linear coefficient and the constant by their signed residues
preserves every root of the translated quadratic after scaling. -/
theorem scaled_root {A N c t k b z y w v : ℤ} (root : (c+t)^2-N=A*v)
    (slope : 2*k*c=b+A*y) (constant : k*(c^2-N)=z+A*w) :
    k*t^2+b*t+z = A*(k*v-y*t-w) := by
  linear_combination k*root - t*slope - constant

/-- The lift interval has length less than one modulus at this explicit
cube-root radius. Bounded-slope approximation supplies k and b. -/
theorem single_lift_width {A R k b : ℤ} (pos : 0 < A) (r : 0 ≤ R)
    (radius : 16*R^3 ≤ A) (multiplier : k ≤ 4*R)
    (slope : |b| *(4*R+1) ≤ A) : 2*(k*R^2+|b| *R) < A := by
  have quad := mul_le_mul_of_nonneg_right multiplier (sq_nonneg R)
  by_cases hb : |b|=0
  · rw [hb, zero_mul, add_zero]
    nlinarith [mul_nonneg (sq_nonneg R) r]
  · have h := abs_nonneg b
    nlinarith

end PrimeFactors.PolynomialRootPacking
