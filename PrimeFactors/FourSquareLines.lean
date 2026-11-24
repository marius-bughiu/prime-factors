import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- At least one of three public two-square pivots is nonzero at each odd
prime where the quaternion has rank one. -/
theorem fourSquareLines_pivot {F : Type*} [Field F] {a b c d : F}
    (odd : (2 : F) ≠ 0) (norm : a^2+b^2+c^2+d^2 = 0)
    (primitive : ¬(a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)) :
    a^2+b^2 ≠ 0 ∨ a^2+c^2 ≠ 0 ∨ a^2+d^2 ≠ 0 := by
  by_contra! no
  obtain ⟨h₁,h₂,h₃⟩ := no
  have h : (2:F)*a^2 = 0 := by linear_combination h₁+h₂+h₃-norm
  have ha : a = 0 := pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp ((mul_eq_zero.mp h).resolve_left odd)
  subst a
  simp_all

/-- Division in the chosen pair constructs a public solution of u²+v²=-1,
even over a composite modulus. -/
theorem fourSquareLines_split {R : Type*} [CommRing R] {a b c d e : R}
    (norm : a^2+b^2+c^2+d^2=0) (inverse : (a^2+b^2)*e=1) :
    ((a*c+b*d)*e)^2 + ((a*d-b*c)*e)^2 = -1 := by
  have h : c^2+d^2 = -(a^2+b^2) := by linear_combination norm
  calc
    _ = (a^2+b^2)*(c^2+d^2)*e^2 := by ring
    _ = -((a^2+b^2)*e)^2 := by rw [h]; ring
    _ = -1 := by rw [inverse]; simp

/-- The Hamilton quaternion in the public split matrix coordinates. -/
def fourSquareLinesMatrix {R : Type*} [CommRing R] (u v : R) (x : Quaternion R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![x.re + x.imJ*u - x.imK*v, -x.imI + x.imJ*v + x.imK*u;
      x.imI + x.imJ*v + x.imK*u, x.re - x.imJ*u + x.imK*v]

/-- In these coordinates the determinant is exactly the reduced norm. -/
theorem fourSquareLines_det {R : Type*} [CommRing R] {u v : R}
    (split : u^2+v^2 = -1) (x : Quaternion R) :
    (fourSquareLinesMatrix u v x).det = x.re^2+x.imI^2+x.imJ^2+x.imK^2 := by
  simp [fourSquareLinesMatrix, Matrix.det_fin_two]
  linear_combination -(x.imJ^2+x.imK^2)*split

/-- Four linear combinations recover twice the input coordinates. In odd
characteristic this also distinguishes all quaternions in the chart. -/
theorem fourSquareLines_recover {R : Type*} [CommRing R] {u v : R}
    (split : u^2+v^2 = -1) (x : Quaternion R) :
    let M := fourSquareLinesMatrix u v x
    M 0 0 + M 1 1 = 2*x.re ∧ M 1 0 - M 0 1 = 2*x.imI ∧
    -(u*(M 0 0-M 1 1) + v*(M 0 1+M 1 0)) = 2*x.imJ ∧
    v*(M 0 0-M 1 1) - u*(M 0 1+M 1 0) = 2*x.imK := by
  dsimp [fourSquareLinesMatrix]
  refine ⟨by ring, by ring, ?_, ?_⟩
  · linear_combination -2*x.imJ*split
  · linear_combination -2*x.imK*split

/-- Multiplication is preserved by the chart, including over rings with
zero divisors. -/
theorem fourSquareLines_mul {R : Type*} [CommRing R] {u v : R}
    (split : u^2+v^2 = -1) (x y : Quaternion R) :
    fourSquareLinesMatrix u v (x*y) = fourSquareLinesMatrix u v x * fourSquareLinesMatrix u v y := by
  have hv : v^2 = -1-u^2 := by linear_combination split
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourSquareLinesMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK] <;>
    ring_nf <;> simp only [hv] <;> ring

/-- Two affine row slopes coincide exactly where their determinant vanishes. -/
theorem fourSquareLines_slopes {R : Type*} [CommRing R] {a b c d s t : R}
    (left : b=a*s) (right : d=c*t) (ac : IsUnit (a*c)) :
    a*d-b*c = 0 ↔ t=s := by
  rw [left, right, show a*(c*t)-a*s*c = (a*c)*(t-s) by ring]
  rw [← mul_zero (a*c), ac.mul_right_inj, sub_eq_zero]

/-- An input-only representation of 77 sets the chart. Two other integral
representations have distinct affine slopes with a proper common prime. -/
theorem fourSquareLines_example :
    0^2+2^2+3^2+8^2 = 77 ∧ 0^2+3^2+2^2+8^2 = 77 ∧
    0^2+6^2+4^2+5^2 = 77 ∧
    ((4:ZMod 77)^2+37^2 = -1) ∧
    fourSquareLinesMatrix (4:ZMod 77) 37 ⟨0,3,2,8⟩ = !![20,26;32,57] ∧
    fourSquareLinesMatrix (4:ZMod 77) 37 ⟨0,6,4,5⟩ = !![62,8;20,15] ∧
    ((20:ZMod 77)*9 = 26) ∧ ((62:ZMod 77)*20 = 8) ∧
    Nat.gcd (20-9) 77 = 11 ∧ Nat.Prime 7 ∧ Nat.Prime 11 ∧ 7*11 = 77 := by decide

end PrimeFactors
