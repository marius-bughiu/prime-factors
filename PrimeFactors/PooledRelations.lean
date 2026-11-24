import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- A weighted pair of factors produces a square norm with denominator
`2*a*b`. Dividing all three entries by a common divisor preserves the identity. -/
theorem pooledRelations_weighted_square (p q a b : ℤ) :
    (a^2*p + b^2*q)^2 - p*q*(2*a*b)^2 = (a^2*p - b^2*q)^2 := by ring

/-- In the planted near-square family the weighted difference is independent
of `t`, even as both factors grow. -/
theorem pooledRelations_family_gap (a b g t : ℤ) :
    b^2*((a*g)^2*t+2*(a*g)+1) - a^2*((b*g)^2*t+2*(b*g)+1) =
      (b-a)*(2*a*b*g+a+b) := by ring

/-- A uniform bound on the weighted squared difference. The right side is
a lower bound on the square root of the near-square product. -/
theorem pooledRelations_family_bound {a b g t : ℕ} (hg : 1 ≤ g)
    (threshold : (b-a)^2*(2*a*b+a+b)^2 < a*b*t) :
    ((b-a)*(2*a*b*g+a+b))^2 < g^2*(a*b*t) := by
  have mono : 2*a*b*g+a+b ≤ g*(2*a*b+a+b) := by
    nlinarith only [Nat.mul_le_mul_left a hg, Nat.mul_le_mul_left b hg]
  calc
    _ ≤ ((b-a)*(g*(2*a*b+a+b)))^2 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left (b-a) mono) 2
    _ = g^2*((b-a)^2*(2*a*b+a+b)^2) := by ring
    _ < _ := Nat.mul_lt_mul_of_pos_left threshold (pow_pos (by omega) _)

/-- A square norm small enough to meet Legendre's bound occurs in the ordinary
continued fraction of the public square root. The denominator and numerator
here are already in lowest terms. -/
theorem pooledRelations_square_convergent {N : ℕ} {r : ℚ} {z : ℝ}
    (positive : 0 < Real.sqrt N + (r : ℝ))
    (norm : (r.num : ℝ)^2 - N*(r.den : ℝ)^2 = z^2)
    (small : 2*z^2 < Real.sqrt N + (r : ℝ)) :
    ∃ i, r = (Real.sqrt N).convergent i := by
  have den : 0 < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have num : (r : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by
    rw [Rat.cast_def, div_mul_cancel₀ _ den.ne']
  have identity : (((r : ℝ) - Real.sqrt N) * (Real.sqrt N + (r : ℝ))) *
      (r.den : ℝ)^2 = z^2 := by
    rw [← norm, ← num]
    calc
      _ = ((r : ℝ)*(r.den : ℝ))^2 - (Real.sqrt N)^2*(r.den : ℝ)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]
  have absolute := congrArg abs identity
  rw [abs_mul, abs_mul, abs_of_pos positive, abs_of_nonneg (sq_nonneg (r.den : ℝ)),
    abs_of_nonneg (sq_nonneg z), abs_sub_comm] at absolute
  apply Real.exists_rat_eq_convergent
  apply (lt_div_iff₀ (by positivity)).mpr
  apply (mul_lt_mul_left positive).mp
  rw [mul_one]
  nlinarith only [absolute, small]

/-- With a square multiplier, the common divisor of the full numerator squared
and multiplier is the square of a common divisor. -/
theorem pooledRelations_gcd_square (x a : ℕ) :
    Nat.gcd (x^2) (a^2) = (Nat.gcd x a)^2 := by
  exact Nat.pow_gcd_pow

/-- Dividing out a known unit square preserves the signed norm relation. -/
theorem pooledRelations_normalize {A : Type*} [CommRing A] {x g r : A}
    (unit : IsUnit g) (y : A) (scale : x = g*y) (norm : x^2 = g^2*r) :
    y^2 = r := by
  rw [scale, mul_pow] at norm
  exact (unit.pow 2).mul_right_inj.mp norm

/-- The third rows from the two walks give different square roots of the same
signed unit modulo the product. -/
theorem pooledRelations_small_example :
    (18543^2 + 4847) % 21490481 = 0 ∧
    (98121^2 + 4847) % 21490481 = 0 ∧
    Nat.gcd (98121-18543) 21490481 = 4421 ∧ 4421*4861 = 21490481 := by decide

end PrimeFactors
