import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- On the product fiber N=xy, multiplying the cleared shifted product by x²
gives a cubic with three explicit roots. Hence its square test is unchanged. -/
theorem shift_cubic_iff {K : Type*} [Field K] (a b x y : K) (hx : x ≠ 0) :
    IsSquare ((2*b*x+a)*(2*b*y+a)) ↔
      IsSquare (x*(2*b*x+a)*(a*x+2*b*(x*y))) := by
  let v := (2*b*x+a)*(2*b*y+a)
  have same : x*(2*b*x+a)*(a*x+2*b*(x*y)) = v*(x*x) := by dsimp [v]; ring
  rw [same]
  change IsSquare v ↔ _
  constructor
  · exact fun h => h.mul (IsSquare.mul_self x)
  · rintro ⟨r, hr⟩
    refine ⟨r/x, ?_⟩
    field_simp
    exact hr

/-- Nondegenerate parameters give three distinct roots of the cubic,
including zero. This is the smoothness condition for the Hasse bound in
odd characteristic. -/
theorem shift_cubic_roots {K : Type*} [Field K] {a b n : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hn : n ≠ 0) (two : (2 : K) ≠ 0)
    (distinct : a^2 ≠ 4*b^2*n) :
    -a/(2*b) ≠ 0 ∧ -(2*b*n)/a ≠ 0 ∧ -a/(2*b) ≠ -(2*b*n)/a := by
  refine ⟨div_ne_zero (neg_ne_zero.mpr ha) (mul_ne_zero two hb),
    div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two hb) hn)) ha, ?_⟩
  intro eq
  apply distinct
  field_simp [two, hb, ha] at eq
  linear_combination eq

end PrimeFactors
