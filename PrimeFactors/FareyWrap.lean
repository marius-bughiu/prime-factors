import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace PrimeFactors.FareyWrap

/-- Both the true weighted sum and the tested label lie on the stride s.
The local equality then has exactly the order of the 24th power as its period
in stride coordinates. Negative displacements are allowed. -/
theorem period {G : Type*} [Group G] (v : G) {s : ℕ} (hs : s ∣ 24)
    {T t j : ℤ} (grid : T-t = (s:ℤ)*j) :
    v ^ (((24/s : ℕ):ℤ)*(T-t)) = 1 ↔ (orderOf (v^24):ℤ) ∣ j := by
  have prod : (((24/s : ℕ):ℤ) * (s:ℤ)) = 24 := by exact_mod_cast Nat.div_mul_cancel hs
  rw [grid, ← mul_assoc, prod, zpow_mul]
  rw [show v^(24:ℤ) = v^(24:ℕ) by exact zpow_natCast v 24, orderOf_dvd_iff_zpow_eq_one]

/-- Suppose z_i is sqrt(b r_i), c is sqrt(a) and v bounds both z_i.
When both points are on one branch at distance at least u from c, an interval
of square displacements of width eps contains a ratio interval of width
at most v eps/(bu). The formulation avoids division at zero. -/
theorem branch_diameter {b r₁ r₂ z₁ z₂ c u v eps : ℝ}
    (zlo : 0 ≤ z₁) (ordered : z₁ ≤ z₂) (cap : z₂ ≤ v)
    (e0 : 0 ≤ eps)
    (first : z₁^2 = b*r₁) (last : z₂^2 = b*r₂)
    (branch : u ≤ z₁-c ∨ u ≤ c-z₂)
    (variation : |(z₂-c)^2-(z₁-c)^2| ≤ eps) :
    (r₂-r₁)*b*u ≤ v*eps := by
  have diff : (z₂-z₁)*(z₂+z₁) = (r₂-r₁)*b := by nlinarith only [first,last]
  have shell : (z₂-z₁)*(2*u) ≤ eps := by
    obtain ⟨lower,upper⟩ := abs_le.mp variation
    rcases branch with right | left
    · have h : 2*u ≤ z₂+z₁-2*c := by linarith
      nlinarith only [upper, mul_le_mul_of_nonneg_left h (sub_nonneg.mpr ordered)]
    · have h : 2*u ≤ 2*c-z₂-z₁ := by linarith
      nlinarith only [lower, mul_le_mul_of_nonneg_left h (sub_nonneg.mpr ordered)]
  have h1 := mul_le_mul_of_nonneg_right shell (show 0 ≤ z₂+z₁ by linarith)
  have h2 := mul_le_mul_of_nonneg_right (show z₂+z₁ ≤ 2*v by linarith) e0
  rw [← diff]
  nlinarith only [h1,h2]

/-- The sum of inverse square roots controls the total width over nonzero
periods without a factor of log(K). -/
theorem reciprocal_sqrt_sum (n : ℕ) :
    ∑ i ∈ Finset.range n, 1/Real.sqrt ((i:ℝ)+1) ≤ 2*Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have pos : (0:ℝ) < n+1 := by positivity
    have h : 1/Real.sqrt ((n:ℝ)+1) ≤ 2*(Real.sqrt ((n:ℝ)+1)-Real.sqrt n) := by
      apply (div_le_iff₀ (Real.sqrt_pos.mpr pos)).mpr
      nlinarith only [Real.sq_sqrt pos.le, Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity),
        sq_nonneg (Real.sqrt ((n:ℝ)+1)-Real.sqrt n)]
    linarith

set_option maxRecDepth 4096 in
/-- A genuine wrapped label exposes the factor 109 at base 2. The candidate
1051 differs from the exact weighted sum 1069 by one local period of 18. -/
theorem example_22999 : Nat.Prime 109 ∧ Nat.Prime 211 ∧ 109*211 = (22999:ℕ) ∧
    4*109+3*211 = (1069:ℕ) ∧ (24/2)*(4+3*22999-1051) = (815400:ℕ) ∧
    (2 : ZMod 22999)^815400 = 18204 ∧ Nat.gcd (18204-1) 22999 = 109 := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,?_,by decide⟩
  have one : (2 : ZMod 22999)^1260 = 1 := by
    rw [show 1260 = 36*35 by decide, pow_mul]
    decide
  rw [show 815400 = 1260*647+180 by decide, pow_add, pow_mul, one, one_pow, one_mul]
  decide

/-- Exact rational arithmetic in the population estimate. The logarithm and
prime-count bounds substituted here are separate analytic inputs. -/
theorem target_probability_arithmetic :
    let X : ℚ := 2^1023
    let K : ℚ := 2^204
    let m : ℚ := 2^408
    let A := 20/K + 240*m*K^2/X + 2*K^3/X
    let universal := 30*(1511/1000)*710*A/(22/100)^2
    let random := 60*711*710^2*A/(22/100)^2
    let central := (2*(1511/1000)*710/(22/100)^2)*
      (36/2^104 + 90/2^157 + 1/2^823)
    universal < 1/2^178 ∧ random < 1/2^159 ∧ central + random < 1/2^83 := by
  norm_num

end PrimeFactors.FareyWrap
