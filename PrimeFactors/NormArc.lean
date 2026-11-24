import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PrimeFactors.NormArc

/-- The discriminant of an intercept line also has a determinant expression
in the line's slope and its intercept at the origin. -/
theorem line_discriminant (A B N lo den num intercept : ℤ) :
    let K := A*den^2+B*num^2
    let L := A*den^2*lo-B*num*intercept
    let C := A*den^2*lo^2+B*intercept^2-N*den^2
    L^2-K*C = den^2*(N*K-A*B*(intercept+num*lo)^2) := by
  dsimp
  ring

/-- Every point on the ellipse and on the chosen line produces the exact
signed square root used to reconstruct its displacement. -/
theorem point_discriminant {A B N lo j y den num intercept : ℤ}
    (point : A*(lo+j)^2+B*y^2=N) (line : den*y+num*j=intercept) :
    let K := A*den^2+B*num^2
    let L := A*den^2*lo-B*num*intercept
    let C := A*den^2*lo^2+B*intercept^2-N*den^2
    (K*j+L)^2=L^2-K*C := by
  subst intercept
  dsimp
  linear_combination (A*den^2+B*num^2)*den^2*point

private theorem height_antitone {A B x z u v : ℝ}
    (a : 0 ≤ A) (b : 0 < B) (x0 : 0 ≤ x) (xz : x ≤ z)
    (u0 : 0 ≤ u) (v0 : 0 ≤ v) (norm : A*x^2+B*u^2=A*z^2+B*v^2) :
    v ≤ u := by
  by_contra! h
  have xsq := (sq_le_sq₀ x0 (x0.trans xz)).2 xz
  have ysq := (sq_lt_sq₀ u0 v0).2 h
  linarith only [mul_le_mul_of_nonneg_left xsq a, mul_lt_mul_of_pos_left ysq b, norm]

/-- Rational secant bounds for a block in the nonnegative quadrant.
The exact heights are u at lo, y at lo+j, and v at lo+w. The code
uses its rounded heights divided by the scale as lower and upper inputs. -/
theorem secant_bounds {A B lo j w u y v lowerLeft upperLeft lowerRight : ℝ}
    (a : 0 ≤ A) (b : 0 < B) (l : 0 ≤ lo) (j0 : 0 ≤ j) (jw : j ≤ w)
    (u0 : 0 ≤ u) (y0 : 0 ≤ y) (v0 : 0 ≤ v)
    (point : A*lo^2+B*u^2=A*(lo+j)^2+B*y^2)
    (right : A*(lo+j)^2+B*y^2=A*(lo+w)^2+B*v^2)
    (leftLow : lowerLeft ≤ u) (leftHigh : u ≤ upperLeft)
    (rightLow : lowerRight ≤ v) (upperPos : 0 < upperLeft)
    (denPos : 0 < lowerLeft+lowerRight) :
    A*lo/(B*upperLeft)*j ≤ u-y ∧
      u-y ≤ A*(2*lo+w)/(B*(lowerLeft+lowerRight))*j := by
  have yu := height_antitone a b l (by linarith) u0 y0 point
  have vy := height_antitone a b (add_nonneg l j0) (by linarith) y0 v0 right
  have scale : 0 ≤ B*(u-y) := mul_nonneg b.le (sub_nonneg.mpr yu)
  have eqn : B*(u-y)*(u+y)=A*j*(2*lo+j) := by linear_combination point
  have below := mul_le_mul_of_nonneg_left
    (show u+y ≤ 2*upperLeft by linarith only [yu,leftHigh]) scale
  have above := mul_le_mul_of_nonneg_left
    (add_le_add leftLow (rightLow.trans vy)) scale
  have leftPart := mul_le_mul_of_nonneg_left
    (show 2*lo ≤ 2*lo+j by linarith) (mul_nonneg a j0)
  have rightPart := mul_le_mul_of_nonneg_left
    (show 2*lo+j ≤ 2*lo+w by linarith) (mul_nonneg a j0)
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos b upperPos)]
    nlinarith only [eqn, below, leftPart]
  · rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos b denPos)]
    nlinarith only [eqn, above, rightPart]

private theorem scaled_span {j w : ℝ} (s : ℝ) (j0 : 0 ≤ j) (jw : j ≤ w) :
    min 0 (s*w) ≤ s*j ∧ s*j ≤ max 0 (s*w) := by
  rcases le_total 0 s with h | h
  · exact ⟨(min_le_left _ _).trans (mul_nonneg h j0),
      (mul_le_mul_of_nonneg_left jw h).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left jw h),
      (mul_nonpos_of_nonpos_of_nonneg h j0).trans (le_max_left _ _)⟩

/-- Each exact integer intercept lies in the interval obtained from the
rational height and secant bounds, for either sign of the slope error. -/
theorem intercept_bounds {u y den num j w lowerLeft upperLeft lowSlope highSlope : ℝ}
    (d : 0 ≤ den) (j0 : 0 ≤ j) (jw : j ≤ w)
    (leftLow : lowerLeft ≤ u) (leftHigh : u ≤ upperLeft)
    (slopeLow : lowSlope*j ≤ u-y) (slopeHigh : u-y ≤ highSlope*j) :
    den*lowerLeft+min 0 ((num-den*highSlope)*w) ≤ den*y+num*j ∧
      den*y+num*j ≤ den*upperLeft+max 0 ((num-den*lowSlope)*w) := by
  constructor
  · nlinarith only [(scaled_span (num-den*highSlope) j0 jw).1,
      mul_le_mul_of_nonneg_left leftLow d, mul_le_mul_of_nonneg_left slopeHigh d]
  · nlinarith only [(scaled_span (num-den*lowSlope) j0 jw).2,
      mul_le_mul_of_nonneg_left leftHigh d, mul_le_mul_of_nonneg_left slopeLow d]

end PrimeFactors.NormArc
