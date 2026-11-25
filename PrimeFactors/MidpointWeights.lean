import PrimeFactors.ModularHyperbola
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

namespace PrimeFactors

/-- On a balanced factor pair the midpoint and the unsigned half-gap lie in
two intervals determined by the product. Either ordering of the factors works. -/
theorem balanced_weight_coordinates {h d : ℤ}
    (balanced : 3 * |d| ≤ h) :
    let N := (h - d) * (h + d)
    N ≤ h ^ 2 ∧ 8 * h ^ 2 ≤ 9 * N ∧ 8 * d ^ 2 ≤ N := by
  have b := mul_self_le_mul_self (by positivity : 0 ≤ 3 * |d|) balanced
  have e := sq_abs d
  dsimp
  constructor
  · nlinarith [sq_nonneg d]
  · constructor <;> nlinarith

/-- In midpoint coordinates, either ordering satisfies the balance condition
exactly when the absolute half-gap is at most a third of the midpoint. -/
theorem midpoint_balance_iff (h d : ℤ) :
    (h+d ≤ 2*(h-d) ∧ h-d ≤ 2*(h+d)) ↔ 3*|d| ≤ h := by
  by_cases hd : 0 ≤ d
  · rw [abs_of_nonneg hd]
    omega
  · rw [abs_of_neg (by omega : d < 0)]
    omega

/-- With the stationary choice of weights, the product fixes their weighted
sum modulo R² on the whole low-digit pair. -/
theorem midpoint_weight_congruence {R N u w k i v z a b : ℤ}
    (hr : R ≠ 0) (carry : N = u*w + R*k) (inverse : u*i ≡ 1 [ZMOD R])
    (product : (u+R*v)*(w+R*z) = N) (weight : b ≡ a*i*w [ZMOD R]) :
    a*(w+R*z) + b*(u+R*v) ≡ a*(w+R*(i*k)) + b*u [ZMOD R^2] := by
  have hz := (hyperbola_affine_partner_iff hr carry inverse v z).mp
    (show (u+R*v)*(w+R*z) ≡ N [ZMOD R^2] by rw [product])
  obtain ⟨j, hj⟩ := Int.modEq_iff_dvd.mp hz
  obtain ⟨l, hl⟩ := Int.modEq_iff_dvd.mp weight
  apply Int.modEq_iff_dvd.mpr
  refine ⟨a*j + v*l, ?_⟩
  linear_combination R*a*hj + R*v*hl

/-- The sum's absolute change between two possible midpoints and gaps is
bounded by the width used to choose the weights. -/
theorem midpoint_weight_width {a b h h' d d' H G : ℤ}
    (midpoints : |h-h'| ≤ H) (gaps : |d-d'| ≤ G) :
    |(a*(h+d)+b*(h-d)) - (a*(h'+d')+b*(h'-d'))| ≤
      H*|a+b| + G*|a-b| := by
  rw [show a*(h+d)+b*(h-d) - (a*(h'+d')+b*(h'-d')) =
    (h-h')*(a+b) + (d-d')*(a-b) by ring]
  exact (abs_add_le ..).trans (by
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right midpoints (abs_nonneg _))
      (mul_le_mul_of_nonneg_right gaps (abs_nonneg _)))

/-- Two sums at distance strictly less than the modulus cannot differ
if the residue test identifies them. -/
theorem midpoint_weight_unique {t t' step : ℤ}
    (close : |t-t'| < step) (lane : t ≡ t' [ZMOD step]) : t = t' := by
  by_cases h : t ≤ t'
  · have := Int.eq_zero_of_dvd_of_nonneg_of_lt (sub_nonneg.mpr h)
      (by rw [abs_of_nonpos (sub_nonpos.mpr h)] at close; omega : t'-t < step)
      (Int.modEq_iff_dvd.mp lane)
    omega
  · have h' : t' ≤ t := by omega
    have := Int.eq_zero_of_dvd_of_nonneg_of_lt (sub_nonneg.mpr h')
      (by rwa [abs_of_nonneg (sub_nonneg.mpr h')] at close : t-t' < step)
      (Int.modEq_iff_dvd.mp lane.symm)
    omega

/-- The surviving trace determines a quadratic with the first factor as
a root. Its discriminant must be a square. -/
theorem midpoint_weight_discriminant (x y a b : ℤ) :
    let N := x*y
    let t := a*y+b*x
    b*x^2-t*x+a*N = 0 ∧ t^2-4*a*b*N = (a*y-b*x)^2 := by
  constructor <;> ring

end PrimeFactors
