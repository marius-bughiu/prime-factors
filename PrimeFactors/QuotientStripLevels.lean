import PrimeFactors.SecantQuotientCells
import PrimeFactors.QuotientStripScheduleCost
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Five integer lines cover the true factor rows of a balanced strip

Approximate the negative of the chord's slope by an integer ratio. The curved
arc through the genuine factor pairs stays closer to the chord than the full
tangent triangle. The normalized width is strictly less than five, so testing
at most five integer labels covers the arc.
-/

namespace PrimeFactors.QuotientStripLevels

/-- Dirichlet's bound, with only integer arithmetic needed to check the answer. -/
theorem direction_exists (N M : ℤ) (mpos : 0<M) (Q : ℕ) (qpos : 0<Q) :
    ∃ u v : ℤ, 0<v ∧ v≤Q ∧ |u*M-v*N| *((Q:ℤ)+1)≤M := by
  obtain ⟨u,v,vpos,vle,h⟩ := Real.exists_int_int_abs_mul_sub_le ((N:ℝ)/M) qpos
  refine ⟨u,v,vpos,vle,?_⟩
  have mp : (0:ℝ)<M := by exact_mod_cast mpos
  have qp : 0 < (Q:ℝ)+1 := by positivity
  rw [le_div_iff₀ qp] at h
  have rearrange : |(u:ℝ)*M-v*N| = |(v:ℝ)*((N:ℝ)/M)-u| *M := by
    rw [← abs_of_pos mp, ← abs_mul, abs_of_pos mp, ← abs_neg ((u:ℝ)*M-v*N)]
    congr 1
    field_simp
    ring
  have realBound : |(u:ℝ)*M-v*N| *((Q:ℝ)+1) ≤ M := by
    rw [rearrange]
    nlinarith only [mul_le_mul_of_nonneg_right h mp.le]
  exact_mod_cast realBound

/-- Scale of a projected integer label and offset at the left endpoint. -/
def scale (a b : ℤ) : ℤ := 4*a^2*b
def origin (a b N u v : ℤ) : ℤ := scale a b*u*a+4*a*b*v*N
def tilt (a b N u v : ℤ) : ℤ := 4*a*(u*a*b-v*N)

/-- The product supplies both bounds on each level, without counting strip points. -/
theorem enclosure {a b N x y u v : ℤ} (ap : 0<a) (left : a≤x) (right : x≤b)
    (yp : 0≤y) (vp : 0≤v) (prod : N=x*y) :
    let base := origin a b N u v
    let slope := tilt a b N u v
    let t := scale a b * (u*x+v*y)
    base+min 0 (slope*(b-a))-v*N*(b-a)^2 ≤ t ∧ t ≤ base+max 0 (slope*(b-a)) := by
  dsimp only
  have depth := SecantQuotientCells.factor_in_strip left right ap.le yp prod
  have eqn : scale a b * (u*x+v*y) =
      origin a b N u v + tilt a b N u v*(x-a) - v*SecantQuotientCells.depth a b N x y := by
    unfold scale origin tilt SecantQuotientCells.depth
    unfold scale
    ring
  rw [eqn]
  have shelf : min 0 (tilt a b N u v*(b-a)) ≤ tilt a b N u v*(x-a) ∧
      tilt a b N u v*(x-a) ≤ max 0 (tilt a b N u v*(b-a)) := by
    rcases le_total 0 (tilt a b N u v) with h|h
    · exact ⟨(min_le_left ..).trans (mul_nonneg h (by omega)),
        (mul_le_mul_of_nonneg_left (by omega : x-a≤b-a) h).trans (le_max_right ..)⟩
    · exact ⟨(min_le_right ..).trans (mul_le_mul_of_nonpos_left (by omega : x-a≤b-a) h),
        (mul_nonpos_of_nonpos_of_nonneg h (by omega)).trans (le_max_left ..)⟩
  constructor <;> nlinarith only [shelf.1, shelf.2, mul_nonneg vp depth.1,
    mul_le_mul_of_nonneg_left depth.2 vp]

/-- The sixth-root width and balance imply the estimates with constants 2
and 3, respectively, for the tilted chord and the gap below it. -/
theorem width_lt_five {N a b d u v Q : ℤ} (ap : 0<a) (dd : d=b-a) (dp : 0<d)
    (np : 0<N) (balance : N≤2*a^2) (width : d^6≤64*N)
    (rounding : d<2*(Q+1)) (vb : 2*v≤d)
    (approximation : |u*(a*b)-v*N| *(Q+1)≤a*b) :
    |tilt a b N u v*d| + v*N*d^2 < 5*scale a b := by
  have ab : a≤b := by omega
  have bp : 0<b := by omega
  have error : |u*(a*b)-v*N| *d < 2*(a*b) := by
    rcases (abs_nonneg (u*(a*b)-v*N)).lt_or_eq with pos|zero
    · nlinarith only [mul_lt_mul_of_pos_left rounding pos, approximation]
    · rw [← zero, zero_mul]
      positivity
  have cube : d^3 < 12*a := by
    by_contra! bad
    have a2 := sq_pos_of_pos ap
    nlinarith only [mul_self_le_mul_self (by positivity : 0≤12*a) bad, width, balance, a2]
  have tip := mul_lt_mul_of_pos_left cube np
  have area := mul_le_mul_of_nonneg_right balance (by positivity : 0≤12*a)
  have base := mul_le_mul_of_nonneg_left ab (by positivity : 0≤24*a^2)
  have half := mul_le_mul_of_nonneg_right vb (by positivity : 0≤N*d^2)
  have slope := mul_lt_mul_of_pos_left error (by positivity : 0<4*a)
  unfold tilt scale
  rw [abs_mul, abs_of_pos dp, abs_mul, abs_of_pos (by positivity : 0<4*a), mul_assoc u a b]
  nlinarith only [tip, area, base, half, slope]

/-- The integers in a closed rational interval of width strictly below five
lie between its first possible label and that integer plus four. -/
theorem five_labels {low high D : ℤ} (pos : 0<D) (width : high-low<5*D) :
    ∀ z : ℤ, low≤D*z → D*z≤high → -((-low)/D)≤z ∧ z≤-((-low)/D)+4 := by
  intro z lower upper
  have bound := Int.ediv_mul_le (-low) (ne_of_gt pos)
  have bot : -z ≤ (-low)/D := (Int.le_ediv_iff_mul_le pos).mpr (by nlinarith)
  have top : z < -((-low)/D)+5 := by
    by_contra! h
    have scaled := mul_le_mul_of_nonneg_right h pos.le
    nlinarith only [scaled, upper, width, bound]
  omega

/-- With at least three columns in a sixth-root strip, one direction and five
consecutive labels work simultaneously for every factor row in the strip.
The base of the interval is computed from the product, endpoints and direction. -/
theorem five_cover {N a b : ℤ} (ap : 0<a) (length : a+2≤b) (np : 0<N)
    (balance : N≤2*a^2) (width : (b-a)^6≤64*N) :
    ∃ u v L : ℤ, 0<v ∧ 2*v≤b-a ∧
      ∀ x y : ℤ, a≤x → x≤b → 0≤y → N=x*y → L≤u*x+v*y ∧ u*x+v*y≤L+4 := by
  let Q := ((b-a)/2).toNat
  have qint : (Q:ℤ)=(b-a)/2 := Int.toNat_of_nonneg (by omega)
  have qp : 0<Q := by omega
  have bp : 0<b := by omega
  obtain ⟨u,v,vp,vb,approximation⟩ := direction_exists N (a*b) (mul_pos ap bp) Q qp
  have small : 2*v≤b-a := by omega
  let R := tilt a b N u v*(b-a)
  let low := origin a b N u v + min 0 R - v*N*(b-a)^2
  let high := origin a b N u v + max 0 R
  have span := width_lt_five (u:=u) (v:=v) (Q:=(Q:ℤ)) ap rfl (by omega : 0<b-a)
    np balance width (by omega) small approximation
  have diff : high-low = |R| + v*N*(b-a)^2 := by
    dsimp only [high,low]
    rcases le_total 0 R with h|h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_left h, min_eq_right h, abs_of_nonpos h]; ring
  have pos : 0<scale a b := by unfold scale; positivity
  refine ⟨u,v,-((-low)/scale a b),vp,small,?_⟩
  intro x y left right yp prod
  have mem := enclosure (u:=u) ap left right yp vp.le prod
  exact five_labels pos (diff.trans_lt span) _ mem.1 mem.2

/-- A block of the declared schedule meets the sixth-power hypothesis,
including a clipped final block. The length argument counts endpoint distance. -/
theorem scheduled_span {n d : ℕ} (positive : 0<n)
    (short : d < QuotientStripScheduleCost.width n) : d^6≤64*n := by
  let r := QuotientStripScheduleCost.roundedSixth n
  change d < 2*r at short
  by_cases small : r≤1
  · have d1 : d≤1 := by omega
    exact (Nat.pow_le_pow_left d1 6).trans (by simpa only [one_pow] using (by omega : 1≤64*n))
  · have prev : (2*(r-1)+1)^6 < 64*n := by
      by_contra failed
      have smaller : r≤r-1 := by
        change QuotientStripScheduleCost.roundedSixth n ≤ r-1
        unfold QuotientStripScheduleCost.roundedSixth
        apply Nat.find_min'
        exact ⟨by omega, le_of_not_gt failed⟩
      omega
    exact (Nat.pow_le_pow_left (by omega : d≤2*(r-1)+1) 6).trans prev.le

/-- A square check on each retained label is a necessary step for a hit. -/
theorem level_discriminant (u v x y : ℤ) :
    (u*x+v*y)^2 - 4*u*v*(x*y) = (2*u*x-(u*x+v*y))^2 := by ring

/-- On this scheduled block the chord gives labels 3091 and 3092. Oddness
leaves 3091 and its discriminant is 21², recovering the unique factor row. -/
theorem example_119423 {x y : ℤ} (left : 301≤x) (right : x≤314) (yp : 0≤y)
    (prod : (119423:ℤ)=x*y) : x=307 ∧ y=389 := by
  have bounds := enclosure (u:=5) (v:=4) (by decide : (0:ℤ)<301) left right yp (by decide) prod
  norm_num [origin, tilt, scale] at bounds
  have odd : x%2≠0 := by
    intro even
    have impossible : (119423:ℤ)%2=0 := by rw [prod, Int.mul_emod, even]; simp
    norm_num at impossible
  have label : 5*x+4*y=3091 := by omega
  have square := level_discriminant 5 4 x y
  rw [label, ← prod] at square
  have roots : (10*x-3091-21)*(10*x-3091+21)=0 := by nlinarith only [square]
  rcases mul_eq_zero.mp roots with h|h <;> omega

end PrimeFactors.QuotientStripLevels
