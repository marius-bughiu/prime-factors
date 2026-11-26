import PrimeFactors.MixedPrefixSlab
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-! Locating the integer line selected by a thin strip on a translated lattice. -/

namespace PrimeFactors.MixedPrefixLine

/-- Round the midpoint of the interval of possible integer levels. -/
noncomputable def centerLevel (offset drift span width : ℚ) : ℤ :=
  ⌊-offset - drift * span / 2 + width / 2 + 1 / 2⌋

theorem centerLevel_eq {offset drift span width t : ℚ} {k : ℤ}
    (left : 0 ≤ t) (right : t ≤ span)
    (low : 0 ≤ offset + drift * t + k)
    (high : offset + drift * t + k ≤ width)
    (narrow : width + |drift| * span < 1) :
    centerLevel offset drift span width = k := by
  have distance : |2*t-span| ≤ span := abs_le.mpr ⟨by linarith, by linarith⟩
  have spread := mul_le_mul_of_nonneg_left distance (abs_nonneg drift)
  rw [← abs_mul, abs_le] at spread
  apply Int.floor_eq_iff.mpr
  constructor <;> nlinarith only [low, high, narrow, spread.1, spread.2]

/-- Dirichlet's approximation bound, for the exact rational slope in lattice coordinates. -/
theorem weights_exist (slope : ℚ) {limit : ℕ} (positive : 0 < limit) :
    ∃ d e : ℤ, 0 < d ∧ d ≤ limit ∧ |(d : ℚ)*slope-e| ≤ 1 / ((limit : ℚ)+1) := by
  obtain ⟨e,d,hd,hl,he⟩ := Real.exists_int_int_abs_mul_sub_le (slope : ℝ) positive
  refine ⟨d,e,hd,hl,?_⟩
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact he

/-- The right hand side uses only the strip, lattice, and chosen rational approximation.
Every lattice point in the strip satisfies this same explicit linear equation. -/
theorem line_eq {B span height intercept base slope : ℚ} {m d e t z : ℤ}
    (bp : 0 < B) (dp : 0 < d) (left : 0 ≤ t) (right : (t : ℚ) ≤ span)
    (strip : let y := base + (m : ℚ)*t + B*z
             0 ≤ y - intercept + slope*t ∧ y - intercept + slope*t ≤ height)
    (narrow : d/B*height + |d*((m+slope)/B)-e| *span < 1) :
    centerLevel (d/B*(base-intercept)) (d*((m+slope)/B)-e) span (d/B*height)
      = e*t+d*z := by
  obtain ⟨lo,hi⟩ := strip
  have scale : 0 ≤ (d : ℚ)/B := div_nonneg (by exact_mod_cast dp.le) bp.le
  have identity : d/B*(base-intercept) + (d*((m+slope)/B)-e)*t + ((e*t+d*z : ℤ) : ℚ)
      = d/B*((base+(m:ℚ)*t+B*z)-intercept+slope*t) := by
    push_cast
    field_simp
    ring
  apply centerLevel_eq (by exact_mod_cast left) right _ _ narrow
  · rw [identity]
    exact mul_nonneg scale lo
  · rw [identity]
    exact mul_le_mul_of_nonneg_left hi scale

/-- A denominator at most twice the slab width makes the level interval shorter than one
when the curvature term and rational approximation together fit the public budget. -/
theorem narrow_of_weight {B span height slope : ℚ} {d e : ℤ}
    (bp : 0 < B) (lp : 0 < span) (hp : 0 ≤ height)
    (limit : (d : ℚ) ≤ 2*span) (approximation : |d*slope-e| ≤ 1/(2*span+1))
    (budget : 2*span/B*height + span/(2*span+1) < 1) :
    d/B*height + |d*slope-e| *span < 1 := by
  have size := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right limit bp.le) hp
  have error := mul_le_mul_of_nonneg_right approximation lp.le
  rw [one_div, inv_mul_eq_div] at error
  linarith only [size, error, budget]

set_option maxRecDepth 6000 in
/-- A chord centered at the public product has just one integer level even at
the larger width 2^212. For this width the +1 in Dirichlet's error bound matters. -/
theorem chord_line {B L T x₀ base : ℚ} {m d e t z : ℤ}
    (scale : B = 2^319) (span : L = 2^212) (start : B ≤ x₀)
    (tp : 0 ≤ T) (top : T ≤ 4*B^2) (dp : 0 < d) (limit : (d : ℚ) ≤ 2*L)
    (left : 0 ≤ t) (right : (t : ℚ) ≤ L)
    (product : let y := base + (m : ℚ)*t+B*z
               T ≤ (x₀+t)*y ∧ (x₀+t)*y ≤ T+1/2)
    (approximation : let slope := T/(x₀*(x₀+L))
                     |d*((m+slope)/B)-e| ≤ 1/(2*L+1)) :
    let slope := T/(x₀*(x₀+L))
    let intercept := T/x₀ - L^2/B
    let height := (L^2+1/2)/B
    centerLevel (d/B*(base-intercept)) (d*((m+slope)/B)-e) L (d/B*height)
      = e*t+d*z := by
  have bp : 0<B := by rw [scale]; positivity
  have lp : 0<L := by rw [span]; positivity
  have xp := bp.trans_le start
  have last : 0<x₀+L := add_pos xp lp
  have area := mul_pos xp last
  let y := base + (m : ℚ)*t+B*z
  have lo : T ≤ (x₀+t)*y := product.1
  have hi : (x₀+t)*y ≤ T+1/2 := product.2
  have tl : (0:ℚ) ≤ t := by exact_mod_cast left
  have ⟨under,over⟩ := MixedPrefixSlab.chord_strip (L:=L) bp start tp top
    (show x₀ ≤ x₀+t by linarith only [tl]) (add_le_add_left right x₀) lo hi
  let A := x₀*(x₀+L)
  have pos : 0 < B*A := mul_pos bp area
  let v := y - (T/x₀ - L^2/B) + T/A*t
  have identity : B*A*v = MixedPrefixSlab.chordError B L T x₀ (x₀+t) y + A*L^2 := by
    dsimp [A,v,MixedPrefixSlab.chordError]
    field_simp
    ring
  apply line_eq bp dp left right
  · change 0 ≤ v ∧ v ≤ (L^2+1/2)/B
    constructor
    · apply nonneg_of_mul_nonneg_right _ pos
      rw [identity]
      dsimp only [A]
      linarith only [under]
    · apply le_of_mul_le_mul_left (a:=B*A) _ pos
      rw [identity]
      have scaled : B*A*((L^2+1/2)/B) = A*(L^2+1/2) := by field_simp; ring
      rw [scaled]
      dsimp only [A]
      linarith only [over]
  · apply narrow_of_weight (height := (L^2+1/2)/B) bp lp (by positivity) limit approximation
    rw [scale,span]
    decide +kernel

end PrimeFactors.MixedPrefixLine
