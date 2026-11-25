import PrimeFactors.WeightSlopeCover
import PrimeFactors.MidpointWeightBudget
import PrimeFactors.AffineSlopeClasses
import PrimeFactors.StationaryRadixLimit

namespace PrimeFactors.AdaptiveWeightLimit
open Finset
set_option exponentiation.threshold 4096

/-- Width of the range of a weighted trace on the full midpoint and half-gap rectangle. -/
def rectangleWidth (H G : ℕ) (a b : ℤ) : ℕ :=
  H*(a+b).natAbs + 2*G*(a-b).natAbs

/-- Bounding both diagonals bounds both weights, regardless of their signs. -/
theorem rectangle_coefficients {H G R k : ℕ} {a b : ℤ} (pos : 0<k)
    (mid : k≤H) (gap : k≤2*G) (width : rectangleWidth H G a b < R^2) :
    a.natAbs ≤ R^2/(2*k) ∧ b.natAbs ≤ R^2/(2*k) := by
  have lower : k*((a+b).natAbs+(a-b).natAbs) ≤ rectangleWidth H G a b := by
    rw [mul_add, rectangleWidth]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ mid) (Nat.mul_le_mul_right _ gap)
  have ha := Int.natAbs_add_le (a+b) (a-b)
  rw [show a+b+(a-b)=2*a by ring,Int.natAbs_mul] at ha
  have hb := Int.natAbs_add_le (a+b) (-(a-b))
  rw [show a+b+ -(a-b)=2*b by ring,Int.natAbs_mul,Int.natAbs_neg] at hb
  have finish (x : ℤ) (cap : 2*x.natAbs ≤ (a+b).natAbs+(a-b).natAbs) :
      x.natAbs ≤ R^2/(2*k) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0<2*k)).mpr
    calc x.natAbs*(2*k) = k*(2*x.natAbs) := by ring
         _ ≤ k*((a+b).natAbs+(a-b).natAbs) := Nat.mul_le_mul_left _ cap
         _ ≤ R^2 := lower.trans width.le
  exact ⟨finish a ha,finish b hb⟩

/-- Count the exact stationary slope set as natural residue representatives. -/
theorem all_slopes {R B : ℕ} [NeZero R] (c : (ZMod R)ˣ) (small : B<R)
    (cover : ∀ s ∈ AffineSlopeClasses.slopes c, ∃ a b : ℤ, (a≠0 ∨ b≠0) ∧
      a.natAbs≤B ∧ b.natAbs≤B ∧ a*(s : ZMod R).val ≡ b [ZMOD R]) :
    R.totient ≤ (2*B^2)*Nat.card {t : (ZMod R)ˣ // t^2=1} := by
  classical
  let val (s : (ZMod R)ˣ) := (s : ZMod R).val
  have injective : Function.Injective val := fun _ _ eq => Units.ext (ZMod.val_injective R eq)
  have bound := WeightSlopeCover.unit_slopes small ((AffineSlopeClasses.slopes c).image val) (by
    intro x hx
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hx
    exact ⟨ZMod.val_lt _,(ZMod.val_coe_unit_coprime s).symm, cover s hs⟩)
  rw [card_image_of_injective _ injective] at bound
  rw [← ZMod.card_units_eq_totient R, AffineSlopeClasses.slope_count c,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Nat.mul_le_mul_right _ bound

/-- Any slope-cover bound of this form contradicts the small-radix totient
and torsion estimates when its public numerical constants satisfy the cutoff. -/
theorem excludes_at {R B k scale limit : ℕ} (pos : 0<R) (cap : R≤limit) (limitCap : limit≤2^648)
    (kp : 0<k)
    (count : R.totient ≤ 2*B^2 * 2^91) (share : B*k ≤ scale*R^2)
    (cutoff : 26*2^91*scale^2*limit^3 ≤ k^2) : False := by
  have ratio := quotientBudget_wheel_ratio pos ((cap.trans limitCap).trans (by decide +kernel))
  have upper : R*k^2 < R*(26*2^91*scale^2*R^3) := calc
    R*k^2 < (13*(2*B^2*2^91))*k^2 :=
      Nat.mul_lt_mul_of_pos_right (ratio.trans_le (Nat.mul_le_mul_left 13 count)) (pow_pos kp 2)
    _ = (26*2^91)*(B*k)^2 := by ring
    _ ≤ (26*2^91)*(scale*R^2)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left share 2)
    _ = R*(26*2^91*scale^2*R^3) := by ring
  have low := Nat.lt_of_mul_lt_mul_left upper
  have high := Nat.mul_le_mul_left (26*2^91*scale^2) (Nat.pow_le_pow_left cap 3)
  exact (not_lt_of_ge (high.trans cutoff)) low

theorem excludes {R B k scale : ℕ} (pos : 0<R) (cap : R≤2^648) (kp : 0<k)
    (count : R.totient ≤ 2*B^2 * 2^91) (share : B*k ≤ scale*R^2)
    (cutoff : 26*2^91*scale^2*((2:ℕ)^648)^3 ≤ k^2) : False :=
  excludes_at pos cap le_rfl kp count share cutoff

/-- A full adaptive one-trace search needs a larger modulus, even when every
slope can choose its own weight. This implication uses the supplied exact-group
bound for any hypothetical smaller radix. -/
theorem radix_lower_of_torsion {N R : ℕ} [NeZero R] (size : 2^2047 ≤ N) (c : (ZMod R)ˣ)
    (torsion : R ≤ 2^648 → Nat.card {t : (ZMod R)ˣ // t^2=1} ≤ 2^91)
    (cover : ∀ s ∈ AffineSlopeClasses.slopes c, ∃ a b : ℤ, (a≠0 ∨ b≠0) ∧
      a*(s : ZMod R).val ≡ b [ZMOD R] ∧
      rectangleWidth ((9*N/8).sqrt-((N-1).sqrt+1)) (N/8).sqrt a b < R^2) :
    2^648 < R := by
  by_contra! cap
  have pos := NeZero.pos R
  have low := midpoint_weight_target_ranges size
  have small : R^2/2^1020 < R := by
    apply (Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < (2:ℕ)^1020)).mpr
    rw [sq]
    exact Nat.mul_lt_mul_of_pos_left (cap.trans_lt (by decide +kernel)) pos
  have bound := all_slopes c small (by
    intro s hs
    obtain ⟨a,b,nz,rel,width⟩ := cover s hs
    have both := rectangle_coefficients (by decide +kernel : 0<(2:ℕ)^1019)
      low.1 ((show 2^1019 ≤ 2*(2:ℕ)^1022 by decide +kernel).trans (Nat.mul_le_mul_left _ low.2)) width
    rw [show (2*(2:ℕ)^1019) = 2^1020 by decide +kernel] at both
    exact ⟨a,b,nz,both.1,both.2,rel⟩)
  exact excludes (scale := 1) pos cap (by decide +kernel : 0<(2:ℕ)^1020)
    (bound.trans (Nat.mul_le_mul_left _ (torsion cap)))
    (by simpa using Nat.div_mul_le_self (R^2) (2^1020)) (by decide +kernel)

/-- Unconditional size obstruction for assigning one rectangular trace to
every product slope of a single common stationary radix. -/
theorem radix_lower {N R : ℕ} [NeZero R] (size : 2^2047 ≤ N) (c : (ZMod R)ˣ)
    (cover : ∀ s ∈ AffineSlopeClasses.slopes c, ∃ a b : ℤ, (a≠0 ∨ b≠0) ∧
      a*(s : ZMod R).val ≡ b [ZMOD R] ∧
      rectangleWidth ((9*N/8).sqrt-((N-1).sqrt+1)) (N/8).sqrt a b < R^2) :
    2^648 < R :=
  radix_lower_of_torsion size c (StationaryRadixLimit.small_radix_torsion (NeZero.pos R)) cover

/-- A bound on every slope's weights gives a lower bound on the common radix.
The first numerical condition keeps the weights smaller than the modulus.
The second compares their total capacity to the number of unit slopes. -/
theorem radix_lower_of_scaled_weights {R k scale limit : ℕ} [NeZero R] (c : (ZMod R)ˣ)
    (limitCap : limit≤2^648) (smallWeights : scale*limit<k)
    (cutoff : 26*2^91*scale^2*limit^3 ≤ k^2)
    (cover : ∀ s ∈ AffineSlopeClasses.slopes c, ∃ a b : ℤ, (a≠0 ∨ b≠0) ∧
      a*(s : ZMod R).val ≡ b [ZMOD R] ∧
      k*a.natAbs≤scale*R^2 ∧ k*b.natAbs≤scale*R^2) : limit<R := by
  by_contra! cap
  have pos := NeZero.pos R
  let B := scale*R^2/k
  have kp : 0<k := (Nat.zero_le _).trans_lt smallWeights
  have small : B<R := by
    apply (Nat.div_lt_iff_lt_mul kp).mpr
    calc scale*R^2 = R*(scale*R) := by ring
         _ < R*k := Nat.mul_lt_mul_of_pos_left
           ((Nat.mul_le_mul_left scale cap).trans_lt smallWeights) pos
  have bound := all_slopes c small (by
    intro s hs
    obtain ⟨a,b,nz,rel,ac,bc⟩ := cover s hs
    exact ⟨a,b,nz,(Nat.le_div_iff_mul_le kp).mpr (by rwa [mul_comm]),
      (Nat.le_div_iff_mul_le kp).mpr (by rwa [mul_comm]),rel⟩)
  exact excludes_at pos cap limitCap kp (bound.trans (Nat.mul_le_mul_left _
    (StationaryRadixLimit.small_radix_torsion pos (cap.trans limitCap))))
    (Nat.div_mul_le_self ..) cutoff

/-- A width bound on the full continuous curve forces a large radix. -/
theorem radix_lower_of_curved_weights {R : ℕ} [NeZero R] (c : (ZMod R)ˣ)
    (cover : ∀ s ∈ AffineSlopeClasses.slopes c, ∃ a b : ℤ, (a≠0 ∨ b≠0) ∧
      a*(s : ZMod R).val ≡ b [ZMOD R] ∧
      2^1024*a.natAbs≤17*R^2 ∧ 2^1024*b.natAbs≤17*R^2) : 2^648<R :=
  radix_lower_of_scaled_weights c le_rfl (by decide +kernel) (by decide +kernel) cover

/-- The weaker width bound forced by uniqueness at the actual residue offset still
gives a radix obstruction. -/
theorem radix_lower_of_offset_weights {R : ℕ} [NeZero R] (c : (ZMod R)ˣ)
    (cover : ∀ s ∈ AffineSlopeClasses.slopes c, ∃ a b : ℤ, (a≠0 ∨ b≠0) ∧
      a*(s : ZMod R).val ≡ b [ZMOD R] ∧
      2^1024*a.natAbs≤34*R^2 ∧ 2^1024*b.natAbs≤34*R^2) : 2^647<R :=
  radix_lower_of_scaled_weights c (by decide +kernel) (by decide +kernel) (by decide +kernel) cover

end PrimeFactors.AdaptiveWeightLimit
