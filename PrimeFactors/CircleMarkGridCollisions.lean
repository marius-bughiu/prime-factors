import PrimeFactors.CircleMarkRationalFrequency

/-! Exact collisions when reducing the primitive fractions of a positive square
grid at a prime exceeding the grid area. Distinct fractions can coincide after
squaring only in disjoint opposite pairs. -/

namespace PrimeFactors.CircleMarkGridCollisions

open Finset CircleMarkRationalFrequency CircleMarkTargetFrequency
open private PrimeFactors.CircleMarkRationalFrequency.point PrimeFactors.CircleMarkRationalFrequency.in_rect
  PrimeFactors.CircleMarkRationalFrequency.clear_point PrimeFactors.CircleMarkRationalFrequency.reduced_unique
  PrimeFactors.CircleMarkRationalFrequency.local_point PrimeFactors.CircleMarkRationalFrequency.fraction_eq
  PrimeFactors.CircleMarkRationalFrequency.normalize from PrimeFactors.CircleMarkRationalFrequency

open CircleMarkRationalFrequency (point in_rect clear_point reduced_unique local_point fraction_eq normalize)

/-- Modular value of a numerator-denominator pair. -/
noncomputable abbrev slope (q : ℕ) (z : ℕ × ℕ) : ZMod q := point q z

private theorem cross_lt {q h : ℕ} (room : h^2 < q) {z w : ℕ × ℕ}
    (zm : z ∈ rectangle h h) (wm : w ∈ rectangle h h) : z.1 * w.2 < q :=
  (Nat.mul_le_mul (in_rect.mp zm).1.2 (in_rect.mp wm).2.2).trans_lt (by simpa only [sq] using room)

private theorem units {q h : ℕ} [hq : Fact q.Prime] (room : h^2 < q)
    {z : ℕ × ℕ} (zm : z ∈ rectangle h h) : z.1.Coprime q ∧ z.2.Coprime q := by
  obtain ⟨⟨a,b⟩,⟨c,d⟩⟩ := in_rect.mp zm
  have bound := Nat.le_mul_of_pos_right h (c.trans_le d)
  rw [sq] at room
  exact ⟨(hq.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt a (by omega))).symm,
    (hq.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt c (by omega))).symm⟩

private theorem cross_clear {q : ℕ} (z w : ℕ × ℕ) (cop : z.2.Coprime q) :
    slope q z * ((z.2 : ZMod q) * w.2) = ((z.1 * w.2 : ℕ) : ZMod q) := by
  rw [← mul_assoc, clear_point z cop, Nat.cast_mul]

/-- Before squaring, every positive reduced fraction of the grid has its own residue. -/
theorem slope_injective {q h : ℕ} [Fact q.Prime] (room : h^2 < q) :
    Set.InjOn (slope q) (primitive h h) := by
  intro z hz w hw same
  obtain ⟨zm,zc⟩ := mem_filter.mp hz
  obtain ⟨wm,wc⟩ := mem_filter.mp hw
  have eqn : ((z.1*w.2 : ℕ) : ZMod q) = ((w.1*z.2 : ℕ) : ZMod q) := by
    rw [← cross_clear z w (units room zm).2, same, mul_comm (z.2 : ZMod q),
      cross_clear w z (units room wm).2]
  have eq := congrArg ZMod.val eqn
  rw [ZMod.val_natCast_of_lt (cross_lt room zm wm), ZMod.val_natCast_of_lt (cross_lt room wm zm)] at eq
  exact reduced_unique zc wc (in_rect.mp zm).1.1 eq

theorem opposite_iff {q h : ℕ} [Fact q.Prime] (room : h^2 < q) {z w : ℕ × ℕ}
    (zm : z ∈ rectangle h h) (wm : w ∈ rectangle h h) :
    slope q z = -slope q w ↔ z.1*w.2 + w.1*z.2 = q := by
  have zu := (units room zm).2
  have wu := (units room wm).2
  have unit := mul_ne_zero (isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime ..).mpr zu))
    (isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime ..).mpr wu))
  have clear : (slope q z + slope q w) * ((z.2 : ZMod q) * w.2) =
      ((z.1*w.2 + w.1*z.2 : ℕ) : ZMod q) := by
    rw [add_mul, cross_clear z w zu, mul_comm (z.2 : ZMod q), cross_clear w z wu, Nat.cast_add]
  rw [eq_neg_iff_add_eq_zero]
  constructor
  · intro zero
    have vanish : ((z.1*w.2 + w.1*z.2 : ℕ) : ZMod q) = 0 := by rw [← clear, zero, zero_mul]
    have pos := Nat.mul_pos (in_rect.mp zm).1.1 (in_rect.mp wm).2.1
    have small := cross_lt room zm wm
    have small' := cross_lt room wm zm
    exact Nat.eq_of_dvd_of_lt_two_mul (by omega) ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp vanish) (by omega)
  · intro total
    rw [total, ZMod.natCast_self] at clear
    exact (mul_eq_zero.mp clear).resolve_right unit

/-- A collision of two primitive squared slopes is either equality of cells or
the ordinary integer equation giving opposite modular slopes. -/
theorem collision_iff {q h : ℕ} [Fact q.Prime] (room : h^2 < q) {z w : ℕ × ℕ}
    (hz : z ∈ primitive h h) (hw : w ∈ primitive h h) :
    (slope q z)^2 = (slope q w)^2 ↔ z = w ∨ z.1*w.2 + w.1*z.2 = q := by
  rw [sq_eq_sq_iff_eq_or_eq_neg, opposite_iff room (mem_filter.mp hz).1 (mem_filter.mp hw).1]
  exact or_congr ⟨slope_injective room hz hw,fun eq => eq ▸ rfl⟩ Iff.rfl

/-- The opposite-pair equation has at most one primitive partner for each cell. -/
theorem partner_unique {q h : ℕ} [Fact q.Prime] (room : h^2 < q) {z w v : ℕ × ℕ}
    (hz : z ∈ primitive h h) (hw : w ∈ primitive h h) (hv : v ∈ primitive h h)
    (zw : z.1*w.2 + w.1*z.2 = q) (zv : z.1*v.2 + v.1*z.2 = q) : w = v := by
  have a := (opposite_iff room (mem_filter.mp hz).1 (mem_filter.mp hw).1).mpr zw
  have b := (opposite_iff room (mem_filter.mp hz).1 (mem_filter.mp hv).1).mpr zv
  exact slope_injective room hw hv (neg_inj.mp (a.symm.trans b))


/-- The larger ordinary fraction in each pair of opposite primitive slopes.
The strict cross-product comparison counts each unordered pair once. -/
noncomputable def discarded (q h : ℕ) : Finset (ℕ × ℕ) :=
  (primitive h h).filter fun z => ∃ w ∈ primitive h h,
    w.1*z.2 < z.1*w.2 ∧ z.1*w.2 + w.1*z.2 = q

private theorem square_count {q h : ℕ} [Fact q.Prime] (room : h^2 < q) :
    ((primitive h h).image (fun z => (slope q z)^2)).card + (discarded q h).card =
      (primitive h h).card := by
  let A := primitive h h
  let K := A \ discarded q h
  let f := fun z => (slope q z)^2
  have retain {z w : ℕ × ℕ} (hz : z ∈ A) (hw : w ∈ A)
      (lt : w.1*z.2 < z.1*w.2) (total : z.1*w.2 + w.1*z.2 = q) : w ∈ K := by
    apply mem_sdiff.mpr
    refine ⟨hw,?_⟩
    intro removed
    obtain ⟨v,hv,less,other⟩ := (mem_filter.mp removed).2
    have eqn := partner_unique room hw hz hv (by rwa [Nat.add_comm]) other
    subst v
    omega
  have img : A.image f = K.image f := by
    apply Subset.antisymm _ (image_subset_image sdiff_subset)
    intro x hx
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
    by_cases removed : z ∈ discarded q h
    · obtain ⟨w,hw,less,eq⟩ := (mem_filter.mp removed).2
      exact mem_image.mpr ⟨w,retain hz hw less eq,((collision_iff room hz hw).mpr (Or.inr eq)).symm⟩
    · exact mem_image_of_mem _ (mem_sdiff.mpr ⟨hz,removed⟩)
  have inj : Set.InjOn f K := by
    intro z hz w hw eq
    obtain ⟨zm,zk⟩ := mem_sdiff.mp hz
    obtain ⟨wm,wk⟩ := mem_sdiff.mp hw
    rcases (collision_iff room zm wm).mp eq with same | total
    · exact same
    · rcases lt_trichotomy (z.1*w.2) (w.1*z.2) with left|same|right
      · exact False.elim (wk (mem_filter.mpr ⟨wm,z,zm,left,by rwa [Nat.add_comm]⟩))
      · exact reduced_unique (mem_filter.mp zm).2 (mem_filter.mp wm).2
          (in_rect.mp (mem_filter.mp zm).1).1.1 same
      · exact False.elim (zk (mem_filter.mpr ⟨zm,w,wm,right,total⟩))
  change (A.image f).card + (discarded q h).card = A.card
  rw [img,card_image_of_injOn inj]
  exact card_sdiff_add_card_eq_card (filter_subset ..)

/-- Each opposite pair costs exactly one local square from the product's actual
grid menu. Repeated ordinary fractions have already been removed by taking primitive cells. -/
theorem cover_count {n q h : ℕ} [NeZero n] [Fact q.Prime] (dv : q ∣ n)
    (room : h^2 < q) (denoms : ∀ z ∈ rectangle h h, z.2.Coprime n) :
    (covered q (menu n h h)).card + (discarded q h).card = (primitive h h).card := by
  let f := fun z => (slope q z)^2
  have same : ((menu n h h).image fun x : ℕ => (x : ZMod q)^2) = (primitive h h).image f := by
    rw [menu,image_image]
    ext x
    constructor
    · intro hx
      obtain ⟨z,hz,eq⟩ := mem_image.mp hx
      obtain ⟨w,hw,ratio⟩ := normalize hz
      refine mem_image.mpr ⟨w,hw,?_⟩
      change (((point n z).val : ZMod q)^2) = x at eq
      rwa [local_point dv z (denoms z hz),
        fraction_eq (units room hz).2 (units room (mem_filter.mp hw).1).2 ratio] at eq
    · intro hx
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
      have zm := (mem_filter.mp hz).1
      exact mem_image.mpr ⟨z,zm,congrArg (fun y : ZMod q => y^2) (local_point dv z (denoms z zm))⟩
  have nz : (0 : ZMod q) ∉ (primitive h h).image f := by
    intro hx
    obtain ⟨z,hz,zero⟩ := mem_image.mp hx
    obtain ⟨num,den⟩ := units room (mem_filter.mp hz).1
    have clear := clear_point z den
    rw [show point q z = 0 from sq_eq_zero_iff.mp zero,zero_mul] at clear
    exact (isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime ..).mpr num)) clear.symm
  rw [covered,same,erase_eq_of_not_mem nz]
  exact square_count room

/-- In the census product 2257 = 37 × 61 the side is six. At 61 the fractions
5/6 and 6/5 form the grid's unique opposite pair. -/
theorem example_61 : (discarded 61 6).card = 1 ∧ (6,5) ∈ discarded 61 6 ∧
    (primitive 6 6).card = 23 := by decide

theorem census_2257 : (covered 61 (menu 2257 6 6)).card = 22 := by
  letI : Fact (Nat.Prime 61) := ⟨by decide⟩
  have count := cover_count (n:=2257) (q:=61) (h:=6) (by decide) (by decide) (by decide)
  rw [example_61.1, example_61.2.2] at count
  omega

end PrimeFactors.CircleMarkGridCollisions
