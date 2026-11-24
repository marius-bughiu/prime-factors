import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Abel

namespace PrimeFactors
namespace RandomRelationSigns

open scoped symmDiff

/-- Over an odd prime field, a unit square has two equipopulous root choices.
The inequality also states exactly when this construction works in another field. -/
noncomputable def rootBit {K : Type*} [Field K] (a : K) (distinct : a ≠ -a) :
    {x : K // x^2 = a^2} ≃ Bool := by
  classical
  exact {
    toFun := fun x => if x.val = a then false else true
    invFun := fun b => if b then ⟨-a, by simp⟩ else ⟨a, rfl⟩
    left_inv := by
      intro x
      apply Subtype.ext
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp x.property with h | h
      · simp [h]
      · simp [h, Ne.symm distinct]
    right_inv := by
      intro b
      cases b <;> simp [Ne.symm distinct] }

/-- CRT labels the four equally likely lifts of an observed unit square
by two local bits. The hypotheses exclude a zero root or coincident signs. -/
noncomputable def crtRootBits {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cp : p.Coprime q) (a : ZMod (p*q))
    (hp : ((ZMod.chineseRemainder cp) a).1 ≠ -((ZMod.chineseRemainder cp) a).1)
    (hq : ((ZMod.chineseRemainder cp) a).2 ≠ -((ZMod.chineseRemainder cp) a).2) :
    {x : ZMod (p*q) // x^2 = a^2} ≃ Bool × Bool := by
  let e := ZMod.chineseRemainder cp
  refine (e.toEquiv.subtypeEquiv (q := fun z => z.1^2=(e a).1^2 ∧ z.2^2=(e a).2^2)
    ?_).trans (Equiv.subtypeProdEquivProd.trans ((rootBit _ hp).prodCongr (rootBit _ hq)))
  intro x
  rw [← e.injective.eq_iff, map_pow, map_pow, Prod.ext_iff]
  rfl

/-- The local sign of a square root of one, encoded additively. -/
noncomputable def signBit {K : Type*} [Field K] (z : K) : ZMod 2 :=
  open Classical in if z = 1 then 0 else 1

theorem signBit_mul {K : Type*} [Field K] (odd : (-1 : K) ≠ 1)
    {x y : K} (hx : x^2=1) (hy : y^2=1) :
    signBit (x*y) = signBit x + signBit y := by
  rcases sq_eq_one_iff.mp hx with rfl | rfl <;>
    rcases sq_eq_one_iff.mp hy with rfl | rfl <;> simp [signBit, odd]
  decide

/-- Mixed CRT signs remain unchanged under simultaneous sign reversal. This
accounts for negative representatives in the intersections of two dependencies. -/
theorem global_neg {K L : Type*} [Field K] [Field L]
    (kp : (-1 : K) ≠ 1) (lq : (-1 : L) ≠ 1)
    {x : K} {y : L} (hx : x^2=1) (hy : y^2=1) :
    signBit (-x) + signBit (-y) = signBit x + signBit y := by
  rcases sq_eq_one_iff.mp hx with rfl | rfl <;>
    rcases sq_eq_one_iff.mp hy with rfl | rfl <;> simp [signBit, kp, lq] <;> decide

/-- A dependency splits precisely when these two field signs differ. -/
noncomputable def splitBit {K L : Type*} [Field K] [Field L] (u : K × L) : ZMod 2 :=
  signBit u.1 + signBit u.2

/-- Multiplication up to a common sign gives addition of split bits. -/
theorem splitBit_overlap {K L : Type*} [Field K] [Field L]
    (kp : (-1 : K) ≠ 1) (lq : (-1 : L) ≠ 1) {u v w : K × L}
    (hu : u^2 = 1) (hv : v^2 = 1) (hw : w^2 = 1) (overlap : u*v = w ∨ u*v = -w) :
    splitBit w = splitBit u + splitBit v := by
  have mulBits : splitBit (u*v) = splitBit u + splitBit v := by
    change signBit (u.1*v.1) + signBit (u.2*v.2) = _ + _
    rw [signBit_mul kp (congrArg Prod.fst hu) (congrArg Prod.fst hv),
      signBit_mul lq (congrArg Prod.snd hu) (congrArg Prod.snd hv)]
    unfold splitBit
    abel
  rcases overlap with h | h
  · rwa [h] at mulBits
  · rw [h] at mulBits
    exact (global_neg kp lq (congrArg Prod.fst hw) (congrArg Prod.snd hw)).symm.trans mulBits

/-- The common indices occur twice on multiplication and disappear under XOR. -/
theorem prod_overlap {ι G : Type*} [DecidableEq ι] [CommMonoid G]
    (s t : Finset ι) (f : ι → G) :
    (∏ i ∈ s, f i) * (∏ i ∈ t, f i) =
      (∏ i ∈ s ∆ t, f i) * (∏ i ∈ s ∩ t, f i)^2 := by
  rw [← Finset.prod_union_inter, symmDiff_eq_sup_sdiff_inf, sq, ← mul_assoc]
  congr 1
  exact (Finset.prod_sdiff (f := f) (show s ∩ t ⊆ s ∪ t from
    fun i hi => Finset.mem_union_left _ (Finset.mem_inter.mp hi).1)).symm

/-- Positive integer square roots compose with the absolute value of every
common representative. Its sign is the same at both CRT primes. -/
theorem root_overlap {ι : Type*} [DecidableEq ι] (s t : Finset ι) (w : ι → ℕ)
    {a b c : ℕ} (ha : a^2 = ∏ i ∈ s, w i) (hb : b^2 = ∏ i ∈ t, w i)
    (hc : c^2 = ∏ i ∈ s ∆ t, w i) :
    a*b = c*(∏ i ∈ s ∩ t, w i) := by
  apply Nat.pow_left_injective (by decide : 2 ≠ 0)
  change (a*b)^2 = (c*_)^2
  rw [mul_pow, mul_pow, ha, hb, hc, prod_overlap]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- For any fixed reference law on the dependency subspace, each prescribed
joint outcome has one free ambient sign and one free annihilating functional. -/
noncomputable def outcomeFiberEquiv (D : Subspace (ZMod 2) V)
    (reference target : Module.Dual (ZMod 2) D) :
    {s : Module.Dual (ZMod 2) V × Module.Dual (ZMod 2) V //
      D.dualRestrict (s.1 + s.2) + reference = target} ≃
      Module.Dual (ZMod 2) V × D.dualAnnihilator := by
  let lift := D.dualLift (target - reference)
  have hl : D.dualRestrict lift = target - reference := D.dualRestrict_leftInverse _
  exact {
    toFun := fun s => (s.val.1, ⟨s.val.1 + s.val.2 - lift, by
      change D.dualRestrict _ = 0
      rw [map_sub, hl, sub_eq_zero]
      exact eq_sub_iff_add_eq.mpr s.property⟩)
    invFun := fun w => ⟨(w.1, w.2.val + lift - w.1), by
      change D.dualRestrict (w.1 + (w.2.val + lift - w.1)) + reference = target
      rw [show w.1 + (w.2.val + lift - w.1) = w.2.val + lift by abel,
        map_add, (show D.dualRestrict w.2.val = 0 from w.2.property), zero_add, hl]
      abel⟩
    left_inv := by
      rintro ⟨⟨a,b⟩,h⟩
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change (a + b - lift) + lift - a = b
        abel
    right_inv := by
      rintro ⟨a,b⟩
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change a + (b.val + lift - a) - lift = b.val
        abel }

/-- With m independent pairs of local signs, exactly 2^(2m−d) assignments
give any fixed dependency functional, where d is the dimension of D. -/
theorem joint_count [FiniteDimensional (ZMod 2) V] (D : Subspace (ZMod 2) V)
    (reference target : Module.Dual (ZMod 2) D) :
    Nat.card {s : Module.Dual (ZMod 2) V × Module.Dual (ZMod 2) V //
      D.dualRestrict (s.1 + s.2) + reference = target} =
    2 ^ (2 * Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) D) := by
  rw [Nat.card_congr (outcomeFiberEquiv D reference target), Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) V),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.dualAnnihilator),
    Subspace.dual_finrank_eq, Nat.card_eq_fintype_card, ZMod.card, ← pow_add]
  congr 1
  have := Subspace.finrank_add_finrank_dualAnnihilator_eq D
  omega

/-- Once any dependency succeeds, exactly half the dependencies succeed. -/
theorem splitting_count [FiniteDimensional (ZMod 2) V]
    (f : Module.Dual (ZMod 2) V) (mixed : f ≠ 0) :
    Nat.card {v : V // f v = 1} = 2 ^ (Module.finrank (ZMod 2) V - 1) := by
  obtain ⟨w, hw⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero mixed) 1
  let e : {v : V // f v = 1} ≃ LinearMap.ker f := {
    toFun := fun v => ⟨v.val - w, by change f _ = 0; rw [map_sub, v.property, hw, sub_self]⟩
    invFun := fun k => ⟨k.val + w, by rw [map_add, (show f k.val = 0 from k.property), hw, zero_add]⟩
    left_inv := fun v => Subtype.ext (sub_add_cancel v.val w)
    right_inv := fun k => Subtype.ext (add_sub_cancel_right k.val w) }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_eq_fintype_card, ZMod.card]
  congr 1
  have := Module.Dual.finrank_ker_add_one_of_ne_zero mixed
  omega

/-- The three signed residues −1, −4, −9 modulo 65 give 64 root triples.
For 16 of them both basis dependencies give global signs. -/
theorem example_count :
    let roots := fun a : ℕ => (Finset.range 65).filter (fun x => x^2 % 65 = a)
    let triples := (roots 64 ×ˢ roots 61) ×ˢ roots 56
    triples.card = 64 ∧
      (triples.filter (fun r =>
        (r.1.1*r.1.2 % 65 = 2 ∨ r.1.1*r.1.2 % 65 = 63) ∧
        (r.1.1*r.2 % 65 = 3 ∨ r.1.1*r.2 % 65 = 62))).card = 16 := by decide

end RandomRelationSigns
end PrimeFactors
