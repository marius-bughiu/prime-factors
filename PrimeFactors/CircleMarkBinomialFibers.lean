import PrimeFactors.AffinePrimeSign
import Mathlib.GroupTheory.Coset.Card

/-! The solutions of a power equation with one prescribed quadratic sign form
an empty set or a coset of a subgroup of the squares. -/
namespace PrimeFactors.CircleMarkBinomialFibers

open Finset
open scoped Classical

variable (r : ℕ) [Fact r.Prime]

private noncomputable def positiveUnits : Subgroup (ZMod r)ˣ where
  carrier := {x | quadraticChar (ZMod r) x = 1}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change quadraticChar (ZMod r) (x*y : (ZMod r)ˣ) = 1
    change quadraticChar (ZMod r) (x:ZMod r)=1 at hx
    change quadraticChar (ZMod r) (y:ZMod r)=1 at hy
    rw [Units.val_mul,map_mul,hx,hy,one_mul]
  inv_mem' := by
    intro x hx
    change quadraticChar (ZMod r) (x:ZMod r) = 1 at hx
    change quadraticChar (ZMod r) (↑(x⁻¹):(ZMod r)) = 1
    have h := map_mul (quadraticChar (ZMod r)) (x:ZMod r) (↑(x⁻¹):ZMod r)
    rw [Units.mul_inv, map_one,hx,one_mul] at h
    exact h.symm

private noncomputable def kernel (e : ℕ) : Subgroup (ZMod r)ˣ :=
  positiveUnits r ⊓ (powMonoidHom (α:=(ZMod r)ˣ) e).ker

private theorem positive_size (odd : r≠2) : Nat.card (positiveUnits r) = (r-1)/2 := by
  let f : positiveUnits r ≃ ↥(AffinePrimeSign.positive r) := {
    toFun := fun x => ⟨x.val.val,mem_filter.mpr ⟨mem_univ _,x.property⟩⟩
    invFun := fun y => by
      have c := (mem_filter.mp y.property).2
      have nz : y.val≠0 := by intro h; rw [h,quadraticChar_zero] at c; contradiction
      exact ⟨Units.mk0 y.val nz,c⟩
    left_inv := fun _ => by apply Subtype.ext; apply Units.ext; rfl
    right_inv := fun _ => rfl }
  have h := Nat.card_congr f
  have h' : Nat.card (positiveUnits r)=(AffinePrimeSign.positive r).card := h.trans (by simp)
  have count := AffinePrimeSign.positive_count r odd
  omega

/-- Nonzero field roots of the binomial, partitioned by their sign. -/
noncomputable def fiber (e : ℕ) (c : ZMod r) (s : ℤ) : Finset (ZMod r) :=
  univ.filter fun x => x^e=c ∧ quadraticChar (ZMod r) x=s

private theorem fiber_count (e : ℕ) (c : ZMod r) (s : ℤ) (sn : s≠0) :
    (fiber r e c s).card = 0 ∨ (fiber r e c s).card = Nat.card (kernel r e) := by
  classical
  by_cases empty : (fiber r e c s).Nonempty
  swap
  · exact Or.inl (card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp empty))
  obtain ⟨x,hx⟩ := empty
  have ⟨xc,xs⟩ := (mem_filter.mp hx).2
  have xn : x≠0 := by intro h; apply sn; simpa [h] using xs.symm
  let u := Units.mk0 x xn
  let f : kernel r e ≃ ↥(fiber r e c s) := {
    toFun := fun k => by
      have good : quadraticChar (ZMod r) (k.val:ZMod r)=1 := k.property.1
      have pow : k.val^e=1 := k.property.2
      have kp : (k.val:ZMod r)^e=1 := by simpa using congrArg Units.val pow
      refine ⟨(k.val:ZMod r)*x,mem_filter.mpr ⟨mem_univ _,?_,?_⟩⟩
      · rw [mul_pow,kp,one_mul,xc]
      · change quadraticChar (ZMod r) (_ * _) = s
        rw [map_mul,good,one_mul,xs]
    invFun := fun y => by
      have yc := (mem_filter.mp y.property).2.1
      have ys := (mem_filter.mp y.property).2.2
      have yn : y.val≠0 := by intro h; apply sn; simpa [h] using ys.symm
      let v := Units.mk0 y.val yn
      have ratioPow : (v/u)^e=1 := by
        rw [div_pow,div_eq_one]
        apply Units.ext
        exact yc.trans xc.symm
      have ratioSign : quadraticChar (ZMod r) (↑(v/u):ZMod r)=1 := by
        have mul : (↑(v/u):ZMod r)*x=y.val := by
          change (↑((v/u)*u):ZMod r)=_
          rw [div_mul_cancel]
          rfl
        have rel := congrArg (quadraticChar (ZMod r)) mul
        change quadraticChar (ZMod r) (_ * _) = _ at rel
        rw [map_mul,xs,ys] at rel
        exact (mul_right_cancel₀ sn) (by simpa only [one_mul] using rel)
      exact ⟨v/u,ratioSign,ratioPow⟩
    left_inv := fun k => by
      apply Subtype.ext
      apply Units.ext
      change ((Units.mk0 ((k.val:ZMod r)*x) _ / u : (ZMod r)ˣ):ZMod r) = _
      simp [u, xn]
    right_inv := fun y => by
      apply Subtype.ext
      change ((Units.mk0 y.val _ / u : (ZMod r)ˣ):ZMod r)*x=y.val
      simp [u, xn] }
  right
  have card := Nat.card_congr f
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using card.symm

/-- A nonzero difference of the positive and negative root counts divides
the number of nonzero squares, independently of the power e. -/
theorem difference_dvd (odd : r≠2) (e : ℕ) (c : ZMod r) :
    let z := ((fiber r e c 1).card:ℤ) - ((fiber r e c (-1)).card:ℤ)
    z=0 ∨ z.natAbs ∣ (r-1)/2 := by
  have sub : kernel r e ≤ positiveUnits r := inf_le_left
  have dvd := Subgroup.card_dvd_of_le sub
  rw [positive_size r odd] at dvd
  simp only [Nat.card_eq_fintype_card] at dvd
  rcases fiber_count r e c 1 (by decide) with h|h <;>
    rcases fiber_count r e c (-1) (by decide) with k|k <;>
    simp [h,k,dvd]

end PrimeFactors.CircleMarkBinomialFibers
