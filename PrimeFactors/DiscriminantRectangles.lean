import PrimeFactors.PhaseCharacters
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime

/-! A common odd-prime nonsquare test across different weighted discriminants.
The two sets are *distinct residues* of squared labels and scaled weight products. -/

namespace PrimeFactors.DiscriminantRectangles

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem correlation (odd : ringChar F ≠ 2) (a b : F) :
    ∑ y : F, quadraticChar F (a-y)*quadraticChar F (b-y) =
      (if a=b then (Fintype.card F : ℤ) else 0)-1 := by
  by_cases eq : a = b
  · subst b
    have point (y : F) : quadraticChar F (a-y)*quadraticChar F (a-y) =
        1 - (if y=a then 1 else 0) := by
      by_cases e : y=a
      · simp [e]
      · simpa [e, ← sq] using quadraticChar_sq_one (sub_ne_zero.mpr (Ne.symm e))
    simp_rw [point]
    simp [Finset.sum_sub_distrib]
  · rw [if_neg eq, zero_sub]
    convert phaseCharacters_shift_sum odd (a := -a) (b := -b) (fun e => eq (neg_inj.mp e)) using 1
    apply Finset.sum_congr rfl
    intro y _
    rw [← map_mul]
    congr 1
    ring

/-- Exact energy of the shifted Legendre sums on an arbitrary set of distinct rows. -/
theorem energy (odd : ringChar F ≠ 2) (X : Finset F) :
    ∑ y : F, (∑ x ∈ X, quadraticChar F (x-y))^2 =
      (X.card : ℤ)*(Fintype.card F-X.card) := by
  have row (a : F) (ha : a∈X) :
      ∑ b ∈ X, ∑ y : F, quadraticChar F (a-y)*quadraticChar F (b-y) =
        (Fintype.card F : ℤ)-X.card := by
    simp_rw [correlation odd]
    simp [Finset.sum_sub_distrib, ha]
  calc
    _ = ∑ y : F, ∑ a ∈ X, ∑ b ∈ X, quadraticChar F (a-y)*quadraticChar F (b-y) := by
      simp only [sq, Finset.sum_mul, Finset.mul_sum]
      simp only [mul_comm]
    _ = ∑ a ∈ X, ∑ b ∈ X, ∑ y : F, quadraticChar F (a-y)*quadraticChar F (b-y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_congr rfl row]; simp; ring

/-- Expander mixing for the signed local square test, centered in both variables. -/
theorem mixing (odd : ringChar F ≠ 2) (X Y : Finset F) :
    (Fintype.card F : ℤ)*(∑ y ∈ Y, ∑ x ∈ X, quadraticChar F (x-y))^2 ≤
      X.card*Y.card*((Fintype.card F : ℤ)-X.card)*(Fintype.card F-Y.card) := by
  let q : ℤ := Fintype.card F
  let a : ℤ := X.card
  let b : ℤ := Y.card
  let H (y : F) : ℤ := ∑ x ∈ X, quadraticChar F (x-y)
  let v (y : F) : ℤ := if y ∈ Y then q else 0
  have total : ∑ y, H y = 0 := by
    dsimp only [H]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro x _
    exact (Equiv.sum_comp (Equiv.subLeft x) (quadraticChar F)).trans (quadraticChar_sum_zero odd)
  have weighted (f : F → ℤ) : ∑ y, v y * f y = q * ∑ y ∈ Y, f y := by
    simp [v, ite_mul, ← Finset.mul_sum]
  have linear : ∑ y, (v y-b)*H y = q*∑ y ∈ Y, H y := by
    simp only [sub_mul, Finset.sum_sub_distrib, weighted, ← Finset.mul_sum, total, mul_zero, sub_zero]
  have square : ∑ y, (v y-b)^2 = q*b*(q-b) := by
    have identity (y : F) : (v y-b)^2 = v y*(q-2*b)+b^2 := by
      dsimp only [v]
      split_ifs <;> ring
    simp only [identity, Finset.sum_add_distrib, weighted, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ]
    change q*(b*(q-2*b))+q*b^2=_
    ring
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => v y-b) H
  rw [linear, square, show ∑ y, H y^2 = a*(q-a) from energy odd X] at cs
  have pos : 0<q := by
    change (0:ℤ)<(Fintype.card F:ℤ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  change q*(∑ y ∈ Y, H y)^2 ≤ a*b*(q-a)*(q-b)
  apply le_of_mul_le_mul_right _ pos
  nlinarith only [cs]

/-- Every entry of a rejected rectangle is a nonzero nonsquare. Duplicates in
either list have to be quotiented before using its cardinality. -/
theorem rectangle (odd : ringChar F ≠ 2) (X Y : Finset F)
    (miss : ∀ x ∈ X, ∀ y ∈ Y, ¬ IsSquare (x-y)) :
    (Fintype.card F : ℤ)*X.card*Y.card ≤
      ((Fintype.card F : ℤ)-X.card)*(Fintype.card F-Y.card) := by
  have entry (x : F) (hx : x∈X) (y : F) (hy : y∈Y) :
      quadraticChar F (x-y) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr (miss x hx y hy)
  have totals : (∑ y ∈ Y, ∑ x ∈ X, quadraticChar F (x-y)) = -((Y.card : ℤ)*X.card) := by
    trans ∑ _y ∈ Y, (-(X.card : ℤ))
    · apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_congr rfl (fun x hx => entry x hx y hy)]
      simp
    · simp
  have cs := mixing odd X Y
  rw [totals] at cs
  have Xle : (X.card : ℤ) ≤ Fintype.card F := by exact_mod_cast X.card_le_univ
  have Yle : (Y.card : ℤ) ≤ Fintype.card F := by exact_mod_cast Y.card_le_univ
  by_cases xzero : X.card=0
  · simp only [xzero,Nat.cast_zero,mul_zero,zero_mul,sub_zero]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr Yle)
  by_cases yzero : Y.card=0
  · simp only [yzero,Nat.cast_zero,mul_zero,zero_mul,sub_zero]
    exact mul_nonneg (sub_nonneg.mpr Xle) (by positivity)
  have pos : 0<(X.card : ℤ)*Y.card := by
    exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero xzero) (Nat.pos_of_ne_zero yzero)
  apply le_of_mul_le_mul_right _ pos
  nlinarith only [cs]

/-- The sets used in a weighted search are the images of its label list and
weight catalogue. Reversing signs or repeating the same scaled product leaves
the bound unchanged. -/
theorem weighted {ι : Type*} (odd : ringChar F ≠ 2) (n : F) (labels : Finset F)
    (rows : Finset ι) (a b : ι → F)
    (miss : ∀ t ∈ labels, ∀ i ∈ rows, ¬ IsSquare (t^2-4*a i*b i*n)) :
    let X := labels.image (fun t => t^2)
    let Y := rows.image (fun i => 4*a i*b i*n)
    (Fintype.card F : ℤ)*X.card*Y.card ≤
      ((Fintype.card F : ℤ)-X.card)*(Fintype.card F-Y.card) := by
  apply rectangle odd
  intro x hx y hy
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
  exact miss t ht i hi

local instance : Fact (Nat.Prime 211) := ⟨by norm_num⟩

/-- On the 211-wheel even an arbitrary set of ten distinct squared traces
cannot eliminate nineteen distinct scaled multiplier residues together. -/
theorem ten_classes (X Y : Finset (ZMod 211)) (ten : 10 ≤ X.card)
    (miss : ∀ x ∈ X, ∀ y ∈ Y, ¬ IsSquare (x-y)) : Y.card ≤ 18 := by
  have h := rectangle (F:=ZMod 211) (by rw [ZMod.ringChar_zmod_n]; decide) X Y miss
  rw [ZMod.card] at h
  by_contra! bad
  push_cast at h
  have x : (10:ℤ) ≤ X.card := by exact_mod_cast ten
  have y : (19:ℤ) ≤ Y.card := by exact_mod_cast bad
  nlinarith only [h,x,y,mul_nonneg (sub_nonneg.mpr x) (sub_nonneg.mpr y)]

end PrimeFactors.DiscriminantRectangles
