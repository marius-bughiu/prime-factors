import PrimeFactors.TraceFoldedRight
import PrimeFactors.ReciprocalWheel
import Mathlib.Data.Nat.Totient

/-! A single set of residues used for both factors. Coverage quantifies over
all unit residue pairs with the prescribed product modulo the wheel. -/

namespace PrimeFactors.DivisorResidueCover

open Finset ReciprocalWheel

variable {W : ℕ} [NeZero W]

/-- Select at least one endpoint of each locally possible pair. -/
def Covers (n : (ZMod W)ˣ) (A : Finset (ZMod W)ˣ) : Prop :=
  ∀ x y : (ZMod W)ˣ, x*y=n → x∈A ∨ y∈A

/-- The two endpoints must have opposite membership, even for a repeated residue. -/
def Separates (n : (ZMod W)ˣ) (A : Finset (ZMod W)ˣ) : Prop :=
  ∀ x y : (ZMod W)ˣ, x*y=n → (x∈A ↔ y∉A)

noncomputable def roots (n : (ZMod W)ˣ) : Finset (ZMod W)ˣ := univ.filter fun x => x^2=n

/-- Select the smaller ordinary representative in each complementary pair,
including the common representative when the two residues coincide. -/
noncomputable def selected (n : (ZMod W)ˣ) : Finset (ZMod W)ˣ :=
  univ.filter fun x => (x : ZMod W).val ≤ ((partner n x : (ZMod W)ˣ) : ZMod W).val

omit [NeZero W] in
private theorem mate_product (n x : (ZMod W)ˣ) : x * partner n x = n :=
  (product_iff_partner ..).mpr rfl

omit [NeZero W] in
private theorem fixed_iff (n x : (ZMod W)ˣ) : x=partner n x ↔ x^2=n := by
  simpa only [pow_two] using (product_iff_partner n x x).symm

omit [NeZero W] in
private theorem covers_of_separates {n : (ZMod W)ˣ} {A} (one : Separates n A) : Covers n A := by
  intro x y product
  by_cases h : y∈A
  · exact Or.inr h
  · exact Or.inl ((one x y product).mpr h)

theorem selected_covers (n : (ZMod W)ˣ) : Covers n (selected n) := by
  intro x y eq
  obtain rfl := (product_iff_partner ..).mp eq
  simpa only [selected, mem_filter, mem_univ, true_and, partner_partner] using
    (le_total (x : ZMod W).val ((partner n x : (ZMod W)ˣ) : ZMod W).val)

/-- The overlap counts exactly the excess above half the unit residues. -/
theorem cover_count {n : (ZMod W)ˣ} {A : Finset (ZMod W)ˣ} (hit : Covers n A) :
    2*A.card = W.totient + (A ∩ A.image (partner n)).card := by
  have union : A ∪ A.image (partner n) = univ := by
    apply eq_univ_of_forall
    intro x
    rcases hit x (partner n x) (mate_product ..) with h | h
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_image.mpr ⟨_,h,partner_partner ..⟩)
  have count := card_union_add_card_inter A (A.image (partner n))
  rw [union, card_univ, ZMod.card_units_eq_totient,
    card_image_of_injective A (Function.Involutive.injective (partner_partner n))] at count
  omega

private theorem roots_in_overlap {n : (ZMod W)ˣ} {A} (hit : Covers n A) :
    roots n ⊆ A ∩ A.image (partner n) := by
  intro x hx
  have fixed := (fixed_iff n x).mpr (mem_filter.mp hx).2
  have h : x∈A := (hit x x ((product_iff_partner ..).mpr fixed)).elim id id
  exact mem_inter.mpr ⟨h,mem_image.mpr ⟨x,h,fixed.symm⟩⟩

theorem selected_count (n : (ZMod W)ˣ) :
    2*(selected n).card = W.totient + (roots n).card := by
  letI : LinearOrder (ZMod W)ˣ := LinearOrder.lift' (fun x : (ZMod W)ˣ => (x : ZMod W).val)
    (fun _ _ eq => Units.ext (ZMod.val_injective W eq))
  have eq := TraceFoldedRight.orbit_count univ (partner n) (fun _ _ => mem_univ _)
    (fun x _ => partner_partner n x)
  calc
    2*(selected n).card = 2*(TraceFoldedRight.representatives univ (partner n)).card := rfl
    _ = _ := eq
    _ = _ := by
      rw [card_univ,ZMod.card_units_eq_totient]
      congr 2
      ext x
      simp only [roots,mem_filter,mem_univ,true_and,fixed_iff]

/-- Sharp minimum for all residue-only selectors, including Boolean
combinations of arbitrarily many character tests. -/
theorem minimum (n : (ZMod W)ˣ) :
    Covers n (selected n) ∧ (selected n).card = (W.totient+(roots n).card)/2 ∧
      ∀ A, Covers n A → (selected n).card≤A.card := by
  refine ⟨selected_covers n, by have := selected_count n; omega, ?_⟩
  intro A hit
  have only := card_le_card (roots_in_overlap hit)
  have a := cover_count hit
  have b := selected_count n
  omega

/-- Exactly-one separation can occur precisely when there is no square root
of the product in the wheel's unit group. -/
theorem separates_iff (n : (ZMod W)ˣ) :
    (∃ A, Separates n A) ↔ roots n = ∅ := by
  constructor
  · rintro ⟨A,one⟩
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨x,hx⟩
    have xx : x*x=n := by simpa only [← pow_two] using (mem_filter.mp hx).2
    exact iff_not_self (one x x xx)
  · intro empty
    refine ⟨selected n, ?_⟩
    intro x y product
    obtain rfl := (product_iff_partner ..).mp product
    have different : (x : ZMod W).val ≠ ((partner n x : (ZMod W)ˣ) : ZMod W).val := by
      intro eq
      have h : x∈roots n := mem_filter.mpr ⟨mem_univ _,
        (fixed_iff ..).mp (Units.ext (ZMod.val_injective W eq))⟩
      rw [empty] at h
      simp at h
    simp only [selected,mem_filter,mem_univ,true_and,partner_partner,not_le]
    omega

theorem separates_count {n : (ZMod W)ˣ} {A : Finset (ZMod W)ˣ} (one : Separates n A) :
    2*A.card = W.totient := by
  have disjoint : Disjoint A (A.image (partner n)) := by
    apply disjoint_left.mpr
    intro x hx hx'
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx'
    exact (one y (partner n y) (mate_product ..)).mp hy hx
  simpa only [disjoint_iff_inter_eq_empty.mp disjoint,card_empty,Nat.add_zero] using
    cover_count (covers_of_separates one)

/-- Modulo eight, product residue one forces all four units to be selected.
Product residue three allows the two units with representatives one and five. -/
theorem mod_eight :
    (roots (1 : (ZMod 8)ˣ)).card = 4 ∧ (selected (1 : (ZMod 8)ˣ)).card = 4 ∧
    (roots (ZMod.unitOfCoprime 3 (by decide : Nat.Coprime 3 8))).card = 0 ∧
    (selected (ZMod.unitOfCoprime 3 (by decide : Nat.Coprime 3 8))).card = 2 ∧
    (selected (ZMod.unitOfCoprime 3 (by decide : Nat.Coprime 3 8))).image
      (fun x : (ZMod 8)ˣ => (x : ZMod 8).val) = {1,5} := by
  decide +kernel

end PrimeFactors.DivisorResidueCover
