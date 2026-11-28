import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! Comparing ordered pair counts above a product threshold when only the
one-dimensional upper-tail counts are known. The two factor slots can have
different finite sets, including overlapping ones. -/
namespace PrimeFactors.ThresholdPairCount

open Finset

noncomputable def region (K : ℕ) (A B : Finset ℕ) :=
  (A ×ˢ B).filter fun z => K<z.1*z.2

noncomputable def distinctRegion (K : ℕ) (A B : Finset ℕ) :=
  (region K A B).filter fun z => z.1≠z.2

private theorem row_count (K : ℕ) (A B : Finset ℕ) :
    (region K A B).card = ∑ p∈A,(B.filter fun q => K<p*q).card := by
  rw [region,card_eq_sum_ones,sum_filter,sum_product]
  apply sum_congr rfl
  intro p _
  rw [card_eq_sum_ones,sum_filter]

private theorem swap (K : ℕ) (A B : Finset ℕ) : (region K A B).card=(region K B A).card := by
  apply card_nbij' Prod.swap Prod.swap
  · intro z hz
    obtain ⟨pair,threshold⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨mem_product.mpr (mem_product.mp pair).symm,by simpa [Nat.mul_comm] using threshold⟩
  · intro z hz
    obtain ⟨pair,threshold⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨mem_product.mpr (mem_product.mp pair).symm,by simpa [Nat.mul_comm] using threshold⟩
  all_goals intro z _; rfl

private theorem change_right {K D : ℕ} (A B C : Finset ℕ)
    (rows : ∀ p∈A, (B.filter fun q => K<p*q).card ≤ (C.filter fun q => K<p*q).card + D) :
    (region K A B).card ≤ (region K A C).card + A.card*D := by
  rw [row_count,row_count]
  simpa only [sum_add_distrib,sum_const,smul_eq_mul] using sum_le_sum rows

private theorem with_diagonal (K : ℕ) (A B : Finset ℕ) :
    (region K A B).card ≤ (distinctRegion K A B).card+A.card := by
  have upper : ((region K A B).filter fun z => z.1=z.2).card≤A.card := by
    apply card_le_card_of_injOn Prod.fst
    · intro z hz
      exact (mem_product.mp (mem_filter.mp (mem_filter.mp hz).1).1).1
    · intro x hx y hy eq
      exact Prod.ext eq (by simpa only [←(mem_filter.mp hx).2,←(mem_filter.mp hy).2] using eq)
  have parts := filter_card_add_filter_neg_card_eq_card (s:=region K A B) (fun z => z.1=z.2)
  change _ ≤ ((region K A B).filter (fun z => ¬z.1=z.2)).card + _
  omega

/-- Replacing one residue class at a time costs at most D per point visited
in the other coordinate. Dropping equal pairs costs at most U further points. -/
theorem spread {K D U : ℕ} (A B C E : Finset ℕ)
    (left : A.card≤U) (right : E.card≤U) (refLeft : C.card≤U)
    (first : ∀ p∈A, (B.filter fun q => K<p*q).card ≤ (E.filter fun q => K<p*q).card + D)
    (second : ∀ q∈E, (A.filter fun p => K<q*p).card ≤ (C.filter fun p => K<q*p).card + D) :
    (distinctRegion K A B).card ≤ (distinctRegion K C E).card + (2*D*U+U) := by
  have one := change_right A B E first
  have two := change_right E A C second
  rw [swap K E A,swap K E C] at two
  have diag := with_diagonal K C E
  have loss : (distinctRegion K A B).card ≤ (region K A B).card := card_filter_le ..
  have ad := Nat.mul_le_mul_right D left
  have ed := Nat.mul_le_mul_right D right
  rw [show 2*D*U=U*D+U*D by ring]
  omega

/-- If two subsets of size at least M have all their cross products above K,
at least M(M−1) distinct-coordinate ordered pairs survive, even if the two
subsets coincide. -/
theorem lower {K M : ℕ} {A B a b : Finset ℕ}
    (ac : M≤a.card) (bc : M≤b.card) (asub : a⊆A) (bsub : b⊆B)
    (all : ∀ p∈a, ∀ q∈b, K<p*q) : M*(M-1) ≤ (distinctRegion K A B).card := by
  obtain ⟨a',sa,ca⟩ := exists_subset_card_eq ac
  obtain ⟨b',sb,cb⟩ := exists_subset_card_eq bc
  have all' : region K a' b'=a' ×ˢ b' := by
    apply filter_eq_self.mpr
    intro z hz
    exact all _ (sa (mem_product.mp hz).1) _ (sb (mem_product.mp hz).2)
  have diag := with_diagonal K a' b'
  rw [all',card_product,ca,cb] at diag
  have sub : distinctRegion K a' b' ⊆ distinctRegion K A B := by
    intro z hz
    obtain ⟨r,ne⟩ := mem_filter.mp hz
    obtain ⟨pair,threshold⟩ := mem_filter.mp r
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr
      ⟨asub (sa (mem_product.mp pair).1),bsub (sb (mem_product.mp pair).2)⟩,threshold⟩,ne⟩
  rw [Nat.mul_sub_left_distrib,Nat.mul_one]
  exact (show M*M-M ≤ (distinctRegion K a' b').card by omega).trans (card_le_card sub)

end PrimeFactors.ThresholdPairCount
