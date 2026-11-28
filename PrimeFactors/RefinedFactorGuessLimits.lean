import PrimeFactors.ProductResidueRefinement
import PrimeFactors.FiveSquareFactorGuessing
import PrimeFactors.ExtendedProductCosts

/-! Order guesses for either factor remainder modulo the five prime squares
using the entire product remainder at a finer, publicly observable modulus. -/
namespace PrimeFactors.RefinedFactorGuessLimits

open Finset FactorOrbitGuessRanks ProductResidueRefinement
open FiveSquarePolicy (U)
open FiveSquarePrimeSupply (m)
open FiveSquareFactorGuessing (optimalCenter)
open private PrimeFactors.FiveSquareFactorGuessing.label_bound PrimeFactors.FiveSquareFactorGuessing.centers
  from PrimeFactors.FiveSquareFactorGuessing
open private PrimeFactors.FiveSquarePolicy.change_product PrimeFactors.FiveSquarePolicy.normalize
  from PrimeFactors.FiveSquarePolicy
open scoped Classical
set_option maxRecDepth 4096
attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card

section FiniteModel
variable {H G : Type*} [CommGroup H] [CommGroup G] [Fintype H] [Fintype G]
variable (π : H →* G)

private noncomputable def rankAt (P : Policy π) (h a : H) := ((P h) (label (π h) (π a))).val+1
/-- The list may use both observed fine residues through their product.
Its successful guess names the projected orbit, so swapping factors preserves the rank. -/
noncomputable def rank (P : Policy π) (a b : H) := rankAt π P (a*b) a

omit [Fintype H] in
private theorem symmetric (P : Policy π) (a b : H) : rank π P a b=rank π P b a := by
  dsimp only [rank,rankAt]
  rw [mul_comm b a,(hit_iff (π (a*b)) (π b) (π a)).mpr (Or.inr (by rw [map_mul,mul_div_cancel_left]))]

omit [Fintype H] in
private theorem rank_le (P : Policy π) (a b : H) : rank π P a b≤Fintype.card G :=
  (Nat.succ_le_of_lt (Fin.isLt _)).trans (PrimeFactors.FiveSquareFactorGuessing.label_bound (π (a*b)))

omit [Fintype H] in
private theorem row (P : Policy π) (h a : H) : rank π P a (a⁻¹*h)=rankAt π P h a :=
  congrArg (fun x => rankAt π P x a) (mul_inv_cancel_left a h)

private theorem uniform_model (P : Policy π) :
    ((∑ v : H×H,rank π P v.1 v.2:ℕ):ℝ)/Fintype.card (H×H) = (pooled π P:ℝ) := by
  rw [PrimeFactors.FiveSquarePolicy.change_product]
  unfold pooled
  apply PrimeFactors.FiveSquarePolicy.normalize rfl
  intro h
  simp only [conditional,row,rankAt]
end FiniteModel

variable {d : ℕ} [NeZero d]
private theorem center : (((∑ g : U,optimum g)/(Fintype.card U:ℚ):ℚ):ℝ)=optimalCenter := by
  rw [FiveSquarePolicy.unit_count.1]
  exact PrimeFactors.FiveSquareFactorGuessing.centers.1

private theorem projected_optimum (div : m∣d) : IsLeast
    (Set.range (fun P : Policy (ZMod.unitsMap div) => (pooled (ZMod.unitsMap div) P:ℝ))) optimalCenter := by
  obtain ⟨⟨P,attains⟩,least⟩ := pooled_optimum _ (ZMod.unitsMap_surjective div)
  rw [←center]
  exact ⟨⟨P,congrArg (fun q : ℚ => (q:ℝ)) attains⟩,
    fun y ⟨Q,eq⟩ => eq ▸ (Rat.cast_le (K:=ℝ)).mpr (least ⟨Q,rfl⟩)⟩

private theorem transfer_min {A : Type*} [Fintype A] (model actual : A→ℝ) {c err : ℝ}
    (least : IsLeast (Set.range model) c) (close : ∀ p, |actual p-model p|≤err) :
    ∃ p, IsLeast (Set.range actual) (actual p) ∧ |actual p-c|≤err := by
  obtain ⟨⟨q,attains⟩,lower⟩ := least
  letI : Nonempty A := ⟨q⟩
  obtain ⟨p,_,best⟩ := univ.exists_min_image actual univ_nonempty
  have lo := (abs_le.mp (close p)).1
  have hi := (abs_le.mp (close q)).2
  have bound := lower ⟨p,rfl⟩
  have top := best q (mem_univ _)
  exact ⟨p,⟨⟨p,rfl⟩,fun y ⟨x,h⟩ => h ▸ best x (mem_univ _)⟩,
    abs_le.mpr ⟨by linarith only [lo,bound],by linarith only [top,hi,attains]⟩⟩

/-- Actual one-based guess count, averaged over the eligible distinct prime pairs. -/
noncomputable def primeMean (div : m∣d) (P : Policy (ZMod.unitsMap div)) : ℝ :=
  ExtendedProductCosts.actual (rank (ZMod.unitsMap div) P)

/-- Any observed modulus divisible by the five-square modulus and no larger
than 2^161 has the same optimal mean to the stated precision. The endpoint
hypotheses are for the fine modulus, where the policy may read the product. -/
theorem actual_optimum (div : m∣d) (cap : d≤2^161) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints d li) :
    ∃ P, IsLeast (Set.range (primeMean div)) (primeMean div P) ∧
      |primeMean div P-optimalCenter|≤1/(2:ℝ)^113 := by
  have low : 3≤d := (show 3≤m by rw [show m=7239457225 from FiveSquareGuessRanks.modulus_value]; decide).trans
    (Nat.le_of_dvd (NeZero.pos _) div)
  apply transfer_min _ _ (projected_optimum div)
  intro P
  let π := ZMod.unitsMap div
  have bound (a b : (ZMod d)ˣ) : rank π P a b≤2^33 := (rank_le _ _ _ _).trans
    (FiveSquarePolicy.unit_count.1.trans_le (by decide : FiveSquareFactorGuessing.T≤2^33))
  have eq : ExtendedProductCosts.uniform (rank π P)=(pooled π P:ℝ) := uniform_model π P
  have near := ExtendedProductCosts.close low cap h _ (symmetric π P) bound
  rw [eq] at near
  exact near.trans_eq (by norm_num)

/-- Reading the original five-square remainder and 128 additional low bits
of the product is equivalent to reading the product at this odd-times-dyadic modulus. -/
noncomputable abbrev with128 := m*2^128

theorem with128_optimum {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints with128 li) :
    ∃ P, IsLeast (Set.range (primeMean (dvd_mul_right m (2^128))))
        (primeMean (dvd_mul_right m (2^128)) P) ∧
      |primeMean (dvd_mul_right m (2^128)) P-optimalCenter|≤1/(2:ℝ)^113 := by
  refine actual_optimum _ ?_ h
  rw [show m=7239457225 from FiveSquareGuessRanks.modulus_value]
  decide +kernel

end PrimeFactors.RefinedFactorGuessLimits
