import PrimeFactors.RefinedFactorGuessLimits
import PrimeFactors.ProductBandCostTransfer

/-! Conditional mean guess rank when the product's large residue and its
leading product band may both select the order of factor-residue guesses. -/
namespace PrimeFactors.BandedFactorGuessLimits

open FiveSquarePrimeSupply (m)
open FiveSquareFactorGuessing (optimalCenter)
open ProductResidueRefinement (Policy pooled)
open RefinedFactorGuessLimits (rank)
open PrimeProductBandCounts (Band)
open private PrimeFactors.RefinedFactorGuessLimits.projected_optimum PrimeFactors.RefinedFactorGuessLimits.uniform_model
  PrimeFactors.RefinedFactorGuessLimits.transfer_min PrimeFactors.RefinedFactorGuessLimits.symmetric
  PrimeFactors.RefinedFactorGuessLimits.rank_le from PrimeFactors.RefinedFactorGuessLimits
open scoped Classical
set_option maxRecDepth 4096
attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card

variable {d : ℕ} [NeZero d]

private theorem mixed_min {I A : Type*} (single : A→ℝ) (mixed : (I→A)→ℝ) {c : ℝ}
    (least : IsLeast (Set.range single) c)
    (lower : ∀ P : I→A, (∀ i,c≤single (P i)) → c≤mixed P)
    (upper : ∀ P : I→A, (∀ i,single (P i)≤c) → mixed P≤c) :
    IsLeast (Set.range mixed) c := by
  obtain ⟨⟨q,eq⟩,best⟩ := least
  exact ⟨⟨fun _ => q,le_antisymm (upper _ (fun _ => eq.le)) (lower _ (fun _ => eq.ge))⟩,
    fun y ⟨P,hit⟩ => hit ▸ lower P (fun i => best ⟨P i,rfl⟩)⟩

private theorem row_optimum (div : m∣d) : IsLeast
    (Set.range (fun P : Policy (ZMod.unitsMap div) => ExtendedProductCosts.uniform (rank (ZMod.unitsMap div) P)))
    optimalCenter := by
  have eq (P : Policy (ZMod.unitsMap div)) :
      ExtendedProductCosts.uniform (rank (ZMod.unitsMap div) P)=(pooled (ZMod.unitsMap div) P:ℝ) :=
    PrimeFactors.RefinedFactorGuessLimits.uniform_model _ _
  simp_rw [eq]
  exact PrimeFactors.RefinedFactorGuessLimits.projected_optimum div

/-- The leading 64 varying product bits select one family of orders.
The product residue modulo d then selects the order within that family. -/
abbrev BandedPolicy (div : m∣d) := Band 64 → Policy (ZMod.unitsMap div)

noncomputable def primeMean (div : m∣d) (P : BandedPolicy div) :=
  ProductBandCostTransfer.actual 64 (fun i => rank (ZMod.unitsMap div) (P i))

/-- Existence and accuracy of the minimum over the whole family of orders. -/
def OptimalWithin (div : m∣d) (tolerance : ℝ) : Prop :=
  ∃ P : BandedPolicy div, IsLeast (Set.range (primeMean div)) (primeMean div P) ∧
    |primeMean div P-optimalCenter|≤tolerance

/-- A policy may be selected after seeing the entire population. Its
minimum averaged inclusive guess rank still lies within 2^-48 of the
original complete-residue optimum under the endpoint hypotheses. -/
theorem actual_optimum (div : m∣d) (cap : d≤2^161) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints d li) :
    OptimalWithin div (1/(2:ℝ)^48) := by
  unfold OptimalWithin
  have low : 3≤d := (show 3≤m by rw [show m=7239457225 from FiveSquareGuessRanks.modulus_value]; decide).trans
    (Nat.le_of_dvd (NeZero.pos _) div)
  let π := ZMod.unitsMap div
  let costs (P : BandedPolicy div) (i : Band 64) := rank π (P i)
  let model (P : BandedPolicy div) := ProductBandCostTransfer.mixture 64 (costs P)
  have least : IsLeast (Set.range model) optimalCenter := by
    apply mixed_min _ _ (row_optimum div)
    · intro P rows
      exact ProductBandCostTransfer.le_mixture 64 low cap h (by decide) (costs P) rows
    · intro P rows
      exact ProductBandCostTransfer.mixture_le 64 low cap h (by decide) (costs P) rows
  apply PrimeFactors.RefinedFactorGuessLimits.transfer_min model _ least
  intro P
  have bound (i : Band 64) (a b : (ZMod d)ˣ) : costs P i a b≤2^33 :=
    (PrimeFactors.RefinedFactorGuessLimits.rank_le _ _ _ _).trans
      (FiveSquarePolicy.unit_count.1.trans_le (by decide : FiveSquareFactorGuessing.T≤2^33))
  have near := ProductBandCostTransfer.close64 low cap h (costs P)
    (fun i => PrimeFactors.RefinedFactorGuessLimits.symmetric π (P i)) bound
  exact near.trans_eq (by norm_num)

/-- In particular the observed data may contain the 128 low product bits,
the original five-square product residue, and 64 varying leading bits
of the 2048-bit product. The target is either factor residue modulo m. -/
theorem with128_optimum {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints RefinedFactorGuessLimits.with128 li) :
    OptimalWithin (d:=RefinedFactorGuessLimits.with128) (dvd_mul_right m (2^128)) (1/(2:ℝ)^48) := by
  have cap : RefinedFactorGuessLimits.with128≤2^161 := by
    unfold RefinedFactorGuessLimits.with128
    rw [show m=7239457225 from FiveSquareGuessRanks.modulus_value]
    decide +kernel
  exact actual_optimum (d:=RefinedFactorGuessLimits.with128) (dvd_mul_right m (2^128)) cap h

end PrimeFactors.BandedFactorGuessLimits
