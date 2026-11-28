import PrimeFactors.RefinedSumPrediction
import PrimeFactors.ProductBandCostTransfer

/-! Predicting one sum remainder for the full-width prime population from
a residue of the public product and its 64 varying high bits. The predicted
sum is taken modulo the product of the five designated prime squares. -/

namespace PrimeFactors.BandedSumPrediction

open Finset
open FiveSquarePrimeSupply (m)
open RefinedSumPrediction (Prediction hit)
open PrimeProductBandCounts (Band)
open ExtendedModulusPrimeSupply (Endpoints)
open scoped Classical

set_option maxRecDepth 4096
attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card

variable {d : ℕ} [NeZero d]

/-- The high bits and the product modulo d jointly select the guess. -/
abbrev Policy (d : ℕ) := Band 64 → Prediction d

noncomputable def primeSuccess (div : m∣d) (P : Policy d) : ℝ :=
  ProductBandCostTransfer.actual 64 (fun i => hit div (P i))

private theorem attain_near {A : Type*} [Fintype A] [Nonempty A]
    (actual model : A→ℝ) {center err : ℝ} (upper : ∀ p,model p≤center)
    (base : ∃ p, center≤model p) (near : ∀ p, |actual p-model p|≤err) :
    ∃ p, IsGreatest (Set.range actual) (actual p) ∧ |actual p-center|≤err := by
  obtain ⟨p,_,highest⟩ := univ.exists_max_image actual univ_nonempty
  obtain ⟨q,floor⟩ := base
  have one := (abs_le.mp (near p)).2
  have two := (abs_le.mp (near q)).1
  have best := highest q (mem_univ q)
  exact ⟨p,⟨⟨p,rfl⟩,fun x ⟨r,eq⟩ => eq ▸ highest r (mem_univ r)⟩,
    abs_le.mpr ⟨by linarith only [two,floor,best],by linarith only [one,upper p]⟩⟩

/-- Even a joint predictor optimized on all eligible prime pairs has
success probability within 2⁻⁸¹ of the modular optimum. -/
theorem actual_optimum (div : m∣d) (low : 3≤d) (cap : d≤2^161) {li : ℕ→ℝ} (h : Endpoints d li) :
    ∃ P : Policy d, IsGreatest (Set.range (primeSuccess div)) (primeSuccess div P) ∧
      |primeSuccess div P-57/30638080|≤1/(2:ℝ)^81 := by
  let c (P : Policy d) (i : Band 64) := hit div (P i)
  let mixture (P : Policy d) := ProductBandCostTransfer.mixture 64 (c P)
  obtain ⟨⟨q,eq⟩,best⟩ := RefinedSumPrediction.modular div
  change ExtendedProductCosts.uniform (hit div q)=_ at eq
  apply attain_near (primeSuccess div) mixture
  · intro P
    exact ProductBandCostTransfer.mixture_le 64 low cap h (by decide) (c P)
      (fun i => best ⟨P i,rfl⟩)
  · refine ⟨fun _ => q,?_⟩
    exact ProductBandCostTransfer.le_mixture 64 low cap h (by decide) _ (fun _ => eq.ge)
  · intro P
    have sym (i : Band 64) (a b : (ZMod d)ˣ) : c P i a b=c P i b a := by
      simp only [c,hit,add_comm ((ZMod.unitsMap div a : (ZMod m)ˣ):ZMod m),mul_comm a b]
    have capOne (i : Band 64) (a b : (ZMod d)ˣ) : c P i a b≤1 := by
      unfold c hit
      split_ifs <;> decide
    simpa only [primeSuccess,mixture,c,Nat.cast_one] using
      ProductBandCostTransfer.close64 low cap h (c P) sym capOne

noncomputable def observedSuccess : Policy RefinedFactorGuessLimits.with128→ℝ :=
  primeSuccess (d:=RefinedFactorGuessLimits.with128) (dvd_mul_right m (2^128))

/-- Public observations are the low 128 product bits, its residue modulo
7,239,457,225, and its next 64 high bits after the leading one. -/
theorem with64and128 {li : ℕ→ℝ} (h : Endpoints RefinedFactorGuessLimits.with128 li) :
    ∃ P, IsGreatest (Set.range observedSuccess) (observedSuccess P) ∧
      |observedSuccess P-57/30638080|≤1/(2:ℝ)^81 ∧
      1/537511<observedSuccess P ∧ observedSuccess P<1/537510 := by
  have domain : 3≤m*2^128 ∧ m*2^128≤2^161 := by
    rw [show m=7239457225 from FiveSquareGuessRanks.modulus_value]
    decide +kernel
  obtain ⟨P,best,close⟩ := actual_optimum (d:=RefinedFactorGuessLimits.with128) (dvd_mul_right m (2^128)) domain.1 domain.2 h
  change |observedSuccess P-57/30638080|≤1/(2:ℝ)^81 at close
  obtain ⟨lo,hi⟩ := abs_le.mp close
  exact ⟨P,best,close,by linarith only [lo],by linarith only [hi]⟩

/-- The upper success limit applies to every predictor of these observations. -/
theorem every_policy {li : ℕ→ℝ} (h : Endpoints RefinedFactorGuessLimits.with128 li)
    (P : Policy RefinedFactorGuessLimits.with128) :
    observedSuccess P<1/537510 := by
  obtain ⟨_,best,_,_,hi⟩ := with64and128 h
  exact (best.2 ⟨P,rfl⟩).trans_lt hi

end PrimeFactors.BandedSumPrediction
