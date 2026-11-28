import PrimeFactors.FiveSquareOneSumGuess
import PrimeFactors.ProductResidueRefinement
import PrimeFactors.RefinedFactorGuessLimits

/-! How often can a single guess from a finer publicly observable product
correctly identify the factor-sum remainder modulo the five prime squares?
The guess may be any function of that public observation. -/
namespace PrimeFactors.RefinedSumPrediction

open Finset
open FiveSquarePolicy (U)
open FiveSquarePrimeSupply (m)
open FiveSquareOneSumGuess (conditional peak)
open PrimeSquareSumWeights (weight)
open FiveSquareSignRanks (sign)
open private PrimeFactors.FiveSquarePolicy.change_product PrimeFactors.FiveSquarePolicy.normalize
  from PrimeFactors.FiveSquarePolicy
open private PrimeFactors.FiveSquareOneSumGuess.hit PrimeFactors.FiveSquareOneSumGuess.row
  PrimeFactors.FiveSquareOneSumGuess.pattern_mean from PrimeFactors.FiveSquareOneSumGuess
open scoped Classical
set_option maxRecDepth 4096
attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card

variable {d : ℕ} [NeZero d]
private abbrev H (d : ℕ) := (ZMod d)ˣ
abbrev Prediction (d : ℕ) := H d→ZMod m

/-- Test the guess in the labeled population. The predictor reads only the
product of the two fine residues. Actual evaluation is for measuring accuracy. -/
noncomputable def hit (div : m∣d) (predict : Prediction d) (a b : H d) : ℕ :=
  if ((ZMod.unitsMap div a:U):ZMod m)+((ZMod.unitsMap div b:U):ZMod m)=predict (a*b) then 1 else 0

private theorem rows (div : m∣d) (predict : Prediction d) (h : H d) :
    conditional (ZMod.unitsMap div h) (predict h)=
      ((∑ a : H d,hit div predict a (a⁻¹*h):ℕ):ℚ)/Fintype.card (H d) := by
  let π := ZMod.unitsMap div
  let evaluate := PrimeFactors.FiveSquareOneSumGuess.hit (fun _ => predict h)
  have pull (a : H d) : hit div predict a (a⁻¹*h)=evaluate (π a) ((π a)⁻¹*π h) := by
    simp only [hit,evaluate,PrimeFactors.FiveSquareOneSumGuess.hit,mul_inv_cancel_left,map_mul,map_inv,π]
  have transfer := ProductResidueRefinement.mean_pullback π (ZMod.unitsMap_surjective div)
    (fun a : U => (evaluate a (a⁻¹*π h):ℚ))
  rw [←Nat.cast_sum,←Nat.cast_sum,PrimeFactors.FiveSquareOneSumGuess.row] at transfer
  simp only [pull]
  simpa only [conditional,FiveSquarePolicy.unit_count.1,Nat.cast_ofNat] using transfer.symm

private theorem model (div : m∣d) (predict : Prediction d) :
    ExtendedProductCosts.uniform (hit div predict)=
      (((∑ h : H d,conditional (ZMod.unitsMap div h) (predict h))/(Fintype.card (H d):ℚ):ℚ):ℝ) := by
  unfold ExtendedProductCosts.uniform
  rw [PrimeFactors.FiveSquarePolicy.change_product]
  exact PrimeFactors.FiveSquarePolicy.normalize rfl _ _ (rows div predict)

private noncomputable def center : ℝ := 57/30638080
private noncomputable def top (u : U) : ℚ := (peak (sign u.val.val):ℚ)/3920716800

private theorem peak_mean (div : m∣d) :
    (((∑ n : H d,top (ZMod.unitsMap div n))/(Fintype.card (H d):ℚ):ℚ):ℝ)=center := by
  rw [ProductResidueRefinement.mean_pullback _ (ZMod.unitsMap_surjective div) top]
  unfold top
  rw [PrimeFactors.FiveSquareOneSumGuess.pattern_mean]
  norm_num [center]

/-- The optimum is exact in the uniform finite model even after the
product can select predictions at the finer modulus. -/
theorem modular (div : m∣d) :
    IsGreatest (Set.range fun g : Prediction d => ExtendedProductCosts.uniform (hit div g))
      (57/30638080) := by
  change IsGreatest _ center
  choose g okay using FiveSquareOneSumGuess.attains
  have same (u : U) : conditional u (g u)=top u := by rw [conditional,okay,top]
  constructor
  · refine ⟨fun h => g (ZMod.unitsMap div h),?_⟩
    change ExtendedProductCosts.uniform (hit div (fun h => g (ZMod.unitsMap div h)))=center
    rw [model]
    simpa only [same] using peak_mean div
  · rintro _ ⟨g,rfl⟩
    change ExtendedProductCosts.uniform (hit div g)≤center
    rw [model,←peak_mean div]
    exact_mod_cast div_le_div_of_nonneg_right (sum_le_sum (s:=univ) (fun n _ =>
      (FiveSquareOneSumGuess.conditional_maximum (ZMod.unitsMap div n)).2 ⟨g n,rfl⟩)) (Nat.cast_nonneg _ : (0:ℚ)≤Fintype.card (H d))

noncomputable def primeSuccess (div : m∣d) (g : Prediction d) := ExtendedProductCosts.actual (hit div g)

private theorem accuracy (div : m∣d) (low : 3≤d) (cap : d≤2^161) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints d li) (g : Prediction d) :
    |primeSuccess div g-ExtendedProductCosts.uniform (hit div g)|≤1/(2:ℝ)^146 := by
  have sym (a b : H d) : hit div g a b=hit div g b a := by
    simp only [hit,add_comm (((ZMod.unitsMap div a:U):ZMod m)),mul_comm a b]
  have bound (a b : H d) : hit div g a b≤1 := by unfold hit; split_ifs <;> decide
  simpa only [primeSuccess,Nat.cast_one] using ExtendedProductCosts.close low cap h _ sym bound

/-- All eligible distinct full-width prime products, under the explicit
endpoint estimates at the finer modulus. The optimum is over all maps
from that public residue to a single predicted coarse sum. -/
theorem actual_optimum (div : m∣d) (low : 3≤d) (cap : d≤2^161) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints d li) :
    ∃ g : Prediction d, IsGreatest (Set.range (primeSuccess div)) (primeSuccess div g) ∧
      |primeSuccess div g-57/30638080|≤1/(2:ℝ)^146 := by
  obtain ⟨⟨base,modelHit⟩,ceiling⟩ := modular div
  obtain ⟨g,_,highest⟩ := univ.exists_max_image (primeSuccess div) univ_nonempty
  have upper := (abs_le.mp (accuracy div low cap h g)).2
  have lower := (abs_le.mp (accuracy div low cap h base)).1
  change ExtendedProductCosts.uniform (hit div base)=_ at modelHit
  rw [modelHit] at lower
  have gcap := ceiling ⟨g,rfl⟩
  change ExtendedProductCosts.uniform (hit div g)≤_ at gcap
  have ge := highest base (mem_univ _)
  exact ⟨g,⟨⟨g,rfl⟩,fun y ⟨q,eq⟩ => eq ▸ highest q (mem_univ _)⟩,
    abs_le.mpr ⟨by linarith only [lower,ge],by linarith only [upper,gcap]⟩⟩

/-- One best guess after freely reading an additional 128 low product
bits succeeds on between one in 537,511 and one in 537,510 prime pairs. -/
theorem with128 {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints RefinedFactorGuessLimits.with128 li) :
    ∃ g, IsGreatest (Set.range (primeSuccess (dvd_mul_right m (2^128))))
      (primeSuccess (dvd_mul_right m (2^128)) g) ∧
      1/537511<primeSuccess (dvd_mul_right m (2^128)) g ∧ primeSuccess (dvd_mul_right m (2^128)) g<1/537510 := by
  have range : 3≤m*2^128 ∧ m*2^128≤2^161 := by
    rw [show m=7239457225 from FiveSquareGuessRanks.modulus_value]
    decide +kernel
  obtain ⟨g,best,near⟩ := actual_optimum (dvd_mul_right m (2^128)) range.1 range.2 h
  obtain ⟨lo,hi⟩ := abs_le.mp near
  exact ⟨g,best,by linarith only [lo],by linarith only [hi]⟩

end PrimeFactors.RefinedSumPrediction
