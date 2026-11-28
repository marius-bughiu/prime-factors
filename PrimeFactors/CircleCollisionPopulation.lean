import PrimeFactors.ThreeSquareSignalPopulation
import PrimeFactors.CircleCollisionReadout

/-! Frequency of the informative norm-one circle collision count among distinct
1024-bit prime factors with a 2048-bit product. The progression estimates
used to count the population enter as external hypotheses. -/

namespace PrimeFactors.CircleCollisionPopulation

open Finset
open MixedPrefixSample (eligible)
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open PrimeProductRegion (K)
open PrimeResidueRankTransfer (cell)
open QuarticLocalPopulation (Units16 BmorEndpoints)
open private PrimeFactors.QuarticLocalPopulation.bmor_cells PrimeFactors.QuarticLocalPopulation.relative
  from PrimeFactors.QuarticLocalPopulation
open private PrimeFactors.ThreeSquareSignalPopulation.complementary_shares
  from PrimeFactors.ThreeSquareSignalPopulation
open private PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted from PrimeFactors.FiveSquareAllPrimeRanks
open private PrimeFactors.ExtendedProductCosts.unit_of_prime from PrimeFactors.ExtendedProductCosts

open private PrimeFactors.FullPopulationFavoredSums.mem_eligible from PrimeFactors.FullPopulationFavoredSums

set_option exponentiation.threshold 4096
attribute [local irreducible] eligible cell

/-- Sorted eligible prime pairs whose actual norm-one collision count departs
from four times their product. The uniform population counts each product once. -/
noncomputable def informative : Finset (ℕ × ℕ) := by
  classical
  exact eligible.filter fun v => ∃ h : NeZero (v.1*v.2), @CircleCollisionReadout.count (v.1*v.2) h ≠ 4*(v.1*v.2)

theorem mem_informative {p q : ℕ} [hn : NeZero (p*q)] :
    (p,q)∈informative ↔ (p,q)∈eligible ∧ CircleCollisionReadout.count (p*q)≠4*(p*q) := by
  classical
  rw [informative,mem_filter]
  exact and_congr_right fun _ => ⟨fun ⟨_,h⟩ => h,fun h => ⟨hn,h⟩⟩

/-- In this full-size population the count departs from its baseline exactly
when at least one factor is one modulo four. -/
theorem residue_locus :
    informative = eligible.filter (fun v => v.1%4=1 ∨ v.2%4=1) := by
  classical
  ext ⟨p,q⟩
  rw [informative,mem_filter,mem_filter]
  apply and_congr_right
  intro h
  obtain ⟨lo,lt,_,pp,qp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp h
  letI : Fact p.Prime := ⟨pp⟩
  letI : Fact q.Prime := ⟨qp⟩
  have big := (by decide : 2<X).trans_le lo
  have iff := CircleCollisionReadout.nonbaseline_iff lt.ne big.ne' (big.trans lt).ne'
  exact ⟨fun ⟨_,hc⟩ => iff.mp hc,fun hc => ⟨inferInstance,iff.mpr hc⟩⟩

/-- Indicator of the residue classes in which the count equals four times the product. -/
noncomputable def silentMark (a b : ZMod 16) : ℕ :=
  if ¬(a.val%4=1 ∨ b.val%4=1) then 1 else 0

/-- Exactly sixteen of the sixty-four ordered unit cells are silent. -/
theorem census : (∑ v : Units16,silentMark v.1 v.2)=16 ∧ Fintype.card Units16=64 := by
  decide +kernel

private theorem complementary : (informative.card:ℝ)/eligible.card +
    FiveSquareAllPrimeRanks.actual silentMark = 1 := by
  have count (S : Finset (ℕ×ℕ)) : (∑ v∈S,silentMark v.1 v.2)=
      (S.filter fun v => ¬(v.1%4=1 ∨ v.2%4=1)).card := by
    simp only [silentMark,ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 4∣16),sum_boole,Nat.cast_id]
  rw [FiveSquareAllPrimeRanks.actual,count,residue_locus]
  apply PrimeFactors.ThreeSquareSignalPopulation.complementary_shares
  have pop := ChebyshevPrimeSample.eligible_count
  omega

private theorem close_cells {F l u : ℕ} (lp : 0<l) (fp : 0<F) (scale : F*u≤(F+1)*l)
    (weights : ∀ v : Units16,
      l≤cell X B K (v.1.val,v.2.val) ∧ cell X B K (v.1.val,v.2.val)≤u) :
    |(informative.card:ℝ)/eligible.card-3/4|≤(1/4)/(F:ℝ) := by
  let w (v : Units16) : ℝ := cell X B K (v.1.val,v.2.val)
  let c (v : Units16) : ℝ := silentMark v.1 v.2
  have mean : (∑ v,c v)/Fintype.card Units16=(1:ℝ)/4 := by
    norm_num [c,←Nat.cast_sum,census.1,census.2]
  have sym (a b : ZMod 16) : silentMark a b=silentMark b a := by simp only [silentMark,or_comm]
  have bound : |FiveSquareAllPrimeRanks.actual silentMark-1/4|≤(1/4)/(F:ℝ) := by
    rw [PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted silentMark sym
      (PrimeFactors.ExtendedProductCosts.unit_of_prime (by decide)),←mean]
    apply PrimeFactors.QuarticLocalPopulation.relative w c (l:=(l:ℝ)) (u:=(u:ℝ))
      (by exact_mod_cast lp) (by exact_mod_cast fp) (by exact_mod_cast scale)
    · exact fun v => ⟨Nat.cast_le.mpr (weights v).1,Nat.cast_le.mpr (weights v).2⟩
    · exact fun _ => Nat.cast_nonneg _
  have eq : (informative.card:ℝ)/eligible.card-3/4=-(FiveSquareAllPrimeRanks.actual silentMark-1/4) := by
    linarith only [complementary]
  rwa [eq,abs_neg]

/-- With the logarithmic integral and the unconditional modulus-16
prime-count bound of Bennett, Martin, O'Bryant and Rechnitzer, Theorem 1.3,
the informative share differs from three quarters by at most 1/4160.
The analytic inputs are the fields of BmorEndpoints. -/
theorem close_bmor {li : ℕ→ℝ} (h : BmorEndpoints li) :
    |(informative.card:ℝ)/eligible.card-3/4|≤1/4160 := by
  obtain ⟨l,u,lp,scale,weights⟩ := PrimeFactors.QuarticLocalPopulation.bmor_cells h
  exact (close_cells lp (by decide : 0<1040) scale weights).trans (by norm_num)

/-- With the modulus-16 logarithmic-integral and progression estimates in
Endpoints, supplied by Ernvall-Hytönen and Palojärvi's Corollary 2 under
Dirichlet GRH, the absolute error is at most two to the negative 148. -/
theorem close_ehp {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints 16 li) :
    |(informative.card:ℝ)/eligible.card-3/4|≤1/(2:ℝ)^148 := by
  obtain ⟨l,u,lp,scale,weights⟩ := ExtendedModulusPrimeSupply.cell_bounds (by decide) (by decide) h
  exact (close_cells lp (by decide : 0<2^146) scale weights).trans (by norm_num)

end PrimeFactors.CircleCollisionPopulation
