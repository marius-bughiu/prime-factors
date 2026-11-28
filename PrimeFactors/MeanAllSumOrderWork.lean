import PrimeFactors.MeanSumOrderWork
import PrimeFactors.OtherSumGridPopulation
import PrimeFactors.AllResidueSumCost

/-! Pooled square-test counts on the entire population of distinct 1,024-bit
prime pairs with 2,048-bit product. The preferred-first order agrees with
ascending order on the two nonsquare unit product remainders modulo five. -/

namespace PrimeFactors.MeanAllSumOrderWork

open Finset
open MixedPrefixSample (eligible)
open SumGridPopulation (Label group W possible)
open OtherSumGridPopulation (other tile)
open WideResiduePrimeSupply (B)
open MeanSumOrderGeometry (Q D dHi)
open NormalizedSumWork (coord saved ascending prioritized)
open scoped Classical

open private PrimeFactors.MeanSumOrderWork.U PrimeFactors.MeanSumOrderWork.L
  PrimeFactors.MeanSumOrderWork.scale PrimeFactors.MeanSumOrderWork.scale_pos
  PrimeFactors.MeanSumOrderWork.credit PrimeFactors.MeanSumOrderWork.cost
  PrimeFactors.MeanSumOrderWork.coords PrimeFactors.MeanSumOrderWork.totals
  PrimeFactors.MeanSumOrderWork.group_bounds from PrimeFactors.MeanSumOrderWork

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
attribute [local irreducible] eligible group SumGridPopulation.grid possible other tile

private noncomputable abbrev massHi := PrimeFactors.MeanSumOrderWork.U
private noncomputable abbrev massLo := PrimeFactors.MeanSumOrderWork.L
private noncomputable abbrev scaledCost := PrimeFactors.MeanSumOrderWork.cost
private noncomputable abbrev scaledCredit := PrimeFactors.MeanSumOrderWork.credit

private theorem nonsquare_tile_cost {li : ℕ → ℝ} (bounds : PrimeGridMass.FiveEndpoints li)
    {ij : Label} (inGrid : ij∈possible) :
    (∑ v∈tile ij,scaledCost v) ≤ (2*massHi)*(10*(dHi ij.1 ij.2:ℝ)+1) := by
  have count : ((tile ij).card:ℝ)≤2*massHi := by
    have natBound := OtherSumGridPopulation.tile_upper bounds inGrid
    change _ ≤ 2*((4*(W/2826)^2:ℕ):ℝ)
    exact_mod_cast ((natBound.trans_eq (by ring : 8*(W/2826)^2=2*(4*(W/2826)^2))))
  apply SumOrderAggregation.expense _ _ count (by positivity)
  intro v hv
  obtain ⟨member,xl,xu,yl,yu⟩ := OtherSumGridPopulation.mem_tile.mp hv
  obtain ⟨valid,ns⟩ := OtherSumGridPopulation.mem_other.mp member
  have order := (SumGridPopulation.eligible_data.mp valid).2.1
  have x := PrimeFactors.MeanSumOrderWork.coords xl xu
  have y := PrimeFactors.MeanSumOrderWork.coords yl yu
  have bp : 0<(B:ℝ) := by positivity
  have sorted : coord v.1 ≤ coord v.2 := div_le_div_of_nonneg_right (by exact_mod_cast order.le) bp.le
  have box : ij∈SumGridPopulation.grid :=
    (mem_filter.mp (by simpa only [SumGridPopulation.possible] using inGrid)).1
  obtain ⟨il,jl⟩ := mem_product.mp (by simpa only [SumGridPopulation.grid] using box)
  have corner := (MeanSumOrderGeometry.cell_bounds il jl x.1 x.2 y.1 y.2 sorted).2.1
  exact AllResidueSumCost.base_units bp (by positivity) (by norm_num [Q,B]) corner
    (AllResidueSumCost.non_square_bound ns)

private theorem nonsquare_total {li : ℕ → ℝ} (bounds : PrimeGridMass.FiveEndpoints li) :
    (∑ v∈other,scaledCost v)≤2*massHi*(10*20783259569430118+5124) := by
  obtain ⟨_,d,_,k⟩ := PrimeFactors.MeanSumOrderWork.totals
  have total := SumOrderAggregation.expenses_over_cells possible
    (fun ij => ∑ v∈tile ij,scaledCost v) (fun ij => (dHi ij.1 ij.2:ℝ)) (u:=2*massHi) (c:=10)
    (fun ij hj => nonsquare_tile_cost bounds hj)
  rw [←OtherSumGridPopulation.sum_tiles] at total
  simpa only [d,k,Nat.cast_ofNat] using total

/-- The two public orders perform identical work on every nonsquare-product input. -/
theorem unchanged_on_other {p q : ℕ} (h : (p,q)∈other) :
    prioritized p q=ascending p q ∧ saved p q=0 :=
  AllResidueSumCost.unchanged (OtherSumGridPopulation.mem_other.mp h).2

/-- Both work counts include the unique successful square-discriminant test at
the true sum for every eligible pair, including the unchanged inputs. -/
theorem true_hits {p q : ℕ} (h : (p,q)∈eligible) :
    let n := p*q
    let s := p+q
    let lo := ceilSqrt (4*n)
    let hi := ProductDeficitBand.sumCap n FullRangeResidueEstimates.X
    ((FactorSumPrefixCost.passingPrefix n lo s).filter (fun t => IsSquare (t^2-4*n)))={s} ∧
    ((GlobalSumOrderCost.globalPrefix n lo hi s).filter (fun t => IsSquare (t^2-4*n)))={s} := by
  obtain ⟨pl,lt,qu,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp h
  have full : q<2*FullRangeResidueEstimates.X := (by decide : B=2*FullRangeResidueEstimates.X) ▸ qu
  exact GlobalSumOrderCost.semiprime_unique (by decide) pl lt full pp qp

/-- With BMOR's unconditional modulus-five endpoint estimates supplied, the
two complete traversals differ by more than 1/95 of the ascending square
tests when every eligible sorted pair contributes to the totals. -/
theorem pooled_square_tests {li : ℕ → ℝ} (bounds : PrimeGridMass.FiveEndpoints li) :
    95*(∑ v∈eligible,prioritized v.1 v.2)<94*(∑ v∈eligible,ascending v.1 v.2) := by
  obtain ⟨gain,loss,base⟩ := PrimeFactors.MeanSumOrderWork.group_bounds bounds
  have lower : 0<massLo := by norm_num [massLo,PrimeFactors.MeanSumOrderWork.L,W]
  have ratio : 1000*massHi≤1018*massLo := by
    norm_num [massHi,massLo,PrimeFactors.MeanSumOrderWork.U,PrimeFactors.MeanSumOrderWork.L,W]
  have squareBase : (∑ v∈group true,scaledCost v)+(∑ v∈group false,scaledCost v) ≤
      2*massHi*(7*20783259569430118+5124) := by
    linarith only [base true,base false]
  have net := AllResidueSumCost.pooled_margin lower ratio gain loss squareBase (nonsquare_total bounds)
  have zero : (∑ v∈other,scaledCredit v)=0 := by
    apply sum_eq_zero
    intro v hv
    simp only [scaledCredit,PrimeFactors.MeanSumOrderWork.credit,(unchanged_on_other hv).2,mul_zero]
  have combine (f : ℕ×ℕ → ℝ) :
      (∑ v∈group true,f v)+(∑ v∈group false,f v)+(∑ v∈other,f v)=∑ v∈eligible,f v := by
    rw [←sum_union SumGridPopulation.groups_disjoint,←sum_union OtherSumGridPopulation.other_disjoint,
      OtherSumGridPopulation.all_groups]
  have cost_eq := combine scaledCost
  have saved_eq := combine scaledCredit
  rw [zero,add_zero] at saved_eq
  change _ < 95*((∑ v∈group true,scaledCredit v)+(∑ v∈group false,scaledCredit v)) at net
  rw [cost_eq,saved_eq] at net
  simp only [scaledCredit,scaledCost,PrimeFactors.MeanSumOrderWork.credit,PrimeFactors.MeanSumOrderWork.cost,←mul_sum] at net
  have unscaled : (∑ v∈eligible,ascending v.1 v.2)<95*(∑ v∈eligible,saved v.1 v.2) := by
    apply (mul_lt_mul_iff_of_pos_left PrimeFactors.MeanSumOrderWork.scale_pos).mp
    linarith only [net]
  simp only [NormalizedSumWork.saved_eq,sum_sub_distrib] at unscaled
  linarith only [unscaled]

end PrimeFactors.MeanAllSumOrderWork
