import PrimeFactors.MeanSumOrderGeometry
import PrimeFactors.NormalizedSumWork
import PrimeFactors.SumGridPopulation
import PrimeFactors.SumOrderAggregation

/-! Aggregate exact square-test costs of two complete elementary traversals.
Every input in the eligible square-product population contributes, including
those on which prioritizing the two singular sum remainders costs more. -/

namespace PrimeFactors.MeanSumOrderWork

open Finset
open WideResiduePrimeSupply (B)
open MeanSumOrderGeometry (Q D G dLo dHi gHi)
open SumGridPopulation (W group tile)
open NormalizedSumWork (coord saved ascending prioritized)
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

attribute [local irreducible] SumGridPopulation.group SumGridPopulation.tile SumGridPopulation.grid
  SumGridPopulation.possible SumGridPopulation.full MixedPrefixSample.eligible

private abbrev Pair := ℕ × ℕ
private noncomputable abbrev T : Finset Pair := SumGridPopulation.possible
private noncomputable abbrev I : Finset Pair := SumGridPopulation.full
private abbrev L : ℝ := ((4*(W/2851)^2:ℕ):ℝ)
private abbrev U : ℝ := ((4*(W/2826)^2:ℕ):ℝ)
private noncomputable def scale : ℝ := 100*(Q:ℝ)/(B:ℝ)
private noncomputable def credit (v : Pair) := scale*saved v.1 v.2
private noncomputable def cost (v : Pair) := scale*ascending v.1 v.2

private theorem scale_pos : 0<scale := by unfold scale; positivity
private theorem bpos : 0<(B:ℝ) := by positivity
private theorem qpos : 0≤(Q:ℝ) := by positivity
private theorem rounding : 700*(Q:ℝ)≤(B:ℝ) := by norm_num [B,Q]

private theorem coords {p i : ℕ} (lo : i*W<p) (hi : p≤(i+1)*W) :
    (i:ℝ)≤256*coord p ∧ 256*coord p ≤ (i:ℝ)+1 := by
  have bl : (B:ℝ)=256*(W:ℝ) := by norm_num [B,W]
  have a : (i:ℝ)*W≤p := by exact_mod_cast lo.le
  have b : (p:ℝ)≤((i:ℝ)+1)*W := by exact_mod_cast hi
  unfold coord
  constructor
  · rw [←mul_div_assoc,le_div_iff₀ bpos,bl]
    linarith only [mul_le_mul_of_nonneg_left a (by norm_num : (0:ℝ)≤256)]
  · rw [←mul_div_assoc,div_le_iff₀ bpos,bl]
    linarith only [mul_le_mul_of_nonneg_left b (by norm_num : (0:ℝ)≤256)]

private theorem possible_sums (f : ℕ → ℕ → ℕ) :
    (∑ v∈T,f v.1 v.2)=MeanSumOrderGeometry.sumPossible f := by
  classical
  unfold T MeanSumOrderGeometry.sumPossible SumGridPopulation.possible SumGridPopulation.grid
  rw [sum_filter,Finset.sum_product]
  simp only [MeanSumOrderGeometry.indices,MeanSumOrderGeometry.possible,
    MeanSumOrderGeometry.full,Bool.and_eq_true,decide_eq_true_eq]

private theorem full_sums (f : ℕ → ℕ → ℕ) :
    (∑ v∈I,f v.1 v.2)=MeanSumOrderGeometry.sumFull f := by
  classical
  unfold I MeanSumOrderGeometry.sumFull SumGridPopulation.full SumGridPopulation.grid
  rw [sum_filter,Finset.sum_product]
  simp only [MeanSumOrderGeometry.indices,MeanSumOrderGeometry.possible,
    MeanSumOrderGeometry.full,Bool.and_eq_true,decide_eq_true_eq]

private theorem corners {f : Bool} {ij v : Pair} (cell : ij∈T) (mem : v∈tile f ij) :
    (dLo ij.1 ij.2:ℝ)≤Q*D (coord v.1) (coord v.2) ∧
    Q*D (coord v.1) (coord v.2)≤(dHi ij.1 ij.2:ℝ) ∧
    Q*G (coord v.1) (coord v.2)≤(gHi ij.1 ij.2:ℝ) := by
  have grid : ij∈SumGridPopulation.grid := by
    unfold T SumGridPopulation.possible at cell
    exact (mem_filter.mp cell).1
  unfold SumGridPopulation.grid at grid
  obtain ⟨ijlo,ijhi⟩ := mem_product.mp grid
  obtain ⟨hm,xl,xu,yl,yu⟩ := SumGridPopulation.mem_tile.mp mem
  have pq := (SumGridPopulation.eligible_data.mp (SumGridPopulation.mem_group.mp hm).1).2.1
  have x := coords xl xu
  have y := coords yl yu
  have order : coord v.1≤coord v.2 := div_le_div_of_nonneg_right (by exact_mod_cast pq.le) bpos.le
  have box := MeanSumOrderGeometry.cell_bounds ijlo ijhi x.1 x.2 y.1 y.2 order
  exact ⟨box.1,box.2.1,box.2.2.2⟩

private theorem positive_credit {v : Pair} (h : v∈group true) : 0≤credit v := by
  obtain ⟨eligible,mark⟩ := SumGridPopulation.mem_group.mp h
  exact mul_nonneg scale_pos.le (NormalizedSumWork.favored_bound eligible mark).1

private theorem tile_credit {li : ℕ → ℝ} (h : PrimeGridMass.FiveEndpoints li) {ij : Pair}
    (cell : ij∈I) :
    L*(5*(dLo ij.1 ij.2:ℝ))≤(∑ v∈tile true ij, credit v)+U := by
  have pos := SumGridPopulation.full_subset_possible cell
  apply SumOrderAggregation.gain _ _ (by exact_mod_cast SumGridPopulation.tile_lower h cell)
    (by exact_mod_cast SumGridPopulation.tile_upper h true pos) (by positivity)
  intro v hv
  obtain ⟨eligible,mark⟩ := SumGridPopulation.mem_group.mp (SumGridPopulation.tile_subset true ij hv)
  apply SumOrderAggregation.gain_units bpos qpos (by linarith only [rounding,qpos]) (corners pos hv).1
  exact (NormalizedSumWork.favored_bound eligible mark).2.1

private theorem tile_loss {li : ℕ → ℝ} (h : PrimeGridMass.FiveEndpoints li) {ij : Pair}
    (cell : ij∈T) :
    -(∑ v∈tile false ij, credit v)≤U*(2*(gHi ij.1 ij.2:ℝ)+1) := by
  rw [←sum_neg_distrib]
  apply SumOrderAggregation.expense _ _ (by exact_mod_cast SumGridPopulation.tile_upper h false cell)
    (by positivity)
  intro v hv
  obtain ⟨eligible,mark⟩ := SumGridPopulation.mem_group.mp (SumGridPopulation.tile_subset false ij hv)
  apply SumOrderAggregation.loss_units bpos qpos (by linarith only [rounding,qpos]) (corners cell hv).2.2
  simpa only [G,neg_mul] using (NormalizedSumWork.ordinary_bound eligible mark).1

private theorem tile_cost {li : ℕ → ℝ} (h : PrimeGridMass.FiveEndpoints li) (f : Bool)
    {ij : Pair} (cell : ij∈T) :
    (∑ v∈tile f ij, cost v)≤U*(7*(dHi ij.1 ij.2:ℝ)+1) := by
  apply SumOrderAggregation.expense _ _ (by exact_mod_cast SumGridPopulation.tile_upper h f cell)
    (by positivity)
  intro v hv
  obtain ⟨eligible,mark⟩ := SumGridPopulation.mem_group.mp (SumGridPopulation.tile_subset f ij hv)
  apply SumOrderAggregation.base_units bpos qpos rounding (corners cell hv).2.1
  cases f
  · exact (NormalizedSumWork.ordinary_bound eligible mark).2
  · exact (NormalizedSumWork.favored_bound eligible mark).2.2


private theorem totals :
    (∑ j∈I,(dLo j.1 j.2:ℝ))=18546979888483033 ∧
    (∑ j∈T,(dHi j.1 j.2:ℝ))=20783259569430118 ∧
    (∑ j∈T,(gHi j.1 j.2:ℝ))=41811592525905920 ∧ T.card=5124 := by
  obtain ⟨lo,hi,_,gh,_,count⟩ := MeanSumOrderGeometry.grid_totals
  refine ⟨?_,?_,?_,?_⟩
  · exact_mod_cast (full_sums dLo).trans lo
  · exact_mod_cast (possible_sums dHi).trans hi
  · exact_mod_cast (possible_sums gHi).trans gh
  · simpa only [sum_const,nsmul_eq_mul,mul_one,Nat.cast_id] using
      (possible_sums (fun _ _ => 1)).trans count

private theorem group_bounds {li : ℕ → ℝ} (h : PrimeGridMass.FiveEndpoints li) :
    L*5*18546979888483033 ≤ (∑ v∈group true,credit v)+U*5124 ∧
    -(∑ v∈group false,credit v)≤U*(2*41811592525905920+5124) ∧
    ∀ f : Bool, (∑ v∈group f,cost v)≤U*(7*20783259569430118+5124) := by
  obtain ⟨lo,hi,gh,count⟩ := totals
  have nonneg (j : Pair) (_ : j∈T) (_ : j∉I) : 0≤∑ v∈tile true j,credit v :=
    sum_nonneg fun v hv => positive_credit (SumGridPopulation.tile_subset true j hv)
  constructor
  · have bound := SumOrderAggregation.gains_over_cells T I SumGridPopulation.full_subset_possible
      _ _ (by positivity) (fun j hj => tile_credit h hj) nonneg
    simpa only [←SumGridPopulation.sum_tiles,lo,count,Nat.cast_ofNat] using bound
  constructor
  · have upper := SumOrderAggregation.expenses_over_cells T
      (fun j => -(∑ v∈tile false j,credit v)) (fun j => (gHi j.1 j.2:ℝ)) (u:=U) (c:=2)
      (fun j hj => tile_loss h hj)
    simpa only [sum_neg_distrib,←SumGridPopulation.sum_tiles,gh,count,Nat.cast_ofNat] using upper
  · intro f
    have upper := SumOrderAggregation.expenses_over_cells T
      (fun j => ∑ v∈tile f j,cost v) (fun j => (dHi j.1 j.2:ℝ)) (u:=U) (c:=7)
      (fun j hj => tile_cost h f hj)
    simpa only [←SumGridPopulation.sum_tiles,hi,count,Nat.cast_ofNat] using upper

/-- All eligible products recognizable by their public product residue 1
or 4 modulo five, with the smaller prime listed first. -/
noncomputable def products := MixedPrefixSample.eligible.filter
  (fun v => (v.1*v.2)%5=1 ∨ (v.1*v.2)%5=4)

/-- Under the published unconditional BMOR input at modulus five, pooled
priority work is strictly below 39/40 of the pooled ascending work. -/
theorem pooled_square_tests {li : ℕ → ℝ} (h : PrimeGridMass.FiveEndpoints li) :
    40*(∑ v∈products,prioritized v.1 v.2)<39*(∑ v∈products,ascending v.1 v.2) := by
  obtain ⟨gain,loss,base⟩ := group_bounds h
  have pos : 0<L := by norm_num [L,W]
  have ratio : 1000*U≤1018*L := by norm_num [U,L,W]
  have a := SumOrderAggregation.pooled gain loss (show
      (∑ v∈group true,cost v)+(∑ v∈group false,cost v)≤2*U*(7*20783259569430118+5124) by
    linarith only [base true,base false]) (SumOrderAggregation.grid_margin pos ratio)
  have union : group true ∪ group false=products := SumGridPopulation.group_union
  rw [←sum_union SumGridPopulation.groups_disjoint,←sum_union SumGridPopulation.groups_disjoint,union] at a
  simp only [credit,cost,←mul_sum] at a
  have unscaled : (∑ v∈products,ascending v.1 v.2)<40*∑ v∈products,saved v.1 v.2 := by
    apply (mul_lt_mul_iff_of_pos_left scale_pos).mp
    linarith only [a]
  simp only [NormalizedSumWork.saved_eq,sum_sub_distrib] at unscaled
  linarith only [unscaled]

end PrimeFactors.MeanSumOrderWork
