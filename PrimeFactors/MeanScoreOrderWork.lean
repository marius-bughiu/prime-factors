import PrimeFactors.MeanAllSumOrderWork
import PrimeFactors.ScoreVsGlobal
import PrimeFactors.ScoreGridGeometry
import PrimeFactors.ScoreOrderSlowdown

/-! Compare the interleaved order directly with the earlier global
favored-first schedule. Losses on favored hits and gains on ordinary hits
are both charged to the total. -/

namespace PrimeFactors.MeanScoreOrderWork

open Finset
open SumGridPopulation (group tile possible full W)
open OtherSumGridPopulation (other)
open NormalizedSumWork (coord prioritized ascending)
open MixedPrefixSample (eligible)
open ScoreGridGeometry (globalGain globalLoss Q)
open WideResiduePrimeSupply (B)
open scoped Classical
open private PrimeFactors.MeanSumOrderWork.L PrimeFactors.MeanSumOrderWork.U
  PrimeFactors.MeanSumOrderWork.coords PrimeFactors.MeanSumOrderWork.totals
  PrimeFactors.MeanSumOrderWork.full_sums PrimeFactors.MeanSumOrderWork.possible_sums
  PrimeFactors.MeanSumOrderWork.scale PrimeFactors.MeanSumOrderWork.cost
  PrimeFactors.MeanSumOrderWork.group_bounds from PrimeFactors.MeanSumOrderWork
open private PrimeFactors.MeanAllSumOrderWork.nonsquare_total from PrimeFactors.MeanAllSumOrderWork

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
attribute [local irreducible] eligible group tile possible full SumGridPopulation.grid other

private abbrev Pair := ℕ × ℕ
private noncomputable abbrev l := PrimeFactors.MeanSumOrderWork.L
private noncomputable abbrev u := PrimeFactors.MeanSumOrderWork.U
private noncomputable def scale : ℝ := 100*(Q:ℝ)/(B:ℝ)
private noncomputable def credit (v : Pair) := scale*ScoreVsGlobal.gain v.1 v.2
private noncomputable abbrev base := PrimeFactors.MeanSumOrderWork.cost

private theorem bp : 0<(B:ℝ) := by positivity
private theorem qp : 0≤(Q:ℝ) := by positivity
private theorem scale_pos : 0<scale := by unfold scale; positivity
private theorem rounding : 2000*(Q:ℝ)≤(B:ℝ) := by norm_num [B,Q]

private theorem gain_units {low d s : ℝ} (geo : low≤(Q:ℝ)*d)
    (work : (B:ℝ)*d-2000≤100*s) : low≤scale*s+1 := by
  have general {b q v x a : ℝ} (bpos : 0<b) (qpos : 0≤q) (allow : 2000*q≤b)
      (corner : v≤q*x) (bound : b*x-2000≤100*a) : v≤(100*q/b)*a+1 := by
    apply (mul_le_mul_iff_of_pos_right bpos).mp
    field_simp [bpos.ne']
    nlinarith only [mul_le_mul_of_nonneg_left corner bpos.le,mul_le_mul_of_nonneg_left bound qpos,allow]
  exact general bp qp rounding geo work

private theorem loss_units {high d s : ℝ} (geo : (Q:ℝ)*d≤high)
    (work : -((B:ℝ)*d)-2000≤100*s) : -(scale*s)≤high+1 := by
  apply (mul_le_mul_iff_of_pos_right bp).mp
  rw [show -(scale*s)*(B:ℝ)= -(100*(Q:ℝ)*s) by
    unfold scale
    rw [neg_mul,div_mul_eq_mul_div,div_mul_cancel₀ _ bp.ne']]
  nlinarith only [mul_le_mul_of_nonneg_left geo bp.le,mul_le_mul_of_nonneg_left work qp,rounding]

private theorem corners {f : Bool} {ij v : Pair} (cell : ij∈possible) (hv : v∈tile f ij) :
    (globalGain ij.1 ij.2:ℝ) ≤ 2*Q*max 0 (ScoreVsGlobal.E (coord v.1) (coord v.2)-
      ScoreVsGlobal.V (coord v.1) (coord v.2)) ∧
    5*Q*ScoreVsGlobal.U (coord v.1) (coord v.2)≤(globalLoss ij.1 ij.2:ℝ) := by
  unfold SumGridPopulation.possible SumGridPopulation.grid at cell
  obtain ⟨i,j⟩ := mem_product.mp (mem_filter.mp cell).1
  obtain ⟨grp,xl,xu,yl,yu⟩ := SumGridPopulation.mem_tile.mp hv
  have x := PrimeFactors.MeanSumOrderWork.coords xl xu
  have y := PrimeFactors.MeanSumOrderWork.coords yl yu
  have ord := (SumGridPopulation.eligible_data.mp (SumGridPopulation.mem_group.mp grp).1).2.1
  have sorted : coord v.1≤coord v.2 := div_le_div_of_nonneg_right (by exact_mod_cast ord.le) bp.le
  exact ScoreGridGeometry.global_corners i j x.1 x.2 y.1 y.2 sorted

private theorem tile_gain {li : ℕ → ℝ} (h : PrimeGridMass.FiveEndpoints li) {ij : Pair}
    (cell : ij∈full) :
    l*(1*(globalGain ij.1 ij.2:ℝ))≤(∑ v∈tile false ij,credit v)+u := by
  have pos := SumGridPopulation.full_subset_possible cell
  apply SumOrderAggregation.gain _ _ (by exact_mod_cast SumGridPopulation.tile_lower_group h false cell)
    (by exact_mod_cast SumGridPopulation.tile_upper h false pos) (by positivity)
  intro v hv
  obtain ⟨e,mark⟩ := SumGridPopulation.mem_group.mp (SumGridPopulation.tile_subset false ij hv)
  rw [one_mul]
  apply gain_units (d:=2*max 0 (ScoreVsGlobal.E (coord v.1) (coord v.2)-
    ScoreVsGlobal.V (coord v.1) (coord v.2)))
  · linarith only [(corners pos hv).1]
  · linarith only [(ScoreVsGlobal.ordinary_bound e mark).2]

private theorem tile_loss {li : ℕ → ℝ} (h : PrimeGridMass.FiveEndpoints li) {ij : Pair}
    (cell : ij∈possible) : -(∑ v∈tile true ij,credit v)≤u*(1*(globalLoss ij.1 ij.2:ℝ)+1) := by
  rw [←sum_neg_distrib]
  apply SumOrderAggregation.expense _ _ (by exact_mod_cast SumGridPopulation.tile_upper h true cell)
    (by positivity)
  intro v hv
  obtain ⟨e,mark⟩ := SumGridPopulation.mem_group.mp (SumGridPopulation.tile_subset true ij hv)
  rw [one_mul]
  apply loss_units (d:=5*ScoreVsGlobal.U (coord v.1) (coord v.2))
  · linarith only [(corners cell hv).2]
  · linarith only [ScoreVsGlobal.favored_bound e mark]

private theorem combine (f : Pair → ℝ) :
    (∑ v∈group true,f v)+(∑ v∈group false,f v)+(∑ v∈other,f v)=∑ v∈eligible,f v := by
  rw [←sum_union SumGridPopulation.groups_disjoint,←sum_union OtherSumGridPopulation.other_disjoint,
    OtherSumGridPopulation.all_groups]


private theorem sums :
    (∑ j∈full,(globalGain j.1 j.2:ℝ))=1852539810826416807574 ∧
    (∑ j∈possible,(globalLoss j.1 j.2:ℝ))=1102550953394375229440 := by
  obtain ⟨a,b,_⟩ := ScoreGridGeometry.grid_totals
  constructor
  · exact_mod_cast (PrimeFactors.MeanSumOrderWork.full_sums globalGain).trans a
  · exact_mod_cast (PrimeFactors.MeanSumOrderWork.possible_sums globalLoss).trans b

private theorem group_work {li : ℕ → ℝ} (h : PrimeGridMass.FiveEndpoints li) :
    l*1852539810826416807574 ≤ (∑ v∈group false,credit v)+u*5124 ∧
    -(∑ v∈group true,credit v) ≤ u*(1102550953394375229440+5124) := by
  obtain ⟨dl,dh⟩ := sums
  have count := PrimeFactors.MeanSumOrderWork.totals.2.2.2
  have nonneg (j : Pair) (_ : j∈possible) (_ : j∉full) : 0≤∑ v∈tile false j,credit v := by
    apply sum_nonneg
    intro v hv
    obtain ⟨e,opp⟩ := SumGridPopulation.mem_group.mp (SumGridPopulation.tile_subset false j hv)
    exact mul_nonneg scale_pos.le (ScoreVsGlobal.ordinary_bound e opp).1
  constructor
  · have b := SumOrderAggregation.gains_over_cells possible full SumGridPopulation.full_subset_possible
      _ _ (by positivity) (fun j hj => tile_gain h hj) nonneg
    simpa only [←SumGridPopulation.sum_tiles,dl,count,Nat.cast_ofNat,mul_one] using b
  · have b := SumOrderAggregation.expenses_over_cells possible
      (fun j => -(∑ v∈tile true j,credit v)) (fun j => (globalLoss j.1 j.2:ℝ)) (u:=u) (c:=1)
      (fun j hj => tile_loss h hj)
    simpa only [←SumGridPopulation.sum_tiles,sum_neg_distrib,dh,count,Nat.cast_ofNat,one_mul] using b

private theorem base_total {li : ℕ → ℝ} (h : PrimeGridMass.FiveEndpoints li) :
    (∑ v∈eligible,base v)≤u*(34*20783259569430118+4*5124) := by
  obtain ⟨_,_,bounds⟩ := PrimeFactors.MeanSumOrderWork.group_bounds h
  rw [←combine base]
  linarith only [bounds true,bounds false,PrimeFactors.MeanAllSumOrderWork.nonsquare_total h]

private theorem scaled_margin {f r c : ℝ}
    (a : l*1852539810826416807574≤r+u*5124)
    (b : -f≤u*(1102550953394375229440+5124))
    (upper : c≤u*(34*20783259569430118+4*5124)) : 77*65536*c<5000*(f+r) := by
  have pos : 0<l := by norm_num [l,PrimeFactors.MeanSumOrderWork.L,W]
  have ratio : 1000*u≤1018*l := by norm_num [u,l,PrimeFactors.MeanSumOrderWork.U,PrimeFactors.MeanSumOrderWork.L,W]
  linarith only [a,b,upper,pos,ratio]

/-- Switching from the global favored-first rule to the location-sensitive
order saves more than 1.54% of the original ascending test total. -/
theorem net_vs_global {li : ℕ → ℝ} (h : PrimeGridMass.FiveEndpoints li) :
    77*(∑ v∈eligible,ascending v.1 v.2) <
    5000*((∑ v∈eligible,prioritized v.1 v.2)-(∑ v∈eligible,ScoreVsGlobal.scored v.1 v.2)) := by
  obtain ⟨g,loss⟩ := group_work h
  have net := scaled_margin g loss (base_total h)
  have zero : (∑ v∈other,credit v)=0 := by
    apply sum_eq_zero
    intro v hv
    simp only [credit,ScoreVsGlobal.gain_zero hv,mul_zero]
  have same := combine credit
  rw [zero,add_zero] at same
  rw [same] at net
  have ratio : scale=65536*PrimeFactors.MeanSumOrderWork.scale := by
    unfold scale PrimeFactors.MeanSumOrderWork.scale
    rw [ScoreGridGeometry.scale_eq,Nat.cast_mul,Nat.cast_ofNat]
    ring
  simp only [base,PrimeFactors.MeanSumOrderWork.cost,credit,ScoreVsGlobal.gain_eq,
    mul_sub,sum_sub_distrib,←mul_sum] at net
  have scaled : scale*(77*(∑ v∈eligible,ascending v.1 v.2)) <
      scale*(5000*((∑ v∈eligible,prioritized v.1 v.2)-(∑ v∈eligible,ScoreVsGlobal.scored v.1 v.2))) := by
    rw [ratio] at net ⊢
    linarith only [net]
  exact (mul_lt_mul_iff_of_pos_left scale_pos).mp scaled

/-- The two comparisons use the same ascending denominator and the same
complete prime-product population. Together they give a saving above 2.59%. -/
theorem net_vs_ascending {li : ℕ → ℝ} (h : PrimeGridMass.FiveEndpoints li) :
    10000*(∑ v∈eligible,ScoreVsGlobal.scored v.1 v.2) <
      9741*(∑ v∈eligible,ascending v.1 v.2) := by
  have base : 0≤∑ v∈eligible,ascending v.1 v.2 := sum_nonneg fun v _ => by
    unfold ascending
    positivity
  linarith only [net_vs_global h,MeanAllSumOrderWork.pooled_square_tests h,base]

end PrimeFactors.MeanScoreOrderWork
