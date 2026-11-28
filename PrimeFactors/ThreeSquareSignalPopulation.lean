import PrimeFactors.ThreeSquareCountPrecision
import PrimeFactors.QuarticLocalPopulation
import PrimeFactors.ChebyshevPrimeSample

/-! Frequency of a nonzero excess in the unfiltered, signed, ordered
three-square count. The Hurwitz total-count identity identifies this event.
The prime-count estimates enter only in measuring its frequency. -/
namespace PrimeFactors.ThreeSquareSignalPopulation

open Finset ThreeSquareRadiusCounts ThreeSquareCountPrecision
open MixedPrefixSample (eligible)
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open PrimeProductRegion (K)
open PrimeResidueRankTransfer (cell)
open QuarticLocalPopulation (Units16 BmorEndpoints)
open private PrimeFactors.ThreeSquareRadiusCounts.sign_cases from PrimeFactors.ThreeSquareRadiusCounts
open private PrimeFactors.FullPopulationFavoredSums.mem_eligible from PrimeFactors.FullPopulationFavoredSums
open private PrimeFactors.QuarticLocalPopulation.bmor_cells PrimeFactors.QuarticLocalPopulation.relative
  from PrimeFactors.QuarticLocalPopulation
open private PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted from PrimeFactors.FiveSquareAllPrimeRanks
open private PrimeFactors.ExtendedProductCosts.unit_of_prime from PrimeFactors.ExtendedProductCosts

set_option exponentiation.threshold 4096
attribute [local irreducible] eligible excess cell

/-- The total departs from six times the radius precisely when a factor
is three modulo four. This uses the total-count formula alone. -/
theorem excess_iff (formula : HurwitzFormula) {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (op : Odd p) (oq : Odd q) :
    excess (p*q)≠0 ↔ p%4=3 ∨ q%4=3 := by
  have direct := excess_cases formula pp qp ne op oq
  have swapped := (excess_cases formula qp pp ne.symm oq op).2.1
  rw [Nat.mul_comm q p] at swapped
  have hp := pp.pos
  have hq := qp.pos
  rcases PrimeFactors.ThreeSquareRadiusCounts.sign_cases op with p1|p3 <;>
    rcases PrimeFactors.ThreeSquareRadiusCounts.sign_cases oq with q1|q3
  · rw [direct.1 p1 q1]; omega
  · rw [direct.2.1 p1 q3]; omega
  · rw [swapped q1 p3]; omega
  · rw [direct.2.2 p3 q3]; omega

/-- Each distinct prime pair is in increasing order. Both factors have
1024 bits and their product has 2048 bits. -/
noncomputable def signal := eligible.filter fun v => excess (v.1*v.2)≠0

private noncomputable def silent := eligible.filter fun v => ¬(v.1%4=3 ∨ v.2%4=3)

noncomputable def silentMark (a b : ZMod 16) : ℕ :=
  if ¬(a.val%4=3 ∨ b.val%4=3) then 1 else 0

/-- The 16 silent ordered unit pairs are the complement of the 48 signal
pairs in the 64 cells modulo sixteen. -/
theorem census : (∑ v : Units16,silentMark v.1 v.2)=16 ∧ Fintype.card Units16=64 := by
  decide +kernel

theorem mem_signal (formula : HurwitzFormula) {p q : ℕ} :
    (p,q)∈signal ↔ (p,q)∈eligible ∧ (p%4=3 ∨ q%4=3) := by
  rw [signal,mem_filter]
  apply and_congr_right
  intro h
  obtain ⟨lo,lt,_,pp,qp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp h
  have big := (by decide : 2<X).trans_le lo
  exact excess_iff formula pp qp lt.ne (pp.odd_of_ne_two big.ne') (qp.odd_of_ne_two (big.trans lt).ne')

private theorem silent_share :
    FiveSquareAllPrimeRanks.actual silentMark=(silent.card:ℝ)/eligible.card := by
  have eq (S : Finset (ℕ×ℕ)) : (∑ v∈S,silentMark v.1 v.2)=
      (S.filter fun v => ¬(v.1%4=3 ∨ v.2%4=3)).card := by
    simp only [silentMark,ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 4∣16),sum_boole,Nat.cast_id]
  rw [FiveSquareAllPrimeRanks.actual,eq,silent]

private theorem signal_eq (formula : HurwitzFormula) :
    signal=eligible.filter (fun v => v.1%4=3 ∨ v.2%4=3) := by
  ext ⟨p,q⟩
  rw [mem_filter,mem_signal formula]

private theorem complementary_shares {α : Type*} (S : Finset α) (P : α→Prop)
    [DecidablePred P] (nonzero : S.card≠0) :
    ((S.filter P).card:ℝ)/S.card+((S.filter (fun x => ¬P x)).card:ℝ)/S.card=1 := by
  rw [←add_div,←Nat.cast_add,filter_card_add_filter_neg_card_eq_card,div_self]
  exact_mod_cast nonzero

private theorem complement (formula : HurwitzFormula) :
    (signal.card:ℝ)/eligible.card+(silent.card:ℝ)/eligible.card=1 := by
  rw [signal_eq formula,silent]
  apply complementary_shares
  have pop := ChebyshevPrimeSample.eligible_count
  omega

private theorem close_cells (formula : HurwitzFormula) {F l u : ℕ} (lp : 0<l)
    (fp : 0<F) (scale : F*u≤(F+1)*l) (weights : ∀ v : Units16,
      l≤cell X B K (v.1.val,v.2.val) ∧ cell X B K (v.1.val,v.2.val)≤u) :
    |(signal.card:ℝ)/eligible.card-3/4|≤(1/4)/(F:ℝ) := by
  let w (v : Units16) : ℝ := cell X B K (v.1.val,v.2.val)
  let c (v : Units16) : ℝ := silentMark v.1 v.2
  have mean : (∑ v,c v)/Fintype.card Units16=(1:ℝ)/4 := by
    norm_num [c,←Nat.cast_sum,census.1,census.2]
  have sym (a b : ZMod 16) : silentMark a b=silentMark b a := by simp only [silentMark,or_comm]
  have bound : |(silent.card:ℝ)/eligible.card-1/4|≤(1/4)/(F:ℝ) := by
    rw [←silent_share,PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted silentMark sym
      (PrimeFactors.ExtendedProductCosts.unit_of_prime (by decide)),←mean]
    apply PrimeFactors.QuarticLocalPopulation.relative w c (l:=(l:ℝ)) (u:=(u:ℝ))
      (by exact_mod_cast lp) (by exact_mod_cast fp) (by exact_mod_cast scale)
    · exact fun v => ⟨Nat.cast_le.mpr (weights v).1,Nat.cast_le.mpr (weights v).2⟩
    · exact fun _ => Nat.cast_nonneg _
  have eq : (signal.card:ℝ)/eligible.card-3/4=-((silent.card:ℝ)/eligible.card-1/4) := by
    linarith only [complement formula]
  rwa [eq,abs_neg]

/-- The published unconditional modulus-16 progression estimates are
explicit premises in Lean, as is the classical Hurwitz identity. -/
theorem close_bmor (formula : HurwitzFormula) {li : ℕ→ℝ} (h : BmorEndpoints li) :
    |(signal.card:ℝ)/eligible.card-3/4|≤1/4160 := by
  obtain ⟨l,u,lp,scale,weights⟩ := PrimeFactors.QuarticLocalPopulation.bmor_cells h
  exact (close_cells formula lp (by decide : 0<1040) scale weights).trans (by norm_num)

/-- Using the stronger modulus-16 progression bounds supplied under
Dirichlet GRH, the absolute error is at most two to the negative 148. -/
theorem close_ehp (formula : HurwitzFormula) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints 16 li) :
    |(signal.card:ℝ)/eligible.card-3/4|≤1/(2:ℝ)^148 := by
  obtain ⟨l,u,lp,scale,weights⟩ := ExtendedModulusPrimeSupply.cell_bounds (by decide) (by decide) h
  exact (close_cells formula lp (by decide : 0<2^146) scale weights).trans (by norm_num)

end PrimeFactors.ThreeSquareSignalPopulation
