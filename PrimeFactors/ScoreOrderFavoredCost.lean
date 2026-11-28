import PrimeFactors.ScoreSumOrder

/-! Search work at a favored target under the location-and-residue score.
The comparisons use actual prefix cardinalities in the public factor-width
window. No distributional optimality assumption enters the bounds. -/

open private PrimeFactors.GlobalSumOrderCost.inGroup PrimeFactors.GlobalSumOrderCost.cover
  PrimeFactors.GlobalSumOrderCost.group_block PrimeFactors.GlobalSumOrderCost.count_block
  from PrimeFactors.GlobalSumOrderCost
open private PrimeFactors.FactorSumPrefixCost.whole_blocks from PrimeFactors.FactorSumPrefixCost
open private PrimeFactors.FavoredSumWork.marks_same from PrimeFactors.FavoredSumWork
open private PrimeFactors.ProductDeficitBand.left_cap from PrimeFactors.ProductDeficitBand

namespace PrimeFactors.ScoreOrderFavoredCost

open Finset PeriodicSumRank FactorSumPrefixCost ScoreSumOrder
open FullRangeResidueEstimates
open WideResiduePrimeSupply (B)
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

/-- An ordinary candidate ahead of a favored target advances at most
17/100 as far from the lower endpoint. Its discriminant is penalized
by the exact squared weight ratio 25/4. -/
theorem ordinary_distance {n lo t s : ℕ} (pos : 0<lo) (base : 4*n≤lo^2)
    (lt' : lo≤t) (ls : lo≤s) (shape : 8*s≤9*lo)
    (target : favored (n%100) (s%100)=true) (ordinary : favored (n%100) (t%100)=false)
    (ahead : before n t s) : 100*(t-lo)≤17*(s-lo) := by
  have scores := key_le ahead
  simp only [key,target,ordinary,Bool.false_eq_true,if_false,if_true] at scores
  have tsq := Nat.sub_add_cancel (base.trans (Nat.pow_le_pow_left lt' 2))
  have ssq := Nat.sub_add_cancel (base.trans (Nat.pow_le_pow_left ls 2))
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le lt'
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le ls
  rw [Nat.add_sub_cancel_left,Nat.add_sub_cancel_left]
  have little : 8*b≤lo := by omega
  apply Nat.le_of_mul_le_mul_right (c:=lo) _ pos
  nlinarith only [scores,tsq,ssq,base,Nat.mul_le_mul_right b little,Nat.zero_le (a^2)]

/-- Balanced factors place the true sum close enough to twice the square
root of the product for the preceding location bound to apply. -/
theorem balanced_shape {p q : ℕ} (order : p≤q) (balanced : q≤2*p) :
    8*(p+q)≤9*ceilSqrt (4*(p*q)) := by
  have shape : 2*(p+q)^2≤9*(p*q) := by
    zify at order balanced ⊢
    nlinarith only [mul_nonneg (by linarith : (0:ℤ)≤2*p-q) (by linarith : (0:ℤ)≤2*q-p)]
  have root := ceilSqrt_le_iff.mp (le_refl (ceilSqrt (4*(p*q))))
  apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
  nlinarith only [shape,root,Nat.zero_le (p*q)]

private theorem group_bound {n lo width : ℕ} (square : n%5=1 ∨ n%5=4) (f : Bool) :
    ((Ico lo (lo+width+1)).filter (PrimeFactors.GlobalSumOrderCost.inGroup n f)).card ≤
      (if f then 2 else 5)*(width/100+1) := by
  apply PrimeFactors.GlobalSumOrderCost.cover _ (fun a => PrimeFactors.GlobalSumOrderCost.group_block square a f)
  omega

private theorem ascending_lower {n lo s : ℕ} (square : n%5=1 ∨ n%5=4) (low : lo≤s) :
    7*((s-lo)/100)≤(passingPrefix n lo s).card := by
  let k := (s-lo)/100
  have inside : lo+100*k≤s+1 := by dsimp [k]; omega
  have size := card_le_card (filter_subset_filter (fun t => passes (n%100) (t%100)=true)
    (Ico_subset_Ico_right (a:=lo) inside))
  rw [PrimeFactors.FactorSumPrefixCost.whole_blocks _ 7 (PrimeFactors.GlobalSumOrderCost.count_block square)] at size
  exact size

/-- After 65,536 units of sum distance, at most 41% of the ascending
square tests are needed if the target is favored. -/
theorem distant_bound {n lo hi s : ℕ} (square : n%5=1 ∨ n%5=4) (pos : 0<lo)
    (base : 4*n≤lo^2) (far : lo+65536≤s) (shape : 8*s≤9*lo)
    (target : favored (n%100) (s%100)=true) :
    100*(ScoreSumOrder.«prefix» n lo hi s).card≤41*(passingPrefix n lo s).card := by
  let S := ScoreSumOrder.«prefix» n lo hi s
  let d := s-lo
  let limit := (17*d)/100
  let mark (t : ℕ) := favored (n%100) (t%100)=true
  have low : lo≤s := by omega
  have early : S.filter mark⊆(Ico lo (lo+d+1)).filter (PrimeFactors.GlobalSumOrderCost.inGroup n true) := by
    intro t ht
    obtain ⟨inside,flag⟩ := mem_filter.mp ht
    obtain ⟨⟨l,_⟩,pass,ahead⟩ := mem_prefix.mp inside
    have le := (same_group (flag.trans target.symm)).mp ahead
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨l,by dsimp [d]; omega⟩,pass,flag⟩
  have short : S.filter (fun t => ¬mark t)⊆
      (Ico lo (lo+limit+1)).filter (PrimeFactors.GlobalSumOrderCost.inGroup n false) := by
    intro t ht
    obtain ⟨inside,flag⟩ := mem_filter.mp ht
    obtain ⟨⟨l,_⟩,pass,ahead⟩ := mem_prefix.mp inside
    have regular : favored (n%100) (t%100)=false := by
      cases h : favored (n%100) (t%100) <;> simp_all [mark]
    have cutoff := ordinary_distance pos base l low shape target regular ahead
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨l,by dsimp [limit,d]; omega⟩,pass,regular⟩
  have highCount := (card_le_card early).trans (group_bound square true)
  have lowCount := (card_le_card short).trans (group_bound square false)
  have size := filter_card_add_filter_neg_card_eq_card (s:=S) mark
  have minimum := ascending_lower square low
  change 100*S.card≤_
  change 7*(d/100)≤(passingPrefix n lo s).card at minimum
  change (S.filter mark).card≤2*(d/100+1) at highCount
  change (S.filter (fun t => ¬mark t)).card≤5*((17*d/100)/100+1) at lowCount
  have long : 65536≤d := by dsimp [d]; omega
  omega

/-- Both workload inequalities and the unique successful discriminant test
hold on the same pair. -/
def Work (p q A : ℕ) : Prop :=
  let n := p*q
  let s := p+q
  let lo := ceilSqrt (4*n)
  let hi := ProductDeficitBand.sumCap n A
  let ranked := ScoreSumOrder.«prefix» n lo hi s
  100*ranked.card≤41*(passingPrefix n lo s).card ∧ 2^894≤ranked.card ∧
    ranked.filter (fun t => IsSquare (t^2-4*n))={s}

theorem pointwise {p q A : ℕ} (size : 3≤A) (pl : A≤p) (pq : p<q) (qu : q<2*A)
    (pp : p.Prime) (qp : q.Prime) (sq : (p*q)%5=1 ∨ (p*q)%5=4)
    (target : favored ((p*q)%100) ((p+q)%100)=true)
    (wide : ceilSqrt (4*(p*q))+2^900≤p+q) : Work p q A := by
  let n := p*q
  let s := p+q
  let lo := ceilSqrt (4*n)
  let hi := ProductDeficitBand.sumCap n A
  let S := ScoreSumOrder.«prefix» n lo hi s
  have far : lo+65536≤s := (Nat.add_le_add_left (by decide : 65536≤2^900) _).trans wide
  have low : lo≤s := by omega
  have pos : 0<lo := by
    have root := ceilSqrt_le_iff.mp (le_refl lo)
    have positive := Nat.mul_pos (by decide : 0<4) (Nat.mul_pos pp.pos qp.pos)
    apply Nat.pos_of_ne_zero
    intro zero
    rw [zero] at root
    exact (not_le_of_gt positive) (by simpa [n] using root)
  have high : s≤hi := le_min (PrimeFactors.ProductDeficitBand.left_cap (by omega) pl (pl.trans pq.le))
    (CenteredSumQuartic.sum_upper rfl (by omega) (by omega) (by omega))
  have base := ceilSqrt_le_iff.mp (le_refl lo)
  have shape := balanced_shape pq.le (by omega : q≤2*p)
  have sub : favoredPrefix n lo s⊆S := favored_first_le high target
  exact ⟨distant_bound sq pos base far shape target,
    (FavoredSumWork.absolute_checks sq wide).trans (card_le_card sub),
    unique_hit size pl pq qu pp qp⟩

noncomputable def witnessed := MixedPrefixSample.eligible.filter
  (fun v => Work v.1 v.2 FullRangeResidueEstimates.X)

attribute [local irreducible] MixedPrefixSample.eligible witnessed FullPopulationFavoredSums.longFavored
  FullPopulationFavoredSums.favoredPairs

theorem population_subset : FullPopulationFavoredSums.longFavored⊆witnessed := by
  rintro ⟨p,q⟩ ok
  obtain ⟨pl,pq,hi,pp,qp,_,eq,wide⟩ := FullPopulationFavoredSums.mem_longFavored.mp ok
  have incl : FullPopulationFavoredSums.longFavored ⊆ MixedPrefixSample.eligible := by
    unfold FullPopulationFavoredSums.longFavored FullPopulationFavoredSums.favoredPairs
    exact (filter_subset ..).trans (filter_subset ..)
  have nz : p%5≠0 := by
    intro zero
    have bad := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) pp).mp (Nat.dvd_of_mod_eq_zero zero)
    exact ((by decide : 5<X).trans_le pl).ne bad
  obtain ⟨sq,mark⟩ := PrimeFactors.FavoredSumWork.marks_same nz eq
  rw [witnessed,mem_filter]
  exact ⟨incl ok,pointwise (by decide : 3≤X) pl pq ((show B=2*X by decide +kernel) ▸ hi) pp qp sq mark wide⟩

/-- More than 24.9% of all eligible balanced pairs satisfy the relative
and absolute bounds, with the BMOR endpoint estimate supplied. -/
theorem all_card {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    249*MixedPrefixSample.eligible.card<1000*witnessed.card :=
  (FullPopulationFavoredSums.bmor_card h).trans_le (Nat.mul_le_mul_left _ (card_le_card population_subset))

end PrimeFactors.ScoreOrderFavoredCost
