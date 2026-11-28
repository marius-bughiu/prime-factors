import PrimeFactors.FactorSumPrefixCost
import PrimeFactors.FullPopulationFavoredSums

/-! Counts of square-discriminant tests through the true sum in two
elementary exhaustive traversals of the same factor-width window. The
favored traversal visits its preferred residue classes first across the
entire window. The counts include the successful final test. -/

namespace PrimeFactors.FavoredSumWork

open Finset PeriodicSumRank FactorSumPrefixCost FullRangeResidueEstimates
open WideResiduePrimeSupply (B)
open PrimeProductRegion (population)
open MixedPrefixSample (eligible)
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

/-- Both work inequalities and the unique successful square test hold for
this same pair. The candidate counts are actual inclusive prefix sizes. -/
def Work (p q : ℕ) : Prop :=
  let n := p*q
  let s := p+q
  let lo := ceilSqrt (4*n)
  let ordinary := passingPrefix n lo s
  let first := favoredPrefix n lo s
  passes (n%100) (s%100)=true ∧ favored (n%100) (s%100)=true ∧
    10*first.card≤3*ordinary.card ∧ 2^894≤first.card ∧
    ordinary.filter (fun t => IsSquare (t^2-4*n))={s} ∧
    first.filter (fun t => IsSquare (t^2-4*n))={s}

/-- Members of the given population that satisfy the two work bounds. -/
noncomputable def witnessed (S : Finset (ℕ×ℕ)) := S.filter fun v => Work v.1 v.2

private theorem favored_mod5 (n s : ℕ) :
    favored (n%100) (s%100)=true ↔ (s%5*(s%5))%5=(4*(n%5))%5 := by
  unfold favored
  rw [beq_iff_eq,Nat.mul_mod (s%100) (s%100),Nat.mul_mod 4 (n%100)]
  simp only [Nat.mod_mod_of_dvd _ (by decide : 5∣100),show 4%5=4 by decide]

private theorem marks_same {p q : ℕ} (unit : p%5≠0) (eq : p%5=q%5) :
    ((p*q)%5=1 ∨ (p*q)%5=4) ∧ favored ((p*q)%100) ((p+q)%100)=true := by
  have table : ∀ d : Fin 5, d.val≠0 → ((d.val*d.val)%5=1 ∨ (d.val*d.val)%5=4) ∧
      (((d.val+d.val)%5)*((d.val+d.val)%5))%5=(4*((d.val*d.val)%5))%5 := by decide
  rw [favored_mod5,Nat.mul_mod p q,Nat.add_mod p q,←eq]
  exact table ⟨p%5,Nat.mod_lt _ (by decide)⟩ unit

private theorem marks_selected {n s : ℕ} (prod : (n:ZMod 25)=1)
    (sum : (s:ZMod 25)∈WidePrimePairSumFrequency.selected) :
    (n%5=1 ∨ n%5=4) ∧ favored (n%100) (s%100)=true := by
  have n25 : n%25=1 := by
    simpa only [ZMod.val_natCast,show (1:ZMod 25).val=1 by decide] using congrArg ZMod.val prod
  have s25 : s%25=2 ∨ s%25=23 := by
    simp only [WidePrimePairSumFrequency.selected,mem_insert,mem_singleton] at sum
    rcases sum with a|b
    · left; simpa only [ZMod.val_natCast,show (2:ZMod 25).val=2 by decide] using congrArg ZMod.val a
    · right; simpa only [ZMod.val_natCast,show (23:ZMod 25).val=23 by decide] using congrArg ZMod.val b
  have n5 : n%5=1 := by omega
  have s5 : s%5=2 ∨ s%5=3 := by omega
  refine ⟨Or.inl n5,(favored_mod5 n s).mpr ?_⟩
  rcases s5 with a|a <;> rw [a,n5]

/-- At least 2^893 complete blocks of length 100 precede this target; each
contributes two favored tests. This lower bound allows an incomplete last block. -/
theorem absolute_checks {n lo s : ℕ} (square : n%5=1 ∨ n%5=4) (wide : lo+2^900≤s) :
    2^894≤(favoredPrefix n lo s).card := by
  have lower : lo≤s := by omega
  rw [←favored_card square lower]
  have length : 2^900≤s-lo := by omega
  have blocks : 2^893≤(s-lo)/100 := (Nat.le_div_iff_mul_le (by decide)).mpr
    ((by decide +kernel : 2^893*100≤2^900).trans length)
  rw [show (2:ℕ)^894=2*2^893 by decide +kernel,firstGroupCost]
  exact (Nat.mul_le_mul_left 2 blocks).trans (Nat.le_add_right ..)

theorem pointwise {p q : ℕ} (pl : X≤p) (pq : p<q) (qu : q<B) (pp : p.Prime) (qp : q.Prime)
    (square : (p*q)%5=1 ∨ (p*q)%5=4) (mark : favored ((p*q)%100) ((p+q)%100)=true)
    (wide : ceilSqrt (4*(p*q))+2^900≤p+q) : Work p q := by
  have oddp := pp.odd_of_ne_two ((show 2<X by decide).trans_le pl).ne'
  have oddq := qp.odd_of_ne_two (((show 2<X by decide).trans_le pl).trans pq).ne'
  have hit := (passes_iff (p*q) (p+q)).mpr
    ⟨SumIntervalExclusion.sum_congruence (Nat.odd_iff.mp (oddp.mul oddq)),admissibleSum_of_factor_pair 25 rfl⟩
  have far : ceilSqrt (4*(p*q))+10000≤p+q :=
    (Nat.add_le_add_left (by decide : 10000≤2^900) _).trans wide
  have hi : q<2*X := (show B=2*X by decide +kernel) ▸ qu
  have unique := (semiprime_prefixes (by decide : 3≤X) pl pq hi pp qp square mark).2.2
  exact ⟨hit,mark,distant_prefix_bound square far hit mark,absolute_checks square wide,unique⟩

attribute [local irreducible] eligible population FullPopulationFavoredSums.longFavored
  FullPopulationFavoredSums.favoredPairs FullRangeLongSumPrefix.selectedAfter witnessed Work

theorem all_subset : FullPopulationFavoredSums.longFavored ⊆ witnessed eligible := by
  rintro ⟨p,q⟩ h
  obtain ⟨pl,pq,hi,pp,qp,_,eq,wide⟩ := FullPopulationFavoredSums.mem_longFavored.mp h
  have sub : FullPopulationFavoredSums.longFavored ⊆ eligible := by
    unfold FullPopulationFavoredSums.longFavored FullPopulationFavoredSums.favoredPairs
    exact (filter_subset ..).trans (filter_subset ..)
  have nz : p%5≠0 := by
    intro zero
    have bad := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) pp).mp (Nat.dvd_of_mod_eq_zero zero)
    exact ((by decide : 5<X).trans_le pl).ne bad
  have flags := marks_same nz eq
  rw [witnessed,mem_filter]
  exact ⟨sub h,pointwise pl pq hi pp qp flags.1 flags.2 wide⟩

theorem selected_subset : FullRangeLongSumPrefix.selectedAfter (2^900) ⊆
    witnessed (population univ) := by
  rintro ⟨p,q⟩ h
  obtain ⟨mem,wide⟩ := FullRangeLongSumPrefix.mem_wideSelected.mp h
  obtain ⟨pl,pq,hi,pp,qp,w,prod,sum⟩ := PrimeProductRegion.mem_population.mp mem
  have flags := marks_selected prod sum
  rw [witnessed,mem_filter]
  exact ⟨PrimeProductRegion.mem_population.mpr ⟨pl,pq,hi,pp,qp,w,prod,mem_univ _⟩,
    pointwise pl pq hi pp qp flags.1 flags.2 wide⟩

/-- More than 24.9% of all eligible balanced products satisfy both work
bounds, with the published unconditional BMOR endpoint estimate supplied. -/
theorem all_card {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    249*eligible.card<1000*(witnessed eligible).card :=
  (FullPopulationFavoredSums.bmor_card h).trans_le (Nat.mul_le_mul_left 1000 (card_le_card all_subset))

/-- Within product residue one modulo 25, the share exceeds 49.9%. -/
theorem product_one_card {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    499*(population univ).card<1000*(witnessed (population univ)).card :=
  (FullRangeLongSumPrefix.bmor_wide_card h).trans_le (Nat.mul_le_mul_left 1000 (card_le_card selected_subset))

private theorem share_of_count {k : ℕ} {S : Finset (ℕ×ℕ)}
    (h : k*S.card<1000*(witnessed S).card) :
    (k:ℚ)/1000<((witnessed S).card:ℚ)/S.card := by
  have sub : (witnessed S).card≤S.card := by
    unfold witnessed
    exact card_le_card (filter_subset ..)
  have positive : 0<S.card := by
    have hit : 0<(witnessed S).card := Nat.pos_of_mul_pos_left ((Nat.zero_le _).trans_lt h)
    exact hit.trans_le sub
  apply (div_lt_div_iff₀ (by norm_num) (Nat.cast_pos.mpr positive)).mpr
  exact_mod_cast (show k*S.card<(witnessed S).card*1000 by simpa only [Nat.mul_comm 1000] using h)

theorem all_share {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    249/1000<((witnessed eligible).card:ℚ)/eligible.card :=
  share_of_count (k:=249) (all_card h)

theorem product_one_share {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    499/1000<((witnessed (population univ)).card:ℚ)/(population univ).card :=
  share_of_count (k:=499) (product_one_card h)

end PrimeFactors.FavoredSumWork
