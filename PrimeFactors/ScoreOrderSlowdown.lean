import PrimeFactors.ScoreSumOrder
import PrimeFactors.AllResidueSumCost

/-! A pointwise bound on the extra square tests from merging the two
residue groups by scaled discriminant. The bound uses the distance from
the physical square-root lower endpoint. -/

namespace PrimeFactors.ScoreOrderSlowdown

open Finset ScoreSumOrder FactorSumPrefixCost PeriodicSumRank
open scoped Classical
open private PrimeFactors.GlobalSumOrderCost.group_block PrimeFactors.GlobalSumOrderCost.cover
  PrimeFactors.GlobalSumOrderCost.inGroup from PrimeFactors.GlobalSumOrderCost
open private PrimeFactors.FactorSumPrefixCost.whole_blocks from PrimeFactors.FactorSumPrefixCost

private theorem distance_sq {a b : ℕ} (ab : a≤b) : (b-a)*(b+a)+a^2=b^2 := by
  obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le ab
  rw [Nat.add_sub_cancel_left]
  ring

/-- A favored candidate tested ahead of a smaller ordinary target has a
bounded lead. The one-unit term handles the ceiling of the square root. -/
theorem promoted_distance {n s t : ℕ} (np : 0<n) (low : ceilSqrt (4*n)≤s)
    (st : s<t) (keyBound : 4*(t^2-4*n)≤25*(s^2-4*n)) :
    4*(t-s)≤21*(s-ceilSqrt (4*n)+1) := by
  let lo := ceilSqrt (4*n)
  let r := lo-1
  have positive : 0<lo := by
    have rad := (ceilSqrt_le_iff.mp le_rfl : 4*n≤lo^2)
    by_contra! z
    rw [show lo=0 by omega] at rad
    omega
  have small : r^2<4*n := by
    by_contra! bad
    have le : lo≤r := ceilSqrt_le_iff.mpr bad
    dsimp only [r] at le
    omega
  have rs : r≤s := (Nat.sub_le lo 1).trans low
  have d₁ := distance_sq rs
  have d₂ := distance_sq st.le
  have nontrunc := ceilSqrt_le_iff.mp low
  have d₃ : (t-s)*(t+s)+(s^2-4*n)=t^2-4*n := by omega
  have maxD : s^2-4*n≤(s-r)*(s+r) := by omega
  rw [←d₃,Nat.mul_add] at keyBound
  have bound : 4*((t-s)*(t+s))≤21*(s^2-4*n) := by omega
  have mul : (4*(t-s))*(t+s)≤(21*(s-r))*(t+s) := by
    calc
      _ ≤ 21*(s^2-4*n) := by simpa only [Nat.mul_assoc] using bound
      _ ≤ 21*((s-r)*(s+r)) := Nat.mul_le_mul_left _ maxD
      _ ≤ 21*((s-r)*(t+s)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      _ = _ := (Nat.mul_assoc ..).symm
  have lead := Nat.le_of_mul_le_mul_right mul (by omega)
  have gap : s-r=s-lo+1 := by dsimp only [r]; omega
  rwa [gap] at lead

private theorem later_favored {n lo hi s t : ℕ} (ordinary : favored (n%100) (s%100)=false)
    (order : s<t) (member : t∈ScoreSumOrder.prefix n lo hi s) :
    favored (n%100) (t%100)=true ∧ 4*(t^2-4*n)≤25*(s^2-4*n) := by
  obtain ⟨_,_,before⟩ := mem_prefix.mp member
  have fav : favored (n%100) (t%100)=true := by
    cases ht : favored (n%100) (t%100)
    · exact (not_le_of_gt order ((same_group (ht.trans ordinary.symm)).mp before)).elim
    · rfl
  have le := key_le before
  simp only [key,fav,ordinary,if_true,Bool.false_eq_true,if_false] at le
  exact ⟨fav,le⟩

/-- An ordinary target pays at most two extra favored tests for each
additional 100-sum block in the finite promotion window. -/
theorem promoted_tests {n hi s : ℕ} (sq : n%5=1 ∨ n%5=4)
    (low : ceilSqrt (4*n)≤s) (ordinary : favored (n%100) (s%100)=false) :
    let lo := ceilSqrt (4*n)
    (ScoreSumOrder.prefix n lo hi s).card ≤ (passingPrefix n lo s).card +
      2*((21*(s-lo+1)+399)/400) := by
  dsimp only
  let lo := ceilSqrt (4*n)
  let k := (21*(s-lo+1)+399)/400
  let promoted := (Ico (s+1) (s+1+100*k)).filter (PrimeFactors.GlobalSumOrderCost.inGroup n true)
  have sub : ScoreSumOrder.prefix n lo hi s ⊆ passingPrefix n lo s ∪ promoted := by
    intro t member
    obtain ⟨⟨start,_⟩,pass,_⟩ := mem_prefix.mp member
    by_cases past : s<t
    · obtain ⟨yes,weight⟩ := later_favored ordinary past member
      have pos : 0<n := by rcases sq with a|b <;> omega
      have bound := promoted_distance pos low past weight
      change 4*(t-s)≤21*(s-lo+1) at bound
      have hi : t<s+1+100*k := by dsimp only [k]; omega
      exact mem_union_right _ (mem_filter.mpr ⟨mem_Ico.mpr ⟨past,hi⟩,pass,yes⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Ico.mpr ⟨start,by omega⟩,pass⟩)
  have count : promoted.card=2*k :=
    PrimeFactors.FactorSumPrefixCost.whole_blocks _ 2
      (fun a => PrimeFactors.GlobalSumOrderCost.group_block sq a true) (s+1) k
  exact (card_le_card sub).trans ((card_union_le ..).trans_eq (congrArg (_+·) count))

/-- Worst-case one-based test count on every passing target in a square-unit
product class, uniformly in the target and the upper end of the window. -/
theorem slowdown {n hi s : ℕ} (sq : n%5=1 ∨ n%5=4) (low : ceilSqrt (4*n)≤s)
    (pass : passes (n%100) (s%100)=true) :
    2*(ScoreSumOrder.prefix n (ceilSqrt (4*n)) hi s).card ≤
      5*(passingPrefix n (ceilSqrt (4*n)) s).card+21 := by
  let lo := ceilSqrt (4*n)
  cases mark : favored (n%100) (s%100)
  · have bound := promoted_tests (hi:=hi) sq low mark
    have rank := ascending_card (hi:=s) sq low le_rfl pass
    simp only [positions,PeriodicSumRank.ascending] at rank
    dsimp only at bound
    omega
  · have sub := card_le_card (favored_not_later (hi:=hi) (le_refl lo) mark low)
    change 2*(ScoreSumOrder.prefix n lo hi s).card ≤ 5*(passingPrefix n lo s).card+21
    omega

/-- Both orders test exactly the same prefix on the two nonsquare unit residues. -/
theorem nonsquare_prefix {n lo hi s : ℕ} (ns : n%5=2 ∨ n%5=3) (upper : s≤hi) :
    ScoreSumOrder.prefix n lo hi s = passingPrefix n lo s := by
  ext t
  have phase := (AllResidueSumCost.no_favored ns t).trans (AllResidueSumCost.no_favored ns s).symm
  constructor
  · intro h
    obtain ⟨⟨low,_⟩,pass,ord⟩ := mem_prefix.mp h
    have le := (same_group phase).mp ord
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨low,by omega⟩,pass⟩
  · intro h
    obtain ⟨bounds,pass⟩ := mem_filter.mp h
    obtain ⟨low,top⟩ := mem_Ico.mp bounds
    have le : t≤s := by omega
    exact mem_prefix.mpr ⟨⟨low,le.trans upper⟩,pass,(same_group phase).mpr le⟩

/-- The test bound applies at the unique successful sum for any distinct primes
in the same factor-width band above five. Both counts include the successful test. -/
theorem semiprime_slowdown {p q A : ℕ} (size : 5<A) (pl : A≤p) (ord : p<q)
    (qu : q<2*A) (pp : p.Prime) (qp : q.Prime) :
    let n := p*q
    let s := p+q
    let lo := ceilSqrt (4*n)
    let hi := ProductDeficitBand.sumCap n A
    2*(ScoreSumOrder.prefix n lo hi s).card ≤ 5*(passingPrefix n lo s).card+21 := by
  dsimp only
  have prime5 : Nat.Prime 5 := by decide
  have unit : (p*q)%5≠0 := by
    intro zero
    rcases prime5.dvd_mul.mp (Nat.dvd_of_mod_eq_zero zero) with dp|dq
    · have eq := (Nat.prime_dvd_prime_iff_eq prime5 pp).mp dp
      omega
    · have eq := (Nat.prime_dvd_prime_iff_eq prime5 qp).mp dq
      omega
  have hit := ScoreSumOrder.unique_hit (by omega : 3≤A) pl ord qu pp qp
  have member := (mem_filter.mp (hit.symm ▸ mem_singleton_self (p+q))).1
  obtain ⟨⟨lower,upper⟩,pass,_⟩ := mem_prefix.mp member
  by_cases sq : (p*q)%5=1 ∨ (p*q)%5=4
  · exact slowdown sq lower pass
  · rw [nonsquare_prefix (by omega : (p*q)%5=2 ∨ (p*q)%5=3) upper]
    omega

/-- The global favored-first order instead pays at least two additional
tests for every full 100-sum block after an ordinary target. -/
theorem global_tail {n lo hi s : ℕ} (sq : n%5=1 ∨ n%5=4)
    (mark : favored (n%100) (s%100)=false) :
    (passingPrefix n lo s).card+2*((hi-s)/100) ≤ (GlobalSumOrderCost.globalPrefix n lo hi s).card := by
  have eq := GlobalSumOrderCost.ordinary_exact (lo:=lo) (hi:=hi) mark
  let k := (hi-s)/100
  have tail : 2*k ≤ (favoredPrefix n (s+1) hi).card := by
    by_cases hs : s≤hi
    · have sub : ((Ico (s+1) ((s+1)+100*k)).filter (PrimeFactors.GlobalSumOrderCost.inGroup n true)) ⊆
          favoredPrefix n (s+1) hi := by
        intro t ht
        obtain ⟨bounds,test⟩ := mem_filter.mp ht
        have top : (s+1)+100*k≤hi+1 := by dsimp [k]; omega
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ico.mpr ⟨(mem_Ico.mp bounds).1,
          ((mem_Ico.mp bounds).2.trans_le top)⟩,test.1⟩,test.2⟩
      have h := card_le_card sub
      rwa [PrimeFactors.FactorSumPrefixCost.whole_blocks _ 2
        (fun a => PrimeFactors.GlobalSumOrderCost.group_block sq a true)] at h
    · simp only [k,Nat.sub_eq_zero_of_le (not_le.mp hs).le,Nat.zero_div,mul_zero,Nat.zero_le]
  unfold GlobalSumOrderCost.saving at eq
  dsimp only [k] at tail
  omega

end PrimeFactors.ScoreOrderSlowdown
