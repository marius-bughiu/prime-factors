import PrimeFactors.EarlyPersistentMidpoints
import PrimeFactors.EarlyScoreWindow
import PrimeFactors.PublicWheelLookupCosts
import PrimeFactors.WithinResidueSearchFloor

/-! Wrong candidates in an early part of the actual score prefix. Each candidate
has a nonsquare integer discriminant but admits a local factor pair at every
prime-power precision for every prime through 643. -/
namespace PrimeFactors.PersistentScorePrefix

open Finset EarlyPersistentMidpoints PersistentLocalSurvivors
open WithinResidueSearchFloor (low target scoreVisits)
open MixedPrefixSample (eligible)
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open private PrimeFactors.WithinResidueSearchFloor.rare_of_long
  PrimeFactors.WithinResidueSearchFloor.eligible_hit from PrimeFactors.WithinResidueSearchFloor
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible

private theorem two_mem : 2∈smallPrimes 643 := mem_filter.mpr ⟨mem_range.mpr (by decide),Nat.prime_two⟩
private theorem five_mem : 5∈smallPrimes 643 := mem_filter.mpr ⟨mem_range.mpr (by decide),Nat.prime_five⟩

/-- A local root of the midpoint discriminant gives factors h+d and h−d;
the construction works at powers of two as well. -/
theorem local_sum {n h : ℕ} (ok : Passes n h) {p : ℕ} (hp : p∈smallPrimes 643) (e : ℕ) :
    AdmissibleSum (n:ZMod (p^e)) ((2*h:ℕ):ZMod (p^e)) := by
  rw [Nat.cast_mul,Nat.cast_ofNat,LocalMidpointLanes.midpoint_iff]
  simpa only [Int.cast_sub,Int.cast_pow,Int.cast_natCast] using ok p hp e

/-- The score menu needs the mod-four sum class and the mod-25 discriminant check. -/
theorem passes_menu {n h : ℕ} (odd : n%2=1) (ok : Passes n h) :
    PeriodicSumRank.passes (n%100) (2*h%100)=true := by
  apply (PeriodicSumRank.passes_iff n (2*h)).mpr
  exact ⟨(PublicWheelLookupCosts.first_prefix odd _).mp (local_sum ok two_mem 2),
    local_sum ok five_mem 2⟩

private theorem units {v : ℕ×ℕ} (hv : v∈eligible) : ∀ p∈smallPrimes 643, ¬p∣v.1*v.2 := by
  obtain ⟨pl,ord,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp hv
  intro p hp
  obtain ⟨lt,prime⟩ := mem_filter.mp hp
  have small := (Nat.le_of_lt_succ (mem_range.mp lt)).trans_lt (by decide +kernel : 643<X)
  have a := pp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt prime.pos (small.trans_le pl))
  have b := qp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt prime.pos ((small.trans_le pl).trans ord))
  exact prime.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_left.mpr ⟨a,b⟩).symm

private theorem false_square {v : ℕ×ℕ} (hv : v∈eligible) {t : ℕ}
    (visit : t∈scoreVisits v) (earlier : t<target v) : ¬IsSquare (t^2-4*(v.1*v.2)) := by
  obtain ⟨pl,ord,top,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp hv
  have hi : v.2<2*X := (by decide +kernel : B=2*X) ▸ top
  have only_hit := ScoreSumOrder.unique_hit (by decide +kernel : 3≤X) pl ord hi pp qp
  change (scoreVisits v).filter (fun x => IsSquare (x^2-4*(v.1*v.2)))={target v} at only_hit
  intro square
  exact earlier.ne (mem_singleton.mp (only_hit ▸ mem_filter.mpr ⟨visit,square⟩))

/-- Actual pre-hit sums from the first 2^896 possible midpoints above floor(√n).
The final predicate checks failure of the integer square test. -/
noncomputable def wrong (v : ℕ×ℕ) :=
  let n := v.1*v.2
  let start := n.sqrt+1
  (scoreVisits v).filter (fun t => t<target v ∧ t/2∈Ico start (start+2^896) ∧
    t=2*(t/2) ∧ Passes n (t/2) ∧ ¬IsSquare (t^2-4*n))

/-- Every counted sum has local factors with the specified product and sum.
Its full discriminant is locally square at the same modulus. -/
theorem local_evidence {v : ℕ×ℕ} {t : ℕ} (inside : t∈wrong v)
    {p : ℕ} (hp : p∈smallPrimes 643) (e : ℕ) :
    AdmissibleSum (v.1*v.2:ZMod (p^e)) (t:ZMod (p^e)) ∧
    IsSquare ((t:ZMod (p^e))^2-4*(v.1*v.2)) := by
  obtain ⟨_,_,_,even,all,_⟩ := mem_filter.mp inside
  have s := local_sum all hp e
  rw [←even] at s
  have factors : AdmissibleSum (v.1*v.2:ZMod (p^e)) (t:ZMod (p^e)) := by
    simpa only [Nat.cast_mul] using s
  obtain ⟨x,y,prod,sum⟩ := factors
  exact ⟨⟨x,y,prod,sum⟩,x-y,by rw [←prod,←sum]; ring⟩

/-- The very same natural discriminant fails the integer test and passes every
local square test. The lower endpoint guarantees exact natural subtraction. -/
theorem discriminant {v : ℕ×ℕ} {t : ℕ} (inside : t∈wrong v) :
    t<target v ∧ ¬IsSquare (t^2-4*(v.1*v.2)) ∧
      ∀ p∈smallPrimes 643, ∀ e : ℕ, IsSquare ((t^2-4*(v.1*v.2):ℕ):ZMod (p^e)) := by
  obtain ⟨visit,lt,_,_,_,bad⟩ := mem_filter.mp inside
  refine ⟨lt,bad,?_⟩
  intro p hp e
  have lower : ceilSqrt (4*(v.1*v.2))≤t := (ScoreSumOrder.mem_prefix.mp visit).1.1
  rw [Nat.cast_sub (ceilSqrt_le_iff.mp lower),Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_mul]
  exact (local_evidence inside hp e).2

/-- The bound concerns wrong sums strictly before the first successful test,
including when the local test precision is chosen separately for each sum. -/
theorem long_floor {v : ℕ×ℕ} (hv : v∈eligible) (long : low v+2^900≤target v) :
    2^765<(wrong v).card := by
  let n := v.1*v.2
  let start := n.sqrt+1
  have unit := units hv
  have odd : n%2=1 := by
    have two : ¬2∣n := unit 2 two_mem
    omega
  have np : 0<n := Nat.pos_of_ne_zero (fun hz => by
    have two : ¬2∣n := unit 2 two_mem
    exact two (hz ▸ dvd_zero _))
  apply tally (start:=start) unit
  intro k ok
  have pass := passes_menu odd ok
  have early := EarlyScoreWindow.early np long k.isLt
  have visit : 2*(start+k.val)∈scoreVisits v := EarlyScoreWindow.mem_prefix np long k.isLt
    (PrimeFactors.WithinResidueSearchFloor.eligible_hit hv).1 pass
  have lt : 2*(start+k.val)<target v := early.2.1
  apply mem_filter.mpr
  refine ⟨visit,lt,?_,?_,?_,false_square hv visit lt⟩
  · simp only [Nat.mul_div_cancel_left _ (by decide : 0<2),mem_Ico]
    exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left k.isLt _⟩
  · rw [Nat.mul_div_cancel_left _ (by decide : 0<2)]
  · simpa only [Nat.mul_div_cancel_left _ (by decide : 0<2)] using ok

/-- Fewer than one in 2^35 eligible pairs have at most 2^765 such wrong visits. -/
theorem population :
    2^35*(eligible.filter (fun v => (wrong v).card≤2^765)).card<eligible.card := by
  have h := PrimeFactors.WithinResidueSearchFloor.rare_of_long (visits:=wrong) (n:=2^765+1)
    (fun _ hv long => long_floor hv long)
  simpa only [Nat.lt_succ_iff] using h

end PrimeFactors.PersistentScorePrefix
