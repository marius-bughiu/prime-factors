import PrimeFactors.FullDyadicClueScan
import PrimeFactors.DyadicCluePersistentClass

/-! A lower bound on earlier false sums in the ascending search with a
supplied 160-bit suffix and modular factor tests at every power of two. -/
namespace PrimeFactors.AllDyadicClueScanFloor

open Finset DyadicClueFullSumClass
open FullDyadicClueScan (wrong)
open WithinResidueSearchFloor (low target)
open MixedPrefixSample (eligible)
open scoped Classical
set_option exponentiation.threshold 4096
attribute [local irreducible] eligible

/-- Every residue has a representative in each complete block, whatever
the residue of the lower endpoint. The upper endpoint is excluded. -/
theorem interval_floor {lo hi m b : ℕ} (positive : 0<m) (visits : Finset ℕ)
    (kept : ∀ s, lo≤s → s<hi → s ≡ b [MOD m] → s∈visits) :
    (hi-lo)/m ≤ visits.card := by
  letI : NeZero m := ⟨positive.ne'⟩
  let r := ((b:ZMod m)-(lo:ZMod m)).val
  have small : r<m := ZMod.val_lt _
  have count : (range ((hi-lo)/m)).card ≤ visits.card := by
    apply card_le_card_of_injOn (fun i => lo+i*m+r)
    · intro i hi'
      have block := (Nat.le_div_iff_mul_le positive).mp (Nat.succ_le_of_lt (mem_range.mp hi'))
      rw [Nat.succ_mul] at block
      apply kept _ (by omega) (by omega)
      apply (ZMod.natCast_eq_natCast_iff _ _ m).mp
      simp [r,ZMod.natCast_zmod_val]
    · intro i hi' j hj' eq
      change lo+i*m+r=lo+j*m+r at eq
      exact Nat.eq_of_mul_eq_mul_right positive (by omega)
  simpa only [card_range] using count

/-- A whole compatible residue gives this many earlier ordinary square
tests, regardless of where it falls relative to the true sum. -/
theorem floor_of_class {p q b m : ℕ} (positive : 0<m)
    (ok : ∀ s : ℕ, s ≡ b [MOD m] → Possible 160 (p*q:ℕ) (p%2^160:ℕ) s) :
    (p+q-ceilSqrt (4*(p*q)))/m ≤ (wrong (p,q)).card := by
  apply interval_floor (b:=b) positive
  intro s hl hr congr
  exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hl,hr⟩,ok s congr⟩

/-- For either odd factor supplied, a class of period 2^323 survives.
This counts candidates strictly before the true sum. -/
theorem pointwise {p q : ℕ} (po : Odd p) (qo : Odd q) :
    (p+q-ceilSqrt (4*(p*q)))/2^323 ≤ (wrong (p,q)).card := by
  have suffix : Odd (p%2^160) := Nat.odd_iff.mpr ((Nat.mod_mod_of_dvd p
    (by decide +kernel : 2∣2^160)).trans (Nat.odd_iff.mp po))
  obtain ⟨b,keep⟩ := DyadicCluePersistentClass.exists_class (k:=160)
    (by decide) (po.mul qo) suffix (Nat.mod_lt _ (by decide +kernel))
  exact floor_of_class (b:=b) (by decide +kernel : 0<2^323) keep

/-- Across all eligible distinct full-width prime pairs, the fraction
with fewer than 2^577 earlier false sums is strictly below 2^(-35).
The bounds use unconditional prime counts. -/
theorem population :
    2^35*(eligible.filter (fun v => (wrong v).card<2^577)).card < eligible.card := by
  refine (Nat.mul_le_mul_left _ (card_le_card (t:=WithinResidueSearchFloor.short) ?_)).trans_lt
    WithinResidueSearchFloor.exceptional
  rintro ⟨p,q⟩ h
  obtain ⟨member,small⟩ := mem_filter.mp h
  change (wrong (p,q)).card<2^577 at small
  obtain ⟨pl,ord,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp member
  have pgt : 2<p := (by decide +kernel : 2<FullRangeResidueEstimates.X).trans_le pl
  have po := Nat.odd_iff.mpr (pp.eq_two_or_odd.resolve_left pgt.ne')
  have qo := Nat.odd_iff.mpr (qp.eq_two_or_odd.resolve_left (pgt.trans ord).ne')
  have bound := (Nat.div_lt_iff_lt_mul (by decide +kernel : 0<2^323)).mp
    ((pointwise po qo).trans_lt small)
  rw [show (2:ℕ)^577*2^323=2^900 by decide +kernel] at bound
  apply mem_filter.mpr
  refine ⟨member,?_⟩
  change p+q<ceilSqrt (4*(p*q))+2^900
  omega

end PrimeFactors.AllDyadicClueScanFloor
