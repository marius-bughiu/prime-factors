import PrimeFactors.SixTraceBudget

/-! Count distinct 2048-bit inputs where a mod-six trace search finds a
factor within the budget and the odd trace search spends it unsuccessfully. -/
namespace PrimeFactors.SixTraceNewProducts
open Finset SixTraceBudget InteriorBatchPopulation

set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

private theorem same_first {p q u v : ℕ} (pp : p.Prime) (up : u.Prime) (vp : v.Prime)
    (pq : p<q) (uv : u<v) (eq : p*q=u*v) : p=u := by
  have divide : p∣u*v := eq ▸ dvd_mul_right p q
  rcases pp.dvd_mul.mp divide with h|h
  · exact (Nat.prime_dvd_prime_iff_eq pp up).mp h
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq pp vp).mp h
    have qu := Nat.eq_of_mul_eq_mul_left pp.pos (eq.trans (Nat.mul_comm u p))
    omega

/-- This hypothesis allows any choice of the larger prime at each smaller
prime. Choosing one suffices, even when different rows offer many partners. -/
def HasPartners (budget : ℕ) : Prop :=
  ∀ {p : ℕ}, p∈InteriorBatchPopulation.interior → ∃ q∈neighbors p, q.Prime ∧ p<q ∧ q<U ∧ bin p q ∧
    (unitHit (p*q) (ceilSqrt (24*(p*q))) budget ∧ ¬oddHit (p*q) (ceilSqrt (24*(p*q))) budget)

attribute [local irreducible] InteriorBatchPopulation.interior neighbors firstPrimes population successes

theorem card_new_of_partners {budget : ℕ} (found : HasPartners budget) :
    InteriorBatchPopulation.interior.card ≤ (successes unitHit budget \ successes oddHit budget).card := by
  classical
  let q (p : ↥InteriorBatchPopulation.interior) := Classical.choose (found p.property)
  have facts (p : ↥InteriorBatchPopulation.interior) := Classical.choose_spec (found p.property)
  have pp (p : ↥InteriorBatchPopulation.interior) : p.val.Prime :=
    (mem_filter.mp (by simpa only [InteriorBatchPopulation.interior,firstPrimes] using p.property)).2
  have partner (p : ↥InteriorBatchPopulation.interior) : q p∈neighbors p ∧ (q p).Prime ∧ p.val<q p ∧ q p<U ∧ bin p (q p) ∧
      (unitHit (p.val*q p) (ceilSqrt (24*(p.val*q p))) budget ∧
        ¬oddHit (p.val*q p) (ceilSqrt (24*(p.val*q p))) budget) := facts p
  have into (p : ↥InteriorBatchPopulation.interior) :
      p.val*q p∈successes unitHit budget \ successes oddHit budget := by
    obtain ⟨hq,qp,pq,qu,bn,hit,miss⟩ := partner p
    have pl := (interior_split p.property hq).2.1
    have bit : 16*2^2047≤9*U^2 := by decide +kernel
    have full : 2^2047≤p.val*q p :=
      Nat.le_of_mul_le_mul_left (bit.trans bn.1) (by decide)
    have member := mem_population.mpr ⟨p.val,q p,pl,pq,qu,pp p,qp,full,rfl⟩
    exact mem_sdiff.mpr ⟨mem_success.mpr ⟨member,hit⟩,fun h => miss (mem_success.mp h).2⟩
  have count := card_le_card_of_injOn (s:=InteriorBatchPopulation.interior.attach) (fun p => p.val*q p)
    (fun p _ => into p) (by
      intro p _ r _ eq
      exact Subtype.ext (same_first (pp p) (pp r) (partner r).2.1
        (partner p).2.2.1 (partner r).2.2.1 eq))
  simpa only [card_attach] using count

/-- Only the lower prime count in the single interior interval is
used here. The total applies to individual input integers. -/
theorem many_new_of_partners {budget : ℕ} (C : Counts) (found : HasPartners budget) :
    2^1009 < (successes unitHit budget \ successes oddHit budget).card := by
  have lower := C.lower (79*(U/128)) (82*(U/128))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [←InteriorBatchPopulation.interior] at lower
  have size : 2^1009 < InteriorBatchPopulation.interior.card := by
    norm_num [U] at lower ⊢
    omega
  exact size.trans_le (card_new_of_partners found)

private theorem cover_count (a b : ℕ) :
    (firstPrimes 0 b).card ≤ (firstPrimes 0 a).card + (firstPrimes a b).card := by
  have cover : firstPrimes 0 b ⊆ firstPrimes 0 a ∪ firstPrimes a b := by
    intro p hp
    obtain ⟨hi,pr⟩ := mem_filter.mp (by simpa only [firstPrimes] using hp)
    obtain ⟨_,top⟩ := mem_Icc.mp hi
    rw [mem_union,firstPrimes,firstPrimes]
    by_cases le : p≤a
    · exact Or.inl (mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,le⟩,pr⟩)
    · exact Or.inr (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,top⟩,pr⟩)
  exact (card_le_card cover).trans (card_union_le _ _)

/-- Rounded endpoint inequalities from Rosser–Schoenfeld (1962), Theorem 2.
The prime count in the fixed macroscopic interval requires no short-interval estimate. -/
theorem many_new_of_endpoints {budget : ℕ}
    (low : 1415*(firstPrimes 0 (79*(U/128))).card ≤ 2*(79*(U/128)))
    (high : 2*(82*(U/128)) ≤ 1419*(firstPrimes 0 (82*(U/128))).card)
    (found : HasPartners budget) :
    2^1009 < (successes unitHit budget \ successes oddHit budget).card := by
  have cover := cover_count (79*(U/128)) (82*(U/128))
  rw [←InteriorBatchPopulation.interior] at cover
  have size : 2^1009 < InteriorBatchPopulation.interior.card := by
    norm_num [U] at low high cover ⊢
    omega
  exact size.trans_le (card_new_of_partners found)

end PrimeFactors.SixTraceNewProducts
