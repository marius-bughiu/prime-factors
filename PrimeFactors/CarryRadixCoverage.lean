import PrimeFactors.ShiftedSmallRadices
import PrimeFactors.CarryRemainderPairs

/-! Combine the absolute counts for successful small and large dyadic carry
probes. The split places a pair with successes on both sides in the small set. -/

namespace PrimeFactors.CarryRadixCoverage
open Finset PredictedTraceCarries

set_option exponentiation.threshold 8192

/-- An actual low-radix success with both signed carries in the tested budget. -/
private def SmallHit (z : ℕ × ℕ) : Prop :=
  ∃ e, 1≤e ∧ e≤512 ∧ ∃ h k : ℤ, |h|≤4 ∧ |k|≤4 ∧ ∃ f,
    probe (z.1*z.2) (2^e) h k=some f

/-- All successful ordered prime pairs at target factor width. The high carry
is unrestricted above 2^512 and bounded by four up to that radix. -/
theorem count {pairs : Finset (ℕ × ℕ)}
    (hits : ∀ z∈pairs, z.1.Prime ∧ z.2.Prime ∧ z.1≠z.2 ∧
      2^1023≤z.1 ∧ z.1<2^1024 ∧ 2^1023≤z.2 ∧ z.2<2^1024 ∧
      ∃ e, 1≤e ∧ e≤1024 ∧ ∃ h k : ℤ, (e≤512 → |h|≤4) ∧ |k|≤4 ∧ ∃ f,
        probe (z.1*z.2) (2^e) h k=some f) :
    pairs.card<2^1553 := by
  classical
  let small := pairs.filter SmallHit
  have smallBound := ShiftedSmallRadices.small_count_of_hits
    (pairs:=small) (pool:=range (2^1024)) (by
      intro z hz
      obtain ⟨mem,hit⟩ := mem_filter.mp hz
      obtain ⟨pp,qp,ne,pl,pu,ql,qu,_⟩ := hits z mem
      exact ⟨mem_range.mpr pu,pp,qp,ne,pl,ql,qu,hit⟩)
  rw [card_range,←pow_add] at smallBound
  have largeBound := CarryRemainderPairs.hit_count (pairs:=pairs\small) (by
    intro z hz
    obtain ⟨mem,other⟩ := mem_sdiff.mp hz
    obtain ⟨pp,qp,ne,pl,pu,ql,qu,e,lo,hi,h,k,hc,kc,f,hit⟩ := hits z mem
    have above : 513≤e := by
      by_contra! below
      have lim : e≤512 := by omega
      exact other (mem_filter.mpr ⟨mem,e,lo,lim,h,k,hc lim,kc,f,hit⟩)
    exact ⟨pp,qp,ne,by omega,pu,by omega,qu,e,above,hi,h,k,kc,f,hit⟩)
  have split := card_sdiff_add_card_eq_card (show small⊆pairs from filter_subset _ _)
  exact split ▸ ((Nat.add_le_add_left smallBound _).trans_lt largeBound)

/-- The only population premise is a lower bound on the number of eligible
target pairs. Search windows and exponents may depend on the whole product. -/
theorem successful_fraction {pairs : Finset (ℕ × ℕ)} {pop : ℕ} (den : 2^2021≤pop)
    (hits : ∀ z∈pairs, z.1.Prime ∧ z.2.Prime ∧ z.1≠z.2 ∧
      2^1023≤z.1 ∧ z.1<2^1024 ∧ 2^1023≤z.2 ∧ z.2<2^1024 ∧
      ∃ e, 1≤e ∧ e≤1024 ∧ ∃ h k : ℤ, (e≤512 → |h|≤4) ∧ |k|≤4 ∧ ∃ f,
        probe (z.1*z.2) (2^e) h k=some f) :
    2^468*pairs.card<pop := by
  have two := Nat.mul_lt_mul_of_pos_left (count hits) (Nat.two_pow_pos 468)
  rw [←pow_add] at two
  exact two.trans_le den

end PrimeFactors.CarryRadixCoverage
