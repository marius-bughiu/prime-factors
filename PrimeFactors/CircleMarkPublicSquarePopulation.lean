import PrimeFactors.CircleMarkRationalBoundaryPopulation
import PrimeFactors.RecognizingQuarticProducts

/-! Count eligible products for which the larger prime lies in the one-sided
shortfall strip of the square grid planned from the product's fourth root. -/
namespace PrimeFactors.CircleMarkPublicSquarePopulation

open Finset MixedPrefixSample RecognizingQuarticProducts
open private PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info
  PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info from PrimeFactors.CyclotomicCoefficientProbePopulation
open private PrimeFactors.CircleMarkRationalBoundaryPopulation.gaps
  PrimeFactors.CircleMarkRationalBoundaryPopulation.price_gap from PrimeFactors.CircleMarkRationalBoundaryPopulation

set_option exponentiation.threshold 8192
attribute [local irreducible] eligible primes

/-- Include also products whose larger prime already lies below the threshold. -/
noncomputable def throughBand : Finset (ℕ×ℕ) := eligible.filter fun z =>
  let h := fourthRoot (z.1*z.2)
  z.2≤(h+1)^2+h

/-- Exactly the positive shortfall regime at the larger prime. -/
noncomputable def fringe : Finset (ℕ×ℕ) := throughBand.filter fun z =>
  (fourthRoot (z.1*z.2)+1)^2<z.2

theorem mem_fringe {p q : ℕ} : (p,q)∈fringe ↔ (p,q)∈eligible ∧
    ∃ s : ℕ, 0<s ∧ s≤fourthRoot (p*q) ∧ q=(fourthRoot (p*q)+1)^2+s := by
  simp only [fringe,throughBand,mem_filter]
  constructor
  · rintro ⟨⟨ok,hi⟩,lo⟩
    exact ⟨ok,q-(fourthRoot (p*q)+1)^2,by omega,by omega,by omega⟩
  · rintro ⟨ok,s,sp,bound,eqn⟩
    exact ⟨⟨ok,by omega⟩,by omega⟩

/-- The product-derived fourth root puts twice its square below the sum.
Consequently the upper edge of the strip also bounds the prime gap. -/
theorem gap {p q : ℕ} (cap : q≤(fourthRoot (p*q)+1)^2+fourthRoot (p*q)) :
    q-p≤6*fourthRoot (p*q)+2 := by
  let h := fourthRoot (p*q)
  have fourth : h^4≤p*q := le_fourthRoot.mp le_rfl
  have mid : 2*h^2≤p+q := by
    apply Nat.mul_self_le_mul_self_iff.mp
    nlinarith only [fourth,two_mul_le_add_sq p q]
  change q≤(h+1)^2+h at cap
  have up : q≤h^2+3*h+1 := by nlinarith only [cap]
  change q-p≤6*h+2
  omega

private theorem through_sub : throughBand⊆eligible := filter_subset ..
private theorem fringe_sub : fringe⊆throughBand := filter_subset ..
attribute [local irreducible] fringe throughBand

theorem through_upper : 2^494*throughBand.card<eligible.card := by
  apply PrimeFactors.CircleMarkRationalBoundaryPopulation.price_gap (G:=3*2^512) _ (by decide +kernel)
  apply PrimeFactors.CircleMarkRationalBoundaryPopulation.gaps _ _ through_sub
  rintro ⟨p,q⟩ m
  rw [throughBand,mem_filter] at m
  obtain ⟨pair,cap⟩ := m
  obtain ⟨_,qm,ord⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info pair
  have qtop : q<2^1024 := (PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info qm).2.1
  have pq : p*q<(2^512)^4 := by
    rw [show (2^512:ℕ)^4=2^1024*2^1024 by decide +kernel]
    exact (Nat.mul_le_mul_right q (ord.trans qtop).le).trans_lt
      (Nat.mul_lt_mul_of_pos_left qtop (by decide +kernel))
  have small : fourthRoot (p*q)<2^512 := lt_of_not_ge (fun big => (not_le_of_gt pq) (le_fourthRoot.mp big))
  have d := gap (p:=p) (q:=q) cap
  change q-p<2*(3*2^512)
  omega

/-- This bound is unconditional and counts each full-width product once. -/
theorem fringe_upper : 2^494*fringe.card<eligible.card :=
  (Nat.mul_le_mul_left _ (card_le_card fringe_sub)).trans_lt through_upper

end PrimeFactors.CircleMarkPublicSquarePopulation
