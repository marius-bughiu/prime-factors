import PrimeFactors.BalancedPairPopulation
import PrimeFactors.FixedBaseSmoothPopulation

/-! Frequency of full-size products at which at least one allowed checkpoint
reaches the identity at either hidden prime. -/
namespace PrimeFactors.FullSizeSmoothFrequency
open Finset BalancedPairPopulation FixedBaseSmoothPopulation
set_option exponentiation.threshold 2050
set_option maxRecDepth 4096
attribute [local irreducible] pairs products

noncomputable def hitPairs : Finset (ℕ × ℕ) := by
  classical
  exact pairs.filter fun z => localHit 21 1001 z.1 z.2 ∨ localHit 21 1001 z.2 z.1

noncomputable def hitProducts : Finset ℕ := hitPairs.image fun z => z.1*z.2

private theorem mem_hitPairs {z : ℕ × ℕ} : z ∈ hitPairs ↔ z ∈ pairs ∧
    (localHit 21 1001 z.1 z.2 ∨ localHit 21 1001 z.2 z.1) := by
  classical
  exact mem_filter

private theorem image_bound : hitProducts.card ≤ hitPairs.card := by
  unfold hitProducts
  exact card_image_le

attribute [local irreducible] hitPairs hitProducts

/-- Under Dusart's published prime-count inequalities, fewer than one in
2^177 eligible products admits even a local identity for the entire search. -/
theorem frequency (dusart : WeightedCrowdingEstimates.Dusart) :
    2^177 * hitProducts.card < products.card := by
  classical
  have bounds {n : ℕ} (width : n.size=1024) : 2^1023≤n ∧ n<2^1024 := by
    exact ⟨Nat.lt_size.mp (by omega), Nat.size_le.mp width.le⟩
  have counted := absolute_count hitPairs (by
    intro z hz
    obtain ⟨pp, qp, _, pw, qw, _⟩ := mem_pairs.mp (mem_hitPairs.mp hz).1
    exact ⟨pp, qp, (bounds pw).1, (bounds pw).2, (bounds qw).1, (bounds qw).2⟩)
    (fun _ hz => (mem_hitPairs.mp hz).2)
  have fewer : hitProducts.card < 2^1848 := image_bound.trans_lt counted
  calc
    _ < 2^177 * 2^1848 := Nat.mul_lt_mul_of_pos_left fewer (by positivity)
    _ = 2^2025 := by decide +kernel
    _ ≤ _ := population_products dusart

end PrimeFactors.FullSizeSmoothFrequency
