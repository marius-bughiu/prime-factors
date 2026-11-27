import PrimeFactors.LcmConvergentObstruction
import PrimeFactors.SmoothTotientEuler

/-! Count products for which any sufficiently smooth exponent reveals the prime sum
by ordinary continued fractions. Exponents may depend on the product. -/
namespace PrimeFactors.SmoothConvergentPopulation
open Finset MixedPrefixSample

/-- Eligible prime pairs admitting at least one exponent with prime divisors below B. -/
noncomputable def wins (B : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact eligible.filter fun z => ∃ E ∈ Nat.smoothNumbers B, E ≤ z.1*z.2 ∧
    ∃ i, (E : ℚ)/((z.1-1)*(z.2-1) : ℕ) = ((E : ℝ)/(z.1*z.2 : ℕ)).convergent i

attribute [local irreducible] eligible SmoothTotientTail.exceptional

theorem cover {B T : ℕ} (bound : T ≤ 2^1024) :
    wins B ⊆ SmoothTotientTail.exceptional B T := by
  classical
  intro z hz
  obtain ⟨eligible, E, smooth, fits, hit⟩ := mem_filter.mp hz
  exact LcmConvergentObstruction.smooth_hit eligible smooth fits bound hit

/-- Fewer than one in 2^553 eligible products admits any successful
1500-smooth exponent between one and the product, inclusive. -/
theorem rare : 2^553*(wins 1501).card < eligible.card :=
  (Nat.mul_le_mul_left _ (card_le_card (cover (B:=1501) (T:=2^1024) (by rfl)))).trans_lt
    (SmoothTotientTail.rare553 SmoothTotientEuler.euler_1500)

end PrimeFactors.SmoothConvergentPopulation
