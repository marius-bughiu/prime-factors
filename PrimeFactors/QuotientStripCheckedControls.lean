import PrimeFactors.FullWidthQuarticLaterMidpoint
import PrimeFactors.QuotientStripDistinctTests

/-!
# Before-factor costs on the constructed full-width quartic control

Use the given 1,024-bit factor sizes to cap the partner at 2^1024 − 1.
The retained blocks end strictly before the certified smaller prime. The
discriminant count permits sharing identical square tests across blocks.
-/

namespace PrimeFactors.QuotientStripCheckedControls

open FullWidthQuarticLaterMidpoint QuotientStripScheduleCost QuotientStripSlopeRestart
open QuotientStripSurvivingBlocks QuotientStripDistinctTests

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

private theorem active_quotient {n D : ℕ}
    (below : (n - 1) / 2 < ((n - 1) / D) ^ 2)
    (bit : 2 ^ 1023 ≤ (n - 1) / D + 1) :
    let a := (n - 1) / D + 1
    clippedStart n D = a ∧ first n < a := by
  let a := (n - 1) / D + 1
  have next : ((n - 1) / 2).sqrt < a - 1 := by
    simpa only [a, Nat.add_sub_cancel] using Nat.sqrt_lt'.mpr below
  have earlier : first n < a := by unfold first; omega
  exact ⟨(max_eq_right (earlier.le.trans (le_max_left a _))).trans (max_eq_left bit), earlier⟩

/-- The partner quotient is the active restart on this control. It advances
strictly beyond the original balanced lower endpoint. -/
theorem quartic_restart :
    let a := (N - 1) / (2 ^ 1024 - 1) + 1
    clippedStart N (2 ^ 1024 - 1) = a ∧ first N < a :=
  active_quotient (by decide +kernel) (by decide +kernel)

/-- For the certified quartic semiprime, even the restart using the largest
possible 1,024-bit partner leaves both lower bounds before the first factor. -/
theorem quartic_before_factor :
    2 ^ 654 < (kept N (clippedStart N (2 ^ 1024 - 1)) p).card ∧
    2 ^ 635 < (tests N (clippedStart N (2 ^ 1024 - 1)) p).card := by
  obtain ⟨factorization, _, ordered, _, low, high⟩ := FullWidthQuarticLaterMidpoint.data
  have product : p * q = N := by simpa only [List.prod_cons, List.prod_nil, mul_one] using factorization.1
  have ratio : 4 * q ≤ 5 * p := by decide +kernel
  have threshold : 400 * N ≤ 289 * (2 ^ 1024 - 4) ^ 2 := by decide +kernel
  have oddProduct := (p_prime.odd_of_ne_two (by decide +kernel)).mul
    (q_prime.odd_of_ne_two (by decide +kernel))
  have window := clipped_window (p := p) (q := q) (D := 2 ^ 1024 - 1)
    (product ▸ low) (product ▸ high) ratio (product ▸ threshold) le_rfl
  exact product ▸ ⟨population window, distinct_tests p_prime q_prime ordered.ne oddProduct window⟩

end PrimeFactors.QuotientStripCheckedControls
