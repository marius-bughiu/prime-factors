import PrimeFactors.DivisorSignPanel
import PrimeFactors.SplitPrimeInterval

/-! A finite analytic hypothesis for the exact set of simultaneous Jacobi-positive
primes in a physical interval. The function ψ is already divided by the field
degree. No analytic estimate or construction of a number field is assumed by
the proof other than the displayed endpoint and remainder hypotheses. -/

namespace PrimeFactors.SplitPrimeBudget

open DivisorSignPanel
open scoped BigOperators

/-- The normalized Chebyshev values at the endpoints of the inclusive interval.
After subtracting the weights of the actual surviving primes, the increment
has a nonnegative bounded remainder. The external field application supplies
ψ and its degree 2^k for the chosen list of moduli. -/
def EndpointBudget (k lo hi : ℕ) (entries : List Entry) (ψ : ℕ → ℝ) : Prop :=
  let m : ℕ := 2^k
  let error : ℝ := (121*((k : ℝ)*355)+21007)*2^512
  let θ := ∑ p ∈ primes lo hi entries, Real.log (p : ℝ)
  |ψ (lo-1) - ((lo-1 : ℕ) : ℝ)/m| ≤ error ∧
    |ψ hi - (hi : ℝ)/m| ≤ error ∧
    0 ≤ ψ hi - ψ (lo-1) - θ ∧ ψ hi - ψ (lo-1) - θ ≤ 710*2^512

/-- The endpoint error estimate gives both integer weighted bounds for exactly
the primes tested by the panel. The interval width includes both endpoints. -/
theorem weightedBounds {k lo hi : ℕ} {entries : List Entry} {ψ : ℕ → ℝ}
    (size : k ≤ 512) (low : 2^1023 ≤ lo) (ordered : lo ≤ hi) (high : hi < 2^1024)
    (analytic : EndpointBudget k lo hi entries ψ) :
    DivisorSignPanel.weightedBounds (2^k) (hi-lo+1) (2^538) (primes lo hi entries).card := by
  obtain ⟨left, right, rem, rem_bound⟩ := analytic
  have logs (p : ℕ) (hp : p ∈ primes lo hi entries) :
      708 ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 710 := by
    have interval := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    exact SplitPrimeInterval.log_1024 (low.trans interval.1) (interval.2.trans high.le)
  have theta := SplitPrimeInterval.log_bounds (primes lo hi entries)
    (fun p hp => (logs p hp).1) (fun p hp => (logs p hp).2)
  have budget := SplitPrimeInterval.normalized_error size (le_refl _) (le_refl _) (le_refl _)
  have b := SplitPrimeInterval.weighted_interval (m := 2^k) (by positivity) left right
    rem rem_bound budget theta.1 theta.2
  have lo_pos : 1 ≤ lo := le_trans (pow_pos (by decide : 0 < (2 : ℕ)) 1023) low
  have width : ((hi-lo+1 : ℕ) : ℝ) = (hi : ℝ) - ((lo-1 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub ordered, Nat.cast_sub lo_pos]
    ring
  rw [← width] at b
  constructor
  · exact_mod_cast b.1
  · exact_mod_cast b.2

end PrimeFactors.SplitPrimeBudget
