import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.MonotoneSumCoverage

/-! How often a nondecreasing prediction of the factor sum, with unrestricted
computational cost, can fit the eligible distinct 1,024-bit prime pairs. -/

namespace PrimeFactors.MonotoneSumPopulation

open Finset MixedPrefixSample
open scoped Classical
open private PrimeFactors.MixedPrefixSample.mem_sample PrimeFactors.MixedPrefixSample.mem_primes
  from PrimeFactors.MixedPrefixSample

set_option exponentiation.threshold 4096
attribute [local irreducible] primes eligible

/-- Agreement within absolute error E, inclusive on both ends. -/
noncomputable def agreement (g : ℕ→ℕ) (E : ℕ) :=
  eligible.filter (fun z => g (z.1*z.2)≤z.1+z.2+E ∧ z.1+z.2≤g (z.1*z.2)+E)

private theorem data {z : ℕ×ℕ} (mem : z∈eligible) : z.1<z.2 ∧ z.2<2^1024 := by
  rw [eligible] at mem
  obtain ⟨ord,lt⟩ := PrimeFactors.MixedPrefixSample.mem_sample.mp mem
  have hm := (mem_ordered.mp ord).2.1
  have high := (PrimeFactors.MixedPrefixSample.mem_primes.mp hm).1.2
  exact ⟨lt,(show 2*X=2^1024 by decide +kernel) ▸ high⟩

/-- Clipping the predictor at the largest possible sum below 2^1025
preserves every agreement. The finite grid bound then depends only on the
chosen block dimensions and the tolerance, even if g is unbounded. -/
theorem count (g : ℕ→ℕ) (mono : Monotone g) (B W E : ℕ) (width : 0<W)
    (blocks : B*W=2^2048) :
    (agreement g E).card ≤ ((2^1025-1)+(2*E+1)*B)*(W.sqrt+1) := by
  let cap : ℕ := 2^1025-1
  let clipped (n : ℕ) := min (g n) cap
  have monotone : Monotone clipped := fun _ _ h => min_le_min_right _ (mono h)
  have bound := MonotoneSumCoverage.card_bound (agreement g E) clipped monotone B W E width
  have sorted (z) (hz : z∈agreement g E) : z.1≤z.2 := (data (mem_filter.mp hz).1).1.le
  have within (z) (hz : z∈agreement g E) : z.1*z.2<B*W := by
    obtain ⟨lt,high⟩ := data (mem_filter.mp hz).1
    rw [blocks,show 2^2048=2^1024*2^1024 by decide +kernel]
    exact Nat.mul_lt_mul_of_lt_of_lt (lt.trans high) high
  have fit (z) (hz : z∈agreement g E) :
      clipped (z.1*z.2)≤z.1+z.2+E ∧ z.1+z.2≤clipped (z.1*z.2)+E := by
    obtain ⟨m,lower,upper⟩ := mem_filter.mp hz
    obtain ⟨lt,high⟩ := data m
    have sc : z.1+z.2≤cap := by
      have two : 2*2^1024=2^1025 := by decide +kernel
      dsimp [cap]
      omega
    by_cases small : g (z.1*z.2)≤cap
    · simpa only [clipped,min_eq_left small] using And.intro lower upper
    · simp only [clipped,min_eq_right (by omega : cap≤g (z.1*z.2))]
      omega
  apply (bound sorted within fit).trans
  apply Nat.mul_le_mul_right
  apply Nat.add_le_add_right
  exact (Nat.sub_le _ _).trans (min_le_right ..)

private theorem price {s c M : ℕ} (bounded : s≤c) (room : 21000000*(M*c)≤2^2046) :
    M*s<eligible.card := by
  have h := Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left M bounded)
  exact Nat.lt_of_mul_lt_mul_left (h.trans_lt (room.trans_lt ChebyshevPrimeSample.eligible_count))

/-- Exact equality occurs on fewer than one in 2^484 eligible pairs. -/
theorem exact_fraction (g : ℕ→ℕ) (mono : Monotone g) :
    2^484*(agreement g 0).card<eligible.card := by
  have h := count g mono (2^1024) (2^1024) 0 (by decide +kernel) (by decide +kernel)
  rw [show ((2:ℕ)^1024).sqrt=2^512 by
    rw [show (2:ℕ)^1024=2^512*2^512 by decide +kernel,Nat.sqrt_eq]] at h
  exact price h (by decide +kernel)

/-- Even a tolerance of 2^128 in the factor sum leaves the probability
of a match strictly below one in 2^419. -/
theorem tolerance_128 (g : ℕ→ℕ) (mono : Monotone g) :
    2^419*(agreement g (2^128)).card<eligible.card := by
  have h := count g mono (2^896) (2^1152) (2^128) (by decide +kernel) (by decide +kernel)
  rw [show ((2:ℕ)^1152).sqrt=2^576 by
    rw [show (2:ℕ)^1152=2^576*2^576 by decide +kernel,Nat.sqrt_eq]] at h
  exact price h (by decide +kernel)

end PrimeFactors.MonotoneSumPopulation
