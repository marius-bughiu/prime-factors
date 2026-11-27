import PrimeFactors.IntervalSievePrimeWeights
import PrimeFactors.ChebyshevPrimePowers

/-! The number of primes in the explicit larger-sieve family. -/
namespace PrimeFactors.IntervalSievePrimeCount

open Finset IntervalSievePrimeWeights ChebyshevPrimePowers

private theorem prime_power_product {Q : ℕ} (hQ : 2 ≤ Q) :
    L Q ≤ Q ^ ((primes Q).card + 1) := by
  let P := (range (Q+1)).filter Nat.Prime
  have split : P = insert 2 (primes Q) := by
    ext p
    simp only [P, primes, mem_filter, mem_range, mem_insert, mem_Icc, Nat.lt_succ_iff]
    constructor
    · rintro ⟨hi, hp⟩
      have lo := hp.two_le
      by_cases eq : p = 2
      · exact Or.inl eq
      · exact Or.inr ⟨⟨by omega, hi⟩, hp⟩
    · rintro (rfl | ⟨⟨_, hi⟩, hp⟩)
      · exact ⟨hQ, Nat.prime_two⟩
      · exact ⟨hi, hp⟩
  have cap := prod_le_prod' (s:=P) (g:=fun _ => Q)
    (fun p _ => Nat.pow_log_le_self p (show Q ≠ 0 by omega))
  change L Q ≤ ∏ _p ∈ P, Q at cap
  rw [prod_const, split, card_insert_of_not_mem (by simp [primes])] at cap
  exact cap

/-- The least common multiple through 2^k has one prime power at most
2^k for each prime. Chebyshev's factorial ratio supplies its lower bound. -/
theorem exponent_bound {k : ℕ} (hk : 1 ≤ k) :
    39*(2^k/30) ≤ 32768 + k*((primes (2^k)).card+1) := by
  let Q := 2^k
  have large : 2 ≤ Q := by simpa [Q] using Nat.pow_le_pow_right (by decide : 0<2) hk
  have base := lower (Q/30)
  have upto : 30*(Q/30) ≤ Q := by omega
  have estimate := base.trans (Nat.mul_le_mul_left (2^32768)
    ((L_mono upto).trans (prime_power_product large)))
  change 2^(39*(2^k/30)) ≤ 2^32768 * (2^k)^((primes (2^k)).card+1) at estimate
  rw [← pow_mul, ← pow_add] at estimate
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp estimate

attribute [local irreducible] IntervalSievePrimeWeights.primes

/-- An implementation that visits each odd prime through 2^520 must
visit more than 2^511 distinct primes. -/
theorem full_width : 2^511 < (primes (2^520)).card := by
  have bound := exponent_bound (k:=520) (by decide)
  have numeric : 32768 + 520*(2^511+1) < 39*(2^520/30) := by decide +kernel
  omega

end PrimeFactors.IntervalSievePrimeCount
