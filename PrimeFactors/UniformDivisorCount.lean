import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.Positivity

/-! An explicit bound for the number of divisors of any positive integer below
`2^2049`, using a finite correction to the inequality at each prime power.
Every correction is rounded upwards to an integer number of sixteenth-bits
in the bound for `τ(n)^21/n^2`. -/

namespace PrimeFactors.UniformDivisorCount

open Finset

set_option exponentiation.threshold 100000

/-- Binary search retaining an upper exponent at each comparison. This kernel-
reducible definition makes the finite numerical certificate independent of a
native logarithm implementation. -/
private def narrow (a hi : ℕ) : ℕ → ℕ
  | 0 => hi
  | k+1 =>
    let mid := hi-2^k
    if a<2^mid then narrow a mid k else narrow a hi k

private theorem narrow_bound (a hi k : ℕ) (h : a<2^hi) : a<2^narrow a hi k := by
  induction k generalizing hi with
  | zero => exact h
  | succ k ih =>
    simp only [narrow]
    split
    · exact ih _ (by assumption)
    · exact ih _ h

private def bits (a : ℕ) := if a=0 then 0 else narrow a 2047 11

private def price (p e : ℕ) := bits (((e+1)^336-1)/p^(32*e))

private noncomputable def charge (p : ℕ) :=
  if p<1449 then (range 16).sup (price p) else 0

/-- Above 37, a single gcd with 37! eliminates small composite divisors.
All primes from 38 through 1448 pass this test. -/
private noncomputable def smallPrimes := (range 1449).filter fun p =>
  if p≤37 then p.Prime else p.Coprime (Nat.factorial 37)

private theorem mem_small {p : ℕ} (hp : p.Prime) (small : p<1449) : p ∈ smallPrimes := by
  apply mem_filter.mpr
  refine ⟨mem_range.mpr small,?_⟩
  split
  · exact hp
  · exact hp.coprime_iff_not_dvd.mpr (fun hd => by have := hp.dvd_factorial.mp hd; omega)

set_option maxRecDepth 300000 in
set_option maxHeartbeats 5000000 in
private theorem budget : (∑ p ∈ smallPrimes, charge p = 14882) ∧ smallPrimes.card = 229 := by
  decide +kernel

private theorem short_prime_power {p e : ℕ} (hp : 0<p) (small : p<1449) (short : e<16) :
    (e+1)^336 ≤ 2^charge p*p^(32*e) := by
  let a := ((e+1)^336-1)/p^(32*e)
  have hb : a<2^bits a := by
    by_cases hz : a=0
    · simp [hz,bits]
    · have top : a<2^2047 := calc
        a ≤ (e+1)^336-1 := Nat.div_le_self ..
        _ ≤ (e+1)^336 := Nat.sub_le ..
        _ ≤ 16^336 := Nat.pow_le_pow_left (by omega) _
        _ < _ := by decide +kernel
      simpa only [bits,if_neg hz] using narrow_bound a 2047 11 top
  have hle : bits a ≤ charge p := by
    simpa only [charge,if_pos small] using
      (Finset.le_sup (s:=range 16) (f:=price p) (mem_range.mpr short))
  have hl := (Nat.div_lt_iff_lt_mul (Nat.pow_pos hp)).mp
    (hb.trans_le (Nat.pow_le_pow_right (by decide) hle))
  have hpos : 0<(e+1)^336 := by positivity
  omega

private theorem next_power {a p : ℕ} (large : 16≤a) (prime : 2≤p) :
    (a+1)^336≤a^336*p^32 := by
  have step := Nat.pow_le_pow_left (show (a+1)*16≤a*17 by omega) 336
  rw [mul_pow,mul_pow] at step
  have start : (17:ℕ)^336≤16^336*2^32 := by decide +kernel
  have hb := Nat.pow_le_pow_left prime 32
  have h := step.trans (Nat.mul_le_mul_left _ (start.trans (Nat.mul_le_mul_left _ hb)))
  exact Nat.le_of_mul_le_mul_right (by simpa only [mul_assoc,mul_left_comm,mul_comm] using h)
    (by decide : 0<(16:ℕ)^336)

private theorem large_prime_power {p : ℕ} (hp : 1449≤p) (e : ℕ) :
    (e+1)^336 ≤ p^(32*e) := by
  have first : (2:ℕ)^336≤p^32 :=
    (by decide +kernel : (2:ℕ)^336≤1449^32).trans (Nat.pow_le_pow_left hp _)
  have bound : e+1≤2^e := by
    induction e with
    | zero => decide
    | succ e ih => rw [pow_succ]; omega
  calc
    _ ≤ (2^e)^336 := Nat.pow_le_pow_left bound _
    _ = (2^336)^e := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
    _ ≤ (p^32)^e := Nat.pow_le_pow_left first _
    _ = _ := (pow_mul ..).symm

private theorem prime_power {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (e+1)^336 ≤ 2^charge p*p^(32*e) := by
  by_cases small : p<1449
  · induction e with
    | zero => exact short_prime_power hp.pos small (by decide)
    | succ e ih =>
      by_cases short : e+1<16
      · exact short_prime_power hp.pos small short
      · calc
          _ ≤ (e+1)^336*p^32 := next_power (by omega) hp.two_le
          _ ≤ (2^charge p*p^(32*e))*p^32 := Nat.mul_le_mul_right _ ih
          _ = _ := by rw [Nat.mul_succ,pow_add,mul_assoc]
  · simpa [charge,small] using large_prime_power (by omega : 1449≤p) e

/-- A size-independent divisor bound obtained with 229 small-prime corrections. -/
theorem power_bound {n : ℕ} (hn : 0<n) : n.divisors.card^336 ≤ 2^14882*n^32 := by
  have hc : ∑ p ∈ n.primeFactors, charge p ≤ 14882 := by
    have eq : ∑ p ∈ n.primeFactors ∩ smallPrimes, charge p =
        ∑ p ∈ n.primeFactors, charge p := by
      apply Finset.sum_subset Finset.inter_subset_left
      intro p h out
      have prime := Nat.prime_of_mem_primeFactors h
      have large : ¬ p<1449 := by
        intro hlt
        exact out (mem_inter.mpr ⟨h,mem_small prime hlt⟩)
      simp [charge,large]
    rw [←eq,←budget.1]
    exact Finset.sum_le_sum_of_subset Finset.inter_subset_right
  have prod := Finset.prod_le_prod' (s:=n.primeFactors) (fun p h =>
    prime_power (Nat.prime_of_mem_primeFactors h) (n.factorization p))
  have fac : ∏ p ∈ n.primeFactors, p^(n.factorization p)=n :=
    Nat.factorization_prod_pow_eq_self hn.ne'
  conv_rhs at prod =>
    arg 2
    ext p
    rw [Nat.mul_comm 32, pow_mul]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Finset.prod_pow,
    Finset.prod_pow,fac,←Nat.card_divisors hn.ne'] at prod
  exact prod.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hc))

/-- A binary input cap retains the fractional exponent from the finite certificate.
For 2,049 bits the right-hand exponent is 80,450, and for 4,098 it is 146,018. -/
theorem below_power_two {n b : ℕ} (hn : 0<n) (bound : n<2^b) :
    n.divisors.card^336 < 2^(14882+32*b) := calc
  _ ≤ 2^14882*n^32 := power_bound hn
  _ < 2^14882*((2^b)^32) :=
    Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left bound (by decide)) (by positivity)
  _ = _ := by rw [←pow_mul,←pow_add,Nat.mul_comm b]

/-- Every positive integer with at most 2,049 bits has fewer than `2^240` divisors. -/
theorem below_2049 {n : ℕ} (hn : 0<n) (bound : n<2^2049) : n.divisors.card < 2^240 := by
  apply (Nat.pow_lt_pow_iff_left (by decide : 336≠0)).mp
  refine (below_power_two hn bound).trans ?_
  rw [←pow_mul]
  exact Nat.pow_lt_pow_right (by decide) (by decide)

end PrimeFactors.UniformDivisorCount
