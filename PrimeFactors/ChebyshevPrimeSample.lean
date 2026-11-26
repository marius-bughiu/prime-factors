import PrimeFactors.ChebyshevPrimeCount
import PrimeFactors.ReusableSumBase

/-! The integer estimates needed at the actual sampling endpoints. Seven applications of
the 30-to-5 Chebyshev bound suffice before using a crude upper bound for the tail. -/

namespace PrimeFactors.ChebyshevPrimeSample

open MixedPrefixSample

set_option exponentiation.threshold 4096

/-- Binary exponent obtained by rounding each endpoint up to a multiple of 30. -/
def budget : ℕ → ℕ → ℕ
  | 0, n => 1024*n
  | k+1, n =>
    let m := (n+29)/30
    40*m+32768+budget k (5*m)

theorem upper (L : ℕ → ℕ) (monotone : Monotone L)
    (crude : ∀ n ≤ 2^1024, L n ≤ (2^1024)^n)
    (step : ∀ m, L (30*m) ≤ 2^(40*m+32768)*L (5*m))
    (k n : ℕ) (bound : n ≤ 2^1024) : L n ≤ 2^budget k n := by
  induction k generalizing n with
  | zero =>
    simpa only [budget, pow_mul] using crude n bound
  | succ k ih =>
    let m := (n+29)/30
    have roundUp : n ≤ 30*m := by dsimp [m]; omega
    have tail : 5*m ≤ 2^1024 := by
      have big : 30 ≤ (2:ℕ)^1024 := by decide +kernel
      dsimp [m]; omega
    calc
      L n ≤ L (30*m) := monotone roundUp
      _ ≤ 2^(40*m+32768)*L (5*m) := step m
      _ ≤ 2^(40*m+32768)*2^budget k (5*m) := Nat.mul_le_mul_left _ (ih _ tail)
      _ = 2^budget (k+1) n := (pow_add ..).symm

/-- The powers of two are compared by their exponents. The numerical check only
evaluates 1,024-bit integers, without forming a factorial or a power of exponential size. -/
theorem input_of_bounds (L : ℕ → ℕ) (monotone : Monotone L)
    (crude : ∀ n ≤ 2^1024, L n ≤ (2^1024)^n)
    (step : ∀ m, L (30*m) ≤ 2^(40*m+32768)*L (5*m))
    (lower : ∀ m, 2^(39*m) ≤ 2^(32768)*L (30*m))
    (cutoff : L (2*X) ≤ L (283*X/200) * (2*X)^(2^512+upperPrimes.card)) :
    PrimeCountInput := by
  let y := 283*X/200
  let m := 2*X/30
  let h := upperPrimes.card
  have scale : 2*X = 2^1024 := by decide +kernel
  have yBound : y ≤ 2^1024 := by decide +kernel
  have low := (lower m).trans (Nat.mul_le_mul_left _ (monotone (show 30*m ≤ 2*X by dsimp [m]; omega)))
  have high := (upper L monotone crude step 7 y yBound)
  have bound : 2^(39*m) ≤ 2^(32768+budget 7 y+1024*(2^512+h)) := calc
    _ ≤ 2^(32768)*L (2*X) := low
    _ ≤ 2^(32768)*(L y*(2*X)^(2^512+h)) := Nat.mul_le_mul_left _ cutoff
    _ ≤ 2^(32768)*(2^budget 7 y*(2*X)^(2^512+h)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ high)
    _ = _ := by rw [scale, ← pow_mul, ← pow_add, ← pow_add, Nat.add_assoc]
  have exponents := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp bound
  have verified :
      11*X < 35500*((39*m-32768-budget 7 y-1024*2^512)/1024-1) := by
    decide +kernel
  change 11*X < 35500*(h-1)
  exact verified.trans_le (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (by omega) 1))

/-- There are enough primes above 283X/200 for the population estimates at 2,048 bits. -/
theorem prime_count : PrimeCountInput :=
  input_of_bounds ChebyshevPrimePowers.L ChebyshevPrimePowers.L_mono
    (fun _ h => ChebyshevPrimePowers.L_crude h) ChebyshevPrimePowers.step
    ChebyshevPrimePowers.lower ChebyshevPrimeCount.cutoff

theorem eligible_count : 2^2046 < 21000000*eligible.card :=
  denominator prime_count

/-- Choose the pair uniformly, then choose a unit uniformly for its product. -/
theorem single_base : SingleBasePopulation.balancedFailure < 1/(2:ℚ)^972 :=
  SingleBasePopulation.balanced prime_count

/-- A heavy seed fails on at least one eligible pair in 2^38. -/
theorem reusable_seed : 2^38*ReusableSumBase.heavySeeds.card < 2^1152 :=
  ReusableSumBase.reusable prime_count

/-- For each visible prefix and suffix, guess at most J signed corrections. -/
theorem mixed_carry {J : ℕ} (menu : ℕ → ℕ → Finset ℤ) (jp : 0<J)
    (slots : ∀ H∈Finset.Ico (2^640) (2^640+2^640), ∀ c<2^1023, Odd c → (menu H c).card≤J)
    (cap : ∀ H∈Finset.Ico (2^640) (2^640+2^640), ∀ c<2^1023, Odd c → ∀ k∈menu H c,
      (LowBitsCarryMenu.output c (2^704) k).natAbs<2^1406) :
    2^72*(successful menu).card < J*eligible.card :=
  probability menu jp prime_count slots cap

end PrimeFactors.ChebyshevPrimeSample
