import PrimeFactors.MonotoneSumPopulation
import PrimeFactors.FirstSumMenuPopulation

/-! How often twice the ceiling square root, a particular monotone function,
agrees with the factor sum. The bin collision count and prime-count estimates
are unconditional over the repository's finite population. -/

namespace PrimeFactors.MonotoneClosePrimeLower

open Finset MixedPrefixSample FirstSumMenuPopulation MonotoneSumPopulation
open private PrimeFactors.FirstSumMenuPopulation.prime_pairs from PrimeFactors.FirstSumMenuPopulation

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192
attribute [local irreducible] sample eligible primes upperPrimes

/-- The factor sum suggested by the first Fermat midpoint. -/
def predictor (n : ℕ) : ℕ := 2*ceilSqrt n

theorem monotone : Monotone predictor := by
  intro a b le
  exact Nat.mul_le_mul_left 2 (ceilSqrt_le_iff.mpr (le.trans (ceilSqrt_le_iff.mp le_rfl)))

/-- The previous single-guess event is exactly the zero-error agreement set. -/
theorem single_eq : sample (event 1) = agreement predictor 0 := by
  ext z
  rw [mem_sample_iff,agreement,mem_filter]
  simp [menu,predictor,Nat.le_antisymm_iff,eq_comm,and_comm]

/-- Hitting one of the first J even sums bounds the one-sided distance from
the first. The approximate predictor still only returns one integer. -/
theorem menu_subset (J E : ℕ) (room : 2*(J-1)≤E) :
    sample (event J) ⊆ agreement predictor E := by
  intro z hz
  obtain ⟨inside,hit⟩ := mem_sample_iff.mp hz
  unfold menu at hit
  obtain ⟨i,hi,eq⟩ := mem_image.mp hit
  have small := mem_range.mp hi
  unfold agreement
  apply mem_filter.mpr
  refine ⟨inside, ?_⟩
  change 2*(ceilSqrt _+i)=z.1+z.2 at eq
  dsimp only [predictor]
  omega

private theorem prime_ratio : 100*primes.card < 631*upperPrimes.card := by
  have xp : 2<X := by decide +kernel
  have composite : ¬X.Prime := Nat.not_prime_of_dvd_of_lt
    (show 2∣X from dvd_pow_self _ (by decide : 1023≠0)) le_rfl xp
  have upper := SquareRootPhasePopulation.prime_upper (x:=X) (k:=1023) rfl (by omega) primes (by
    intro p hp
    obtain ⟨⟨lo,hi⟩,prime⟩ : (X≤p ∧ p<2*X) ∧ p.Prime := by simpa [primes] using hp
    exact ⟨lt_of_le_of_ne lo (fun eq => composite (eq ▸ prime)), hi, prime⟩)
  have lower := ChebyshevPrimeSample.prime_count
  change 11*X<35500*(upperPrimes.card-1) at lower
  omega

/-- If the number of upper primes is at least a thousand times the number
of bins, retaining the diagonal term gives a denominator of 40b. -/
theorem bin_bound {b D J : ℕ} (dp : 0<D) (cover : X≤b*D) (width : D^2≤8*X*J)
    (many : 1000*b≤upperPrimes.card) : eligible.card < (40*b)*(sample (event J)).card := by
  have combine (H P C T B : ℕ) (collision : H^2≤B*(2*T+H)) (lots : 1000*B≤H)
      (marg : 100*P<631*H) (pairs : 2*C≤P^2) : C<(40*B)*T := by
    have diag := Nat.mul_le_mul_right H lots
    have cap : 999*H^2 ≤ 2000*B*T := by nlinarith only [collision,diag]
    have sq := Nat.pow_lt_pow_left marg (by decide : 2≠0)
    nlinarith only [pairs,sq,cap,Nat.zero_le (B*T)]
  exact combine _ _ _ _ _ (finite_bound dp cover width) many prime_ratio
    PrimeFactors.FirstSumMenuPopulation.prime_pairs

private theorem many_bins : 1000*2^510 ≤ upperPrimes.card := by
  have count := ChebyshevPrimeSample.prime_count
  change 11*X<35500*(upperPrimes.card-1) at count
  have room : 35500*(1000*2^510)≤11*X := by decide +kernel
  omega

/-- Over sorted eligible prime pairs, exact agreement has frequency strictly
between 2^(-516) and the uniform upper bound 2^(-484). -/
theorem exact_fraction :
    eligible.card < 2^516*(agreement predictor 0).card ∧
    2^484*(agreement predictor 0).card < eligible.card := by
  have h := bin_bound (b:=2^510) (D:=2^513) (J:=1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) many_bins
  rw [single_eq] at h
  exact ⟨h.trans_le (Nat.mul_le_mul_right _ (by decide +kernel)), MonotoneSumPopulation.exact_fraction _ monotone⟩

/-- With tolerance 2^128 the same one-valued predictor agrees on a fraction
strictly between 2^(-452) and 2^(-419). -/
theorem tolerance_128 :
    eligible.card < 2^452*(agreement predictor (2^128)).card ∧
    2^419*(agreement predictor (2^128)).card < eligible.card := by
  have h := bin_bound (b:=3*2^445) (D:=11*2^573) (J:=2^127)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ((by decide +kernel : 1000*(3*2^445) ≤ 1000*2^510).trans many_bins)
  have sub := card_le_card (menu_subset (2^127) (2^128) (by decide +kernel))
  exact ⟨h.trans_le (Nat.mul_le_mul (by decide +kernel) sub), MonotoneSumPopulation.tolerance_128 _ monotone⟩

end PrimeFactors.MonotoneClosePrimeLower
