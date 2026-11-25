import PrimeFactors.StationaryRadixLimit

namespace PrimeFactors.StationarySlopeBudget
open Finset
open StationaryRadixLimit
set_option exponentiation.threshold 4096

private theorem slope_totient {R : ℕ} [NeZero R] (c : (ZMod R)ˣ) :
    R.totient = (AffineSlopeClasses.slopes c).card * Nat.card (Roots R) := by
  rw [← ZMod.card_units_eq_totient R, AffineSlopeClasses.slope_count c]
  simp [Roots, Nat.card_eq_fintype_card, Fintype.card_subtype]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem first_primes :
    (quotientBudgetPrimes 467).card=91 ∧
    2^554 * 2^91 < ∏ p ∈ quotientBudgetPrimes 467, (p-1) := by
  change ((range 468).filter Nat.Prime).card=91 ∧
    2^554*2^91 < ∏ p ∈ (range 468).filter Nat.Prime, (p-1)
  decide +kernel

private theorem totient_lower {R : ℕ} (pos : 0<R) :
    (∏ p ∈ R.primeFactors, (p-1)) ≤ R.totient := by
  rw [Nat.totient_eq_div_primeFactors_mul]
  have gpos : 0 < ∏ p ∈ R.primeFactors, p := prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
  have one := Nat.div_pos (Nat.le_of_dvd pos (Nat.prod_primeFactors_dvd R)) gpos
  simpa using Nat.mul_le_mul_right (∏ p ∈ R.primeFactors, (p-1)) one

/-- The contribution (p-1)/2 of every prime is compared in the rationals,
including the factor 1/2 at the prime 2. The cutoff product already exceeds
the budget before any larger primes or prime powers are added. -/
theorem many_prime_factors {R : ℕ} [NeZero R] (many : 91≤R.primeFactors.card)
    (c : (ZMod R)ˣ) : 2^553 < (AffineSlopeClasses.slopes c).card := by
  classical
  let P := quotientBudgetPrimes 467
  let f (p : ℕ) : ℚ := ((p-1:ℕ):ℚ)/2
  obtain ⟨card,first⟩ := first_primes
  have cmp := quotientBudget_product_exchange (s := P) (t := R.primeFactors) f
    (cut := 233) (by norm_num) (card.le.trans many)
    (fun _ _ => div_nonneg (Nat.cast_nonneg _) (by norm_num))
    (by
      intro p hp
      have inP := (mem_sdiff.mp hp).1
      have small : p≤467 := by
        have h := (mem_filter.mp inP).1
        exact Nat.le_of_lt_succ (mem_range.mp h)
      have q : ((p-1:ℕ):ℚ) ≤ 466 := by exact_mod_cast (by omega : p-1≤466)
      dsimp [f]
      linarith)
    (by
      intro p hp
      obtain ⟨inR,notP⟩ := mem_sdiff.mp hp
      have notSmall : ¬p≤467 := fun bound => notP
        (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le bound),Nat.prime_of_mem_primeFactors inR⟩)
      have q : (466:ℚ) ≤ ((p-1:ℕ):ℚ) := by exact_mod_cast (by omega : 466≤p-1)
      dsimp [f]
      linarith)
  have prodRatio (s : Finset ℕ) :
      (∏ p ∈ s, f p) = ((∏ p ∈ s, (p-1:ℕ)):ℚ)/(2:ℚ)^s.card := by
    simp [f,prod_div_distrib,Nat.cast_prod]
  rw [prodRatio,prodRatio,show P.card = 91 from card] at cmp
  have strict : (2:ℚ)^554 < ((∏ p ∈ P, (p-1:ℕ)):ℚ)/(2:ℚ)^91 := by
    apply (lt_div_iff₀ (by positivity)).mpr
    exact_mod_cast first
  have scaled := (lt_div_iff₀ (by positivity)).mp (strict.trans_le cmp)
  have natScaled : 2^554*2^R.primeFactors.card < ∏ p ∈ R.primeFactors, (p-1) := by
    exact_mod_cast scaled
  have lower : 2^553 * 2^(R.primeFactors.card+1) < R.totient := by
    rw [pow_succ]
    calc 2^553*(2^R.primeFactors.card*2) = (2^553*2)*2^R.primeFactors.card := by ring
         _ = (2:ℕ)^554*2^R.primeFactors.card := by rw [show (2:ℕ)^554 = 2^553*2 by decide +kernel]
         _ < _ := natScaled.trans_le (totient_lower (NeZero.pos R))
  apply lt_of_not_ge
  intro small
  have upper := Nat.mul_le_mul small (roots_le (NeZero.pos R))
  rw [← slope_totient c] at upper
  exact (not_le_of_gt lower) upper

/-- Beyond this cutoff the slope count exceeds the search budget for every
radix, including radices outside the finite primorial ratio estimate. -/
theorem above_budget {R budget : ℕ} [NeZero R] (c : (ZMod R)ˣ)
    (maxBudget : budget≤2^553) (size : 13*(budget*2^91)<R) :
    budget < (AffineSlopeClasses.slopes c).card := by
  by_cases many : 91≤R.primeFactors.card
  · exact maxBudget.trans_lt (many_prime_factors many c)
  by_contra! small
  have rootCap := (roots_le (NeZero.pos R)).trans
    (Nat.pow_le_pow_right (by decide : 0<2) (by omega : R.primeFactors.card+1≤91))
  have upper := Nat.mul_le_mul small rootCap
  rw [← slope_totient c] at upper
  by_cases finite : R≤2^1366
  · have ratio := quotientBudget_wheel_ratio (NeZero.pos R) finite
    exact (not_le_of_gt size) (ratio.le.trans (Nat.mul_le_mul_left 13 upper))
  · have far := quotientBudget_totient_square R
    have scale := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left
      (upper.trans (Nat.mul_le_mul_right _ maxBudget)) 2)
    exact finite ((far.trans scale).trans (by decide +kernel))

theorem offset_slopes {R : ℕ} [NeZero R] (c : (ZMod R)ˣ) (size : 2^647<R) :
    2^552 < (AffineSlopeClasses.slopes c).card :=
  above_budget c (by decide +kernel) ((by decide +kernel : 13*((2:ℕ)^552*2^91)≤2^647).trans_lt size)

theorem uniform_slopes {R : ℕ} [NeZero R] (c : (ZMod R)ˣ) (size : 2^648<R) :
    2^553 < (AffineSlopeClasses.slopes c).card :=
  above_budget c le_rfl ((by decide +kernel : 13*((2:ℕ)^553*2^91)≤2^648).trans_lt size)

end PrimeFactors.StationarySlopeBudget
