import PrimeFactors.DyadicSumPeak
import PrimeFactors.DyadicSumGuessPopulation

/-! What a single sum guess can achieve on full-width primes, with only
a fixed 161-bit product remainder equal to one modulo eight. -/
namespace PrimeFactors.FullWidthSumPrediction

open DyadicSumGuessPopulation PrimeSquareSumWeights

set_option exponentiation.threshold 4096

/-- For every one of these fixed product suffixes the local maximum
covers 2^81 of the 2^160 ordered possibilities. -/
theorem peak {r : (ZMod (2^161))ˣ} (good : r.val.val%8=1) :
    best (m:=2^161) (weight r.val.val)=2^81 := by
  exact (best_spec (m:=2^161) (weight r.val.val)).unique
    (DyadicSumPeak.square_product_peak (by decide : 6≤161) good)

/-- Best possible success for predicting the true 161-bit sum reading
from this fixed public product remainder. -/
theorem accuracy {r : (ZMod (2^161))ˣ} (good : r.val.val%8=1) {li : ℕ→ℝ}
    (ehp : ExtendedModulusPrimeSupply.Endpoints (2^161) li) :
    |best (actual r)-1/(2:ℝ)^79| ≤ 1/(2:ℝ)^225 := by
  have bound := optimum (by decide : 3≤2^161) (le_refl _) ehp r
  dsimp only at bound
  rw [peak good,Nat.totient_prime_pow_succ Nat.prime_two] at bound
  norm_num at bound ⊢
  exact bound

/-- In the two product classes 3 and 7 modulo 8 every admissible sum
has four ordered presentations. Their optimal single-guess chance is
about 2^(-158), conditional on the full product suffix as above. -/
theorem three_accuracy {r : (ZMod (2^161))ˣ} (cl : r.val.val%4=3) {li : ℕ→ℝ}
    (ehp : ExtendedModulusPrimeSupply.Endpoints (2^161) li) :
    |best (actual r)-1/(2:ℝ)^158| ≤ 1/(2:ℝ)^304 := by
  have box := (best_spec (m:=2^161) (weight r.val.val)).unique
    (DyadicSumPeak.three_peak (by decide : 3≤161) cl).1
  have bound := optimum (by decide : 3≤2^161) (le_refl _) ehp r
  dsimp only at bound
  rw [box,Nat.totient_prime_pow_succ Nat.prime_two] at bound
  norm_num at bound ⊢
  exact bound

/-- Products congruent to 5 modulo 8 have eight presentations of
each admissible sum. -/
theorem five_accuracy {r : (ZMod (2^161))ˣ} (cl : r.val.val%8=5) {li : ℕ→ℝ}
    (ehp : ExtendedModulusPrimeSupply.Endpoints (2^161) li) :
    |best (actual r)-1/(2:ℝ)^157| ≤ 1/(2:ℝ)^303 := by
  have box := (best_spec (m:=2^161) (weight r.val.val)).unique
    (DyadicSumPeak.five_peak (by decide : 5≤161) cl).1
  have bound := optimum (by decide : 3≤2^161) (le_refl _) ehp r
  dsimp only at bound
  rw [box,Nat.totient_prime_pow_succ Nat.prime_two] at bound
  norm_num at bound ⊢
  exact bound

/-- The strict comparisons underlying the maximum survive transfer to
prime pairs. Ties between the two modular maximizers may split. -/
theorem only_local_winners {r : (ZMod (2^161))ˣ} (good : r.val.val%8=1)
    {li : ℕ→ℝ} (ehp : ExtendedModulusPrimeSupply.Endpoints (2^161) li)
    {s : ZMod (2^161)} (win : actual r s=best (actual r)) :
    weight r.val.val s=2^81 := by
  have limit : 2*best (m:=2^161) (weight r.val.val)≤2^146 := by rw [peak good]; decide +kernel
  exact (maximizer (by decide) (le_refl _) ehp r limit win).trans (peak good)

end PrimeFactors.FullWidthSumPrediction
