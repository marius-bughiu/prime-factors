import PrimeFactors.ChebyshevQuarticScale
import PrimeFactors.IntervalWheelResidues

/-! The exact wheel counts for the two published 2,048-bit comparison products
use only their residues modulo 4 and the seven odd primes through 19. -/
namespace PrimeFactors.IntervalWheelControls

open ChebyshevQuarticScale (fresh crossed)
open IntervalWheelResidues LocalSumMenu

def components : List ℕ := [4, 3, 5, 7, 11, 13, 17, 19]

/-- Product residues in the order used by the wheel. -/
theorem fresh_residues :
    fresh % modulus = 1026079 ∧ components.map (fresh % ·) = [3, 1, 4, 5, 10, 2, 10, 3] := by
  decide +kernel

theorem crossed_residues :
    crossed % modulus = 1082089 ∧ components.map (crossed % ·) = [1, 1, 4, 1, 8, 8, 5, 1] := by
  decide +kernel

private theorem prime_count {n p : ℕ} (prime : p.Prime) (odd : p ≠ 2) (unit : ¬ p ∣ n) :
    count n p = (letI : NeZero p := ⟨prime.ne_zero⟩
      if ∃ x : ZMod p, x*x = (n : ZMod p) then (p+1)/2 else (p-1)/2) := by
  letI : Fact p.Prime := ⟨prime⟩
  letI : NeZero p := ⟨prime.ne_zero⟩
  have nz : (n : ZMod p) ≠ 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd n p).mp.mt unit
  rw [count, card_admissibleSum_eq p _ nz]
  split_ifs with square
  · obtain ⟨x, hx⟩ := square
    exact card_factorSumResidues_of_square p odd _ nz ⟨x, hx.symm⟩
  · apply card_factorSumResidues_of_nonsquare p _ nz
    rintro ⟨x, hx⟩
    exact square ⟨x, hx.symm⟩

theorem fresh_components : components.map (count fresh) = [1, 2, 3, 3, 5, 6, 8, 9] := by
  simp only [components, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨count_four (by decide +kernel), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [prime_count (by decide) (by decide) (by decide +kernel)]
    decide +kernel

theorem crossed_components : components.map (count crossed) = [1, 2, 3, 4, 5, 6, 8, 10] := by
  simp only [components, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨count_four (by decide +kernel), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [prime_count (by decide) (by decide) (by decide +kernel)]
    decide +kernel

private theorem count_product (n : ℕ) : count n modulus = (components.map (count n)).prod := by
  rw [count_components]
  simp [components, Nat.mul_assoc]

theorem fresh_count : count fresh modulus = 38880 := by
  rw [count_product, fresh_components]
  decide

theorem crossed_count : count crossed modulus = 57600 := by
  rw [count_product, crossed_components]
  decide

/-- The seven-per-class upper bounds when a supplied error band meets at most
seven representatives of each wheel class. -/
theorem fresh_seven_periods : 7 * count fresh modulus = 272160 := by rw [fresh_count]

theorem crossed_seven_periods : 7 * count crossed modulus = 403200 := by rw [crossed_count]

end PrimeFactors.IntervalWheelControls
