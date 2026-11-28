import PrimeFactors.RationalPredictionTurns
import PrimeFactors.PiecewiseMonotoneSumPopulation

/-! Agreement between the factor sum and the ordinary signed floor of a fixed
real rational function. The denominator must be nonzero on a counted input.
The coefficients and the values of the denominator can be arbitrarily large. -/

namespace PrimeFactors.RoundedRationalSumPopulation

open Finset Polynomial MixedPrefixSample RationalPredictionTurns
open scoped Classical

set_option exponentiation.threshold 4096
attribute [local irreducible] eligible

/-- Sorted eligible prime pairs where the quotient is defined and its signed
integer floor differs from the true factor sum by at most E. -/
noncomputable def hits (A B : ℝ[X]) (E : ℕ) : Finset (ℕ×ℕ) :=
  eligible.filter fun z =>
    let n := z.1*z.2
    B.eval (n:ℝ)≠0 ∧ |⌊ratio A B n⌋ - (z.1+z.2:ℤ)| ≤ E

private theorem covered (A B : ℝ[X]) (E : ℕ) :
    PiecewiseMonotoneSumPopulation.Covered (hits A B E) (range (budget A B)) (piece A B)
      (fun _ => rounded A B) E := by
  intro z hz
  obtain ⟨inside,defined,error⟩ := mem_filter.mp hz
  obtain ⟨i,hi,mem⟩ := covers A B (z.1*z.2) defined
  refine ⟨inside,i,hi,mem,?_⟩
  change |⌊ratio A B ((z.1*z.2 : ℕ) : ℝ)⌋-(z.1+z.2:ℤ)|≤(E:ℤ) at error
  obtain ⟨lo,hi⟩ := abs_le.mp error
  dsimp only [PiecewiseMonotoneSumPopulation.fit,rounded]
  rw [←Int.floor_toNat]
  omega

/-- The bound is linear in the number of interval labels. A pole is excluded
from the numerator and remains present in the population denominator. -/
theorem exact_budget (A B : ℝ[X]) :
    2^484*(hits A B 0).card < budget A B*eligible.card := by
  simpa only [card_range] using PiecewiseMonotoneSumPopulation.exact_menu
    (hits A B 0) (range (budget A B)) (piece A B) (fun _ => rounded A B)
    (fun i _ => rounded_on A B i) (nonempty_range_iff.mpr (by simp [budget])) (covered A B 0)

theorem tolerance_budget (A B : ℝ[X]) :
    2^419*(hits A B (2^128)).card < budget A B*eligible.card := by
  simpa only [card_range] using PiecewiseMonotoneSumPopulation.approximate_menu
    (hits A B (2^128)) (range (budget A B)) (piece A B) (fun _ => rounded A B)
    (fun i _ => rounded_on A B i) (nonempty_range_iff.mpr (by simp [budget])) (covered A B _)

/-- Any numerator and denominator of degrees at most 2^28 give fewer than
one exact floor hit per 2^453 eligible pairs, and fewer than one hit within
2^128 per 2^388 eligible pairs. -/
theorem degree_28 {A B : ℝ[X]} (ha : A.natDegree≤2^28) (hb : B.natDegree≤2^28) :
    2^453*(hits A B 0).card < eligible.card ∧
    2^388*(hits A B (2^128)).card < eligible.card := by
  have cap : budget A B ≤ 2^31 := (budget_le ha hb).trans (by decide +kernel)
  have cmp := Nat.mul_le_mul_right eligible.card cap
  constructor
  · apply Nat.lt_of_mul_lt_mul_left (a:=2^31)
    rw [←Nat.mul_assoc,←pow_add]
    exact (exact_budget A B).trans_le cmp
  · apply Nat.lt_of_mul_lt_mul_left (a:=2^31)
    rw [←Nat.mul_assoc,←pow_add]
    exact (tolerance_budget A B).trans_le cmp

/-- The same event evaluated directly in rational arithmetic. -/
noncomputable def rationalHits (A B : ℚ[X]) (E : ℕ) : Finset (ℕ×ℕ) :=
  eligible.filter fun z =>
    let n := z.1*z.2
    B.eval (n:ℚ)≠0 ∧ |⌊A.eval (n:ℚ)/B.eval (n:ℚ)⌋-(z.1+z.2:ℤ)|≤E

theorem cast_hits (A B : ℚ[X]) (E : ℕ) :
    hits (A.map (algebraMap ℚ ℝ)) (B.map (algebraMap ℚ ℝ)) E = rationalHits A B E := by
  have cast (x : ℚ) : algebraMap ℚ ℝ x=(x:ℝ) := rfl
  ext z
  simp only [hits,rationalHits,mem_filter,ratio,Polynomial.eval_map,Polynomial.eval₂_at_natCast,
    cast,ne_eq,Rat.cast_eq_zero,←Rat.cast_div,Rat.floor_cast]

theorem rational_degree_28 {A B : ℚ[X]} (ha : A.natDegree≤2^28) (hb : B.natDegree≤2^28) :
    2^453*(rationalHits A B 0).card < eligible.card ∧
    2^388*(rationalHits A B (2^128)).card < eligible.card := by
  simpa only [cast_hits] using degree_28 (A:=A.map (algebraMap ℚ ℝ)) (B:=B.map (algebraMap ℚ ℝ))
    (Polynomial.natDegree_map_le.trans ha) (Polynomial.natDegree_map_le.trans hb)

end PrimeFactors.RoundedRationalSumPopulation
