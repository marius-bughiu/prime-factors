import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.UniformDivisorCount

/-! Finite arithmetic for the population reached by two weighted square-excess
windows. The number of Pell solutions per pair of traces is an explicit
hypothesis. The denominator is the checked count of eligible prime pairs. -/
namespace PrimeFactors.WeightedPairPopulation
open Finset

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

/-- Inverse powers of two in the upper bounds for the five window budgets. -/
def saving : ℕ → ℕ
  | 0 => 740
  | 64 => 663
  | 128 => 587
  | 256 => 435
  | 512 => 130
  | _ => 0

/-- The factors account for both trace counts, solutions per class, and
the reciprocal of the lower bound on the population density. -/
private abbrev coefficient : ℕ := 5*42*1024*21000000

/-- The exact fractional exponent, retained as an integer power inequality. -/
theorem divisor_bound {b c : ℕ} (positive : 0<c) (small : c < 512*2^1023*2^b) :
    ((c^2).divisors.card)^336 < 2^(14882+64*(1032+b)) := by
  have size : c < 2^(1032+b) := by
    rw [pow_add]
    exact small
  have sq : c^2 < 2^(2*(1032+b)) := by
    rw [Nat.mul_comm 2 (1032+b),pow_mul]
    exact Nat.pow_lt_pow_left size (by decide)
  convert UniformDivisorCount.below_power_two (pow_pos positive _) sq using 2
  omega

private theorem scaled {b c : ℕ} (positive : 0<c) (small : c < 512*2^1023*2^b) :
    (coefficient*((c^2).divisors.card))^336 < 2^(14125+14882+64*(1032+b)) := by
  have constant : coefficient^336 ≤ 2^14125 := by decide +kernel
  rw [mul_pow]
  calc
    _ ≤ 2^14125 * (c^2).divisors.card^336 := Nat.mul_le_mul_right _ constant
    _ < 2^14125 * 2^(14882+64*(1032+b)) :=
      Nat.mul_lt_mul_of_pos_left (divisor_bound positive small) (by positivity)
    _ = _ := by rw [←pow_add]; congr 1; omega

private theorem rates {b : ℕ} (allowed : b ∈ [0,64,128,256,512]) :
    14125+14882+64*(1032+b) ≤ (1023-b-saving b)*336 ∧ b+saving b≤1023 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with rfl|rfl|rfl|rfl|rfl <;> decide +kernel

/-- A public common upper bound for the number of classes in one Pell equation.
The division keeps the fractional bits in the divisor estimate. -/
def classCap (b : ℕ) := 2^(1023-b-saving b)/coefficient

theorem classes {b c : ℕ} (allowed : b ∈ [0,64,128,256,512])
    (positive : 0<c) (small : c < 512*2^1023*2^b) :
    (c^2).divisors.card ≤ classCap b := by
  have powBound := (scaled positive small).trans_le
    (Nat.pow_le_pow_right (by decide : 0<2) (rates allowed).1)
  rw [pow_mul] at powBound
  have h := (Nat.pow_lt_pow_iff_left (by decide : 336≠0)).mp powBound
  exact (Nat.le_div_iff_mul_le (by decide : 0<coefficient)).mpr
    (by simpa only [Nat.mul_comm] using h.le)

/-- The finite trace sets cover all products in the event together. The
absolute value of c can depend on both traces. The counting hypothesis allows
a product to occur several times in the sum over trace pairs. -/
theorem fraction {b hits pop : ℕ} (allowed : b ∈ [0,64,128,256,512])
    {as : Finset ℕ} {bs : ℕ → Finset ℕ} {c : ℕ → ℕ → ℕ}
    (first : as.card ≤ 5*2^1023) (second : ∀ a∈as, (bs a).card ≤ 42*2^b)
    (sizes : ∀ a∈as, ∀ b'∈bs a, 0<c a b' ∧ c a b' < 512*2^1023*2^b)
    (count : hits ≤ ∑ a∈as, ∑ b'∈bs a, 1024*((c a b')^2).divisors.card)
    (total : 2^2046 < 21000000*pop) : 2^(saving b)*hits < pop := by
  have rows : hits ≤ (5*2^1023)*(42*2^b)*(1024*classCap b) := by
    refine count.trans ?_
    calc
      _ ≤ ∑ a∈as, (42*2^b)*(1024*classCap b) := by
        apply sum_le_sum
        intro a ha
        calc
          _ ≤ ∑ _i∈bs a, 1024*classCap b := by
            apply sum_le_sum
            intro i hi
            obtain ⟨pos,small⟩ := sizes a ha i hi
            exact Nat.mul_le_mul_left _ (classes allowed pos small)
          _ = (bs a).card*(1024*classCap b) := by simp
          _ ≤ _ := Nat.mul_le_mul_right _ (second _ ha)
      _ = as.card*((42*2^b)*(1024*classCap b)) := by simp
      _ ≤ _ := by simpa only [Nat.mul_assoc] using
          Nat.mul_le_mul_right ((42*2^b)*(1024*classCap b)) first
  have cap : classCap b*coefficient ≤ 2^(1023-b-saving b) := Nat.div_mul_le_self ..
  have exps : saving b+1023+b+(1023-b-saving b)=2046 := by have := (rates allowed).2; omega
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  refine lt_of_le_of_lt ?_ total
  calc
    _ ≤ 21000000*(2^(saving b)*((5*2^1023)*(42*2^b)*(1024*classCap b))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ rows)
    _ = (2^(saving b)*2^1023*2^b)*(classCap b*coefficient) := by unfold coefficient; ac_rfl
    _ ≤ (2^(saving b)*2^1023*2^b)*2^(1023-b-saving b) := Nat.mul_le_mul_left _ cap
    _ = _ := by rw [←pow_add,←pow_add,←pow_add,exps]

/-- Use the established denominator for the actual 2,048-bit sample. -/
theorem eligible_fraction {b hits : ℕ} (allowed : b ∈ [0,64,128,256,512])
    {as : Finset ℕ} {bs : ℕ → Finset ℕ} {c : ℕ → ℕ → ℕ}
    (first : as.card ≤ 5*2^1023) (second : ∀ a∈as, (bs a).card ≤ 42*2^b)
    (sizes : ∀ a∈as, ∀ b'∈bs a, 0<c a b' ∧ c a b' < 512*2^1023*2^b)
    (count : hits ≤ ∑ a∈as, ∑ b'∈bs a, 1024*((c a b')^2).divisors.card) :
    2^(saving b)*hits < MixedPrefixSample.eligible.card :=
  fraction allowed first second sizes count ChebyshevPrimeSample.eligible_count

end PrimeFactors.WeightedPairPopulation
