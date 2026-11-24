import PrimeFactors.Fermat

namespace PrimeFactors

/-- A divisor interval centered at `(m + 1) / (2*a)`. Its endpoints can be computed
from the product and weights alone, before any candidate divisor is known. -/
def InWeightedDivisorBand (a m p : ℕ) : Prop :=
  (2 * (a : ℤ) * p - ((m : ℤ) + 1)) ^ 2 ≤ 2 * (m : ℤ)

/-- Two linear endpoint inequalities certify band membership anywhere in an interval.
Taking `r` to be the floor square root of `2*m` gives the full integer band. -/
theorem weightedBand_of_bounds {a m p r : ℕ} (radius : r ^ 2 ≤ 2 * m)
    (left : m + 1 ≤ 2 * a * p + r) (right : 2 * a * p ≤ m + 1 + r) :
    InWeightedDivisorBand a m p := by
  unfold InWeightedDivisorBand
  zify at radius left right
  have lo : 0 ≤ (r : ℤ) + (2 * a * p - ((m : ℤ) + 1)) := by omega
  have hi : 0 ≤ (r : ℤ) - (2 * a * p - ((m : ℤ) + 1)) := by omega
  nlinarith only [mul_nonneg lo hi, radius]

/-- One weighted sum covers a whole interval of possible divisors. The integer
`m` is the ceiling square root of `4abn`, as in the Lawrence–Lehman method. -/
theorem weightedBand_sum {n a b p q : ℕ} (product : p * q = n)
    (band : InWeightedDivisorBand a (ceilSqrt (4 * a * b * n)) p) :
    a * p + b * q = ceilSqrt (4 * a * b * n) := by
  let m := ceilSqrt (4 * a * b * n)
  change (2 * (a : ℤ) * p - ((m : ℤ) + 1)) ^ 2 ≤ 2 * (m : ℤ) at band
  have lower : m ≤ a * p + b * q := by
    apply ceilSqrt_le_iff.mpr
    rw [← product]
    zify
    nlinarith only [sq_nonneg ((a : ℤ) * p - b * q)]
  have upper : 4 * a * b * n ≤ m ^ 2 := ceilSqrt_le_iff.mp (le_refl m)
  have eqn : (2 * (a : ℤ) * p - ((m : ℤ) + 1)) ^ 2 + 4 * a * b * n -
      ((m : ℤ) + 1) ^ 2 = 4 * a * p * (a * p + b * q - ((m : ℤ) + 1)) := by
    rw [← product, Nat.cast_mul]
    ring
  change a * p + b * q = m
  apply le_antisymm _ lower
  by_contra! large
  zify at large upper
  have nonneg : 0 ≤ (a : ℤ) * p + b * q - ((m : ℤ) + 1) := by omega
  have coeff : 0 ≤ 4 * (a : ℤ) * p := by positivity
  nlinarith only [mul_nonneg coeff nonneg, eqn, upper, band]

/-- Any divisor in the band gives an explicit square root of the one discriminant. -/
theorem weightedBand_discriminant {n a b p q : ℕ} (product : p * q = n)
    (band : InWeightedDivisorBand a (ceilSqrt (4 * a * b * n)) p) :
    let m : ℤ := ceilSqrt (4 * a * b * n)
    (2 * (a : ℤ) * p - m) ^ 2 = m ^ 2 - 4 * a * b * n := by
  dsimp only
  rw [← weightedBand_sum product band, ← product]
  push_cast
  ring

/-- A nonsquare rejects every divisor in the interval at once. -/
theorem weightedBand_excludes {n a b p : ℕ}
    (miss : ¬ IsSquare ((ceilSqrt (4 * a * b * n) : ℤ) ^ 2 - 4 * a * b * n))
    (band : InWeightedDivisorBand a (ceilSqrt (4 * a * b * n)) p) : ¬ p ∣ n := by
  rintro ⟨q, hq⟩
  apply miss
  exact ⟨_, by rw [← pow_two]; exact (weightedBand_discriminant hq.symm band).symm⟩

/-- A square leaves at most the two linear candidates, which can be tested for divisibility. -/
theorem weightedBand_two_candidates {n a b p q : ℕ} {d : ℤ} (product : p * q = n)
    (band : InWeightedDivisorBand a (ceilSqrt (4 * a * b * n)) p)
    (square : (ceilSqrt (4 * a * b * n) : ℤ) ^ 2 - 4 * a * b * n = d ^ 2) :
    let m : ℤ := ceilSqrt (4 * a * b * n)
    2 * (a : ℤ) * p = m - d ∨ 2 * (a : ℤ) * p = m + d := by
  let m : ℤ := ceilSqrt (4 * a * b * n)
  have eqn : (2 * (a : ℤ) * p - m) ^ 2 = d ^ 2 :=
    (weightedBand_discriminant product band).trans square
  have zero : (2 * (a : ℤ) * p - m - d) * (2 * (a : ℤ) * p - m + d) = 0 := by
    nlinarith only [eqn]
  change 2 * (a : ℤ) * p = m - d ∨ 2 * (a : ℤ) * p = m + d
  rcases mul_eq_zero.mp zero with h | h <;> omega

private theorem ceilSqrt_eq_of_bounds {n m : ℕ} (below : (m - 1) ^ 2 < n)
    (above : n ≤ m ^ 2) : ceilSqrt n = m := by
  apply le_antisymm (ceilSqrt_le_iff.mpr above)
  by_contra! small
  have := ceilSqrt_le_iff.mp (show ceilSqrt n ≤ m - 1 by omega)
  omega

/-- The weights 3 and 2 exclude fourteen consecutive integers with one nonsquare. -/
theorem weightedBand_example_exclusion (p : ℕ) (lo : 145 ≤ p) (hi : p ≤ 158) :
    ¬ p ∣ 34387 := by
  have hm : ceilSqrt (4 * 3 * 2 * 34387) = 909 := ceilSqrt_eq_of_bounds (by decide) (by decide)
  apply weightedBand_excludes (a := 3) (b := 2)
  · rw [hm]
    rintro ⟨d, sq⟩
    have absEq := congrArg Int.natAbs sq
    rw [Int.natAbs_mul, ← pow_two] at absEq
    change 993 = d.natAbs ^ 2 at absEq
    have impossible : (993 : ℕ).sqrt ^ 2 = 993 := by rw [absEq, Nat.sqrt_eq']
    norm_num at impossible
  · rw [hm]
    apply weightedBand_of_bounds (r := 42) (by decide) <;> omega

/-- Changing the weights isolates the sole divisor in a different interval of the same input. -/
theorem weightedBand_example_recovery (p : ℕ) (lo : 124 ≤ p) (hi : p ≤ 139) :
    p ∣ 34387 ↔ p = 137 := by
  have hm : ceilSqrt (4 * 2 * 1 * 34387) = 525 := ceilSqrt_eq_of_bounds (by decide) (by decide)
  constructor
  · rintro ⟨q, prod⟩
    have band : InWeightedDivisorBand 2 (ceilSqrt (4 * 2 * 1 * 34387)) p := by
      rw [hm]
      apply weightedBand_of_bounds (r := 32) (by decide) <;> omega
    have roots := weightedBand_two_candidates (d := (23 : ℤ)) prod.symm band (by rw [hm]; decide)
    dsimp only at roots
    rw [hm] at roots
    omega
  · rintro rfl
    exact ⟨251, by decide⟩

end PrimeFactors
