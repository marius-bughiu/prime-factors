import Mathlib.Algebra.Ring.Units
import Mathlib.Tactic.LinearCombination

/-! Consecutive reciprocal trace keys over a ring, including composite moduli. -/

namespace PrimeFactors.LiftedPeriodTrace

variable {R : Type*} [CommRing R]

/-- With two seed values, the next trace needs only multiplication by the sum of
the forward and backward steps. The step difference can be a zero divisor. -/
theorem next_key (v w h b : R) (inv : h * b = 1) :
    v * h * h + w * b * b = (h + b) * (v * h + w * b) - (v + w) := by
  linear_combination -(v + w) * inv

/-- At signed index k the two summands are inverse units. -/
def key (v h : Rˣ) (k : ℤ) : R :=
  (v : R) * ((h ^ k : Rˣ) : R) + (↑(v⁻¹) : R) * (((h⁻¹) ^ k : Rˣ) : R)

theorem key_as_trace (v h : Rˣ) (k : ℤ) :
    key v h k = (↑(v * h ^ k) : R) + (↑((v * h ^ k)⁻¹) : R) := by
  simp [key, mul_comm]

/-- The recurrence for every signed range of the left scan or right table. -/
theorem recurrence (v h : Rˣ) (k : ℤ) :
    key v h (k + 2) = ((h : R) + (↑(h⁻¹) : R)) * key v h (k + 1) - key v h k := by
  rw [show k + 2 = (k + 1) + 1 by omega]
  simp only [key, zpow_add, zpow_one, Units.val_mul]
  simpa only [mul_assoc] using
    next_key ((v : R) * ((h ^ k : Rˣ) : R))
      ((↑(v⁻¹) : R) * (((h⁻¹) ^ k : Rˣ) : R)) (h : R) (↑(h⁻¹) : R) h.mul_inv

end PrimeFactors.LiftedPeriodTrace
