import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PrimeFactors.NormResidueCurve

open scoped BigOperators

/-- The j-th coefficient of a Taylor jet needs only m-j powers of Q
when the variable is already a multiple of Q. -/
theorem jet_dvd {Q h : ℤ} (step : Q ∣ h) (m : ℕ) (c : ℕ → ℤ)
    (conditions : ∀ j < m, Q^(m-j) ∣ c j) :
    Q^m ∣ ∑ j ∈ Finset.range m, c j * h^j := by
  apply Finset.dvd_sum
  intro j hj
  have jl := Finset.mem_range.mp hj
  have term := mul_dvd_mul (conditions j jl) (pow_dvd_pow_of_dvd step j)
  rwa [← pow_add, Nat.sub_add_cancel jl.le] at term

/-- Smallness turns the congruences on the local coefficients into
an exact vanishing equation at every integral point in the chart. -/
theorem auxiliary_zero {Q h F : ℤ} {m : ℕ} {c : ℕ → ℤ}
    (step : Q ∣ h) (conditions : ∀ j < m, Q^(m-j) ∣ c j)
    (expansion : F ≡ ∑ j ∈ Finset.range m, c j * h^j [ZMOD Q^m])
    (size : F.natAbs < (Q^m).natAbs) : F = 0 := by
  have vanish := jet_dvd step m c conditions
  have diff := Int.modEq_iff_dvd.mp expansion
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (by simpa using dvd_sub vanish diff) size

/-- On a smooth branch one can cancel the other linear factor of
the difference of the two squares. The Bézout coefficients attest that
the derivative factor is invertible at the working precision. -/
theorem same_branch {M B y f r s : ℤ}
    (unit : r*(B*(y+f))+s*M=1)
    (equation : M ∣ B*(y^2-f^2)) : M ∣ y-f := by
  obtain ⟨k, hk⟩ := equation
  refine ⟨r*k+s*(y-f), ?_⟩
  linear_combination r*hk - (y-f)*unit

/-- One Newton update doubles the number of correct prime-power digits
for a quadratic whenever the derivative has a supplied modular inverse. -/
theorem newton_lift {m B y C v k w : ℤ}
    (error : B*y^2-C=m*k) (inverse : 2*B*y*v-1=m*w) :
    m^2 ∣ B*(y-v*(m*k))^2-C := by
  refine ⟨B*v^2*k^2-k*w, ?_⟩
  linear_combination error - (m*k)*inverse

end PrimeFactors.NormResidueCurve
