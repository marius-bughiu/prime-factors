import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace PrimeFactors.DivisorWindowDimension

/-- The classical LLL first-vector height bound, raised to 4(k+1),
with N bounded above by 2^2048 and all divisors bounded below by 2^1023.
k is the degree, m the multiplicity, and the radius is 2^w. -/
def sufficient (k m w : ℕ) : Prop :=
  (k+1)^(2*(k+1)) * 2^(4096*m*(m+1)+(2*w+1)*k*(k+1)) < 2^(4092*m*(k+1))

private theorem exponent_gap {k m w b : ℕ} (pass : sufficient k m w)
    (dim : 2^b ≤ (k+1)^2) :
    b*(k+1) + (4096*m*(m+1)+(2*w+1)*k*(k+1)) < 4092*m*(k+1) := by
  apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
  rw [pow_add,pow_mul]
  apply lt_of_le_of_lt _ pass
  apply Nat.mul_le_mul_right
  rw [pow_mul]
  exact Nat.pow_le_pow_left dim _

/-- Even optimizing the jet multiplicity, a power-of-two radius 2^510
requires at least 1044 rows for this specific sufficient inequality. -/
theorem least_dimension {k m : ℕ} (pass : sufficient k m 510) : 1044 ≤ k+1 := by
  let K : ℤ := k
  let M : ℤ := m
  let E := 4092*M*(K+1) - (4096*M*(M+1)+1021*K*(K+1))
  have upper : 1024*E ≤ 1024*K*(K-1023)+(K+1)^2 := by
    dsimp [E]
    nlinarith only [sq_nonneg (1024*(K-2*M)-(K+1))]
  have nonneg : 0 ≤ K := Int.natCast_nonneg _
  by_contra! small
  have cap : K ≤ 1042 := by dsimp [K]; omega
  by_cases early : k ≤ 1022
  · have h := exponent_gap (b:=0) pass (by simpa only [pow_zero] using (Nat.one_le_pow 2 (k+1) (by omega)))
    have e : (0:ℤ) < E := by
      simp only [Nat.zero_mul,Nat.zero_add] at h
      change 4096*m*(m+1)+1021*k*(k+1) < 4092*m*(k+1) at h
      dsimp [E,K,M]; exact sub_pos.mpr (by exact_mod_cast h)
    have a : K ≤ 1022 := by dsimp [K]; exact_mod_cast early
    have term := mul_le_mul_of_nonneg_left (show K-1023 ≤ -1 by omega) nonneg
    have square := mul_le_mul_of_nonneg_right (show K+1 ≤ 1023 by omega) (show 0 ≤ K+1 by omega)
    nlinarith only [upper,term,square,show 1 ≤ E by omega,nonneg]
  · have dim : 2^20 ≤ (k+1)^2 := Nat.pow_le_pow_left (by omega : 1024 ≤ k+1) 2
    have h := exponent_gap pass dim
    have e : 20*(K+1) < E := by
      change 20*(k+1)+(4096*m*(m+1)+1021*k*(k+1)) < 4092*m*(k+1) at h
      have hz : 20*(K+1)+(4096*M*(M+1)+1021*K*(K+1)) < 4092*M*(K+1) := by
        dsimp [K,M]; exact_mod_cast h
      dsimp [E]; omega
    by_cases edge : K=1042
    · rw [edge] at upper e
      omega
    · have term := mul_le_mul_of_nonneg_left (show K-1023 ≤ 18 by omega) nonneg
      have square := mul_le_mul_of_nonneg_right (show K+1 ≤ 2048 by omega) (show 0 ≤ K+1 by omega)
      nlinarith only [upper,term,square,e,nonneg]

private theorem sufficient_of_square {k m w b : ℕ} (size : (k+1)^2 < 2^b)
    (budget : b*(k+1)+(4096*m*(m+1)+(2*w+1)*k*(k+1)) = 4092*m*(k+1)) :
    sufficient k m w := by
  unfold sufficient
  rw [← budget,pow_add 2 (b*(k+1)) _,pow_mul (k+1) 2 (k+1),pow_mul 2 b (k+1)]
  exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left size (Nat.succ_ne_zero k)) (Nat.pow_pos (by decide : 0 < 2))

theorem attained : sufficient 1043 521 510 :=
  sufficient_of_square (b:=21) (by decide) (by decide)

end PrimeFactors.DivisorWindowDimension
