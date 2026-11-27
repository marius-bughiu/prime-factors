import Mathlib.Data.Nat.GCD.Basic

/-! The two surviving order classes on the fresh control. Count their
elements in any cyclic image of the two local power maps. -/
namespace PrimeFactors.PoweredTraceLimit

/-- The p-side orders are 7 or 14, each with six elements in a cyclic group
when it occurs. The q-side order 8 has four. -/
def count (P Q : ℕ) : ℕ :=
  (if 7∣P then 6 else 0) * (if 8∣Q then 4 else 0) +
    (if 14∣P then 6 else 0) * (if 8∣Q then 4 else 0)

/-- No choice of a single exponent for a uniform seed makes more than
three sevenths of the image land in the two order classes. -/
theorem upper {P Q : ℕ} (hp : 0<P) (hq : 0<Q) : 7*count P Q ≤ 3*(P*Q) := by
  by_cases h8 : 8∣Q
  · have q8 := Nat.le_of_dvd hq h8
    by_cases h14 : 14∣P
    · have p14 := Nat.le_of_dvd hp h14
      have h7 : 7∣P := dvd_trans (by decide : 7∣14) h14
      have prod := Nat.mul_le_mul p14 q8
      simp only [count,if_pos h7,if_pos h14,if_pos h8]
      omega
    · by_cases h7 : 7∣P
      · have prod := Nat.mul_le_mul (Nat.le_of_dvd hp h7) q8
        simp only [count,if_pos h7,if_neg h14,if_pos h8]
        omega
      · simp [count,h7,h8,h14]
  · simp [count,h8]

theorem attained : 7*count 7 8=3*(7*8) := by decide

/-- Whenever either winning order pair occurs, the same public exponent
14 kills the first component and leaves the second one nontrivial. -/
theorem shortcut {r t : ℕ} (h : (r=7 ∨ r=14) ∧ t=8) : r∣14 ∧ ¬t∣14 := by
  rcases h with ⟨hr,rfl⟩
  rcases hr with rfl|rfl <;> decide

end PrimeFactors.PoweredTraceLimit
