import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- One of the first two multiples has a signed representative within N/3 of zero. -/
theorem phaseResidues_center (H N : ℤ) (half : 2 * H ≤ N) :
    3 * H ≤ N ∨ (0 ≤ N - 2 * H ∧ 3 * (N - 2 * H) ≤ N) := by omega

/-- Rounding an observation with error at most 1/8 can absorb the unknown
fractional displacement of size at most 1/3. -/
theorem phaseResidues_round {a z : ℝ} {k j : ℤ} (center : |a| ≤ 1 / 3)
    (observed : |z - (k + a)| ≤ 1 / 8) (nearest : |z - j| ≤ 1 / 2) : j = k := by
  obtain ⟨ha, hA⟩ := abs_le.mp center
  obtain ⟨ho, hO⟩ := abs_le.mp observed
  obtain ⟨hn, hN⟩ := abs_le.mp nearest
  have upper : (j : ℝ) < (k : ℝ) + 1 := by linarith
  have lower : (k : ℝ) < (j : ℝ) + 1 := by linarith
  have u : j < k + 1 := by exact_mod_cast upper
  have l : k < j + 1 := by exact_mod_cast lower
  omega

/-- Reflection can change the sign of a decoded residue independently at
each auxiliary prime. The same squared congruence survives either choice. -/
theorem phaseResidues_local {m N b s a k j : ℤ} (lift : b * m * s = k * N + a)
    (sign : j = k ∨ j = -k) : (j * N) ^ 2 ≡ a ^ 2 [ZMOD m] := by
  have modSq : (k * N) ^ 2 ≡ a ^ 2 [ZMOD m] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨b * s * (a - k * N), ?_⟩
    linear_combination -(a - k * N) * lift
  rcases sign with rfl | rfl
  · exact modSq
  · simpa using modSq

/-- Squaring a signed modular lift gives a short nonnegative quotient.
Once the CRT residue of that quotient is known, it is unique. -/
theorem phaseResidues_reconstruct {a N b k r M : ℕ} (unit : M.Coprime N)
    (lift : a ^ 2 = N * k + b ^ 2) (cong : a ^ 2 ≡ N * r + b ^ 2 [MOD M])
    (short : k < M) (canonical : r < M) : N * r + b ^ 2 = a ^ 2 := by
  rw [lift] at cong
  have eq := (Nat.ModEq.cancel_left_of_coprime unit
    (cong.add_right_cancel' (b ^ 2))).eq_of_lt_of_lt short canonical
  simpa [eq] using lift.symm

/-- The public stopping condition suffices even at the edge of the central third. -/
theorem phaseResidues_short {a N b k M : ℕ} (pos : 0 < N) (center : 3 * a ≤ N)
    (size : N < 9 * M) (lift : a ^ 2 = N * k + b ^ 2) : k < M := by
  by_contra! large
  have sqBound := Nat.mul_le_mul center center
  have lhs := Nat.mul_le_mul_left N large
  have rhs := Nat.mul_lt_mul_of_pos_left size pos
  nlinarith only [sqBound, lhs, rhs, lift, Nat.zero_le (b ^ 2)]

/-- A nonzero sign at a shared odd prime fixes the orientation at later moduli. -/
theorem phaseResidues_orient {r m u a : ℤ} (divides : r ∣ m)
    (readout : u ≡ a [ZMOD m] ∨ u ≡ -a [ZMOD m]) (chosen : u ≡ a [ZMOD r])
    (distinct : ¬ a ≡ -a [ZMOD r]) : u ≡ a [ZMOD m] :=
  readout.resolve_right fun h => distinct (chosen.symm.trans (h.of_dvd divides))

end PrimeFactors
