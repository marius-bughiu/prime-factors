import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- The first natural number whose square is at least the input. -/
def ceilSqrt : ℕ → ℕ
  | 0 => 0
  | n + 1 => n.sqrt + 1

theorem ceilSqrt_le_iff {n a : ℕ} : ceilSqrt n ≤ a ↔ n ≤ a ^ 2 := by
  cases n with
  | zero => simp [ceilSqrt]
  | succ n => exact Nat.sqrt_lt'

/-- Each successful difference-of-squares test yields a product identity. -/
theorem fermat_split {n a b : ℕ} (hb : b ≤ a) (hit : a ^ 2 = n + b ^ 2) :
    n = (a - b) * (a + b) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [Nat.add_sub_cancel_left]
  nlinarith

/-- Suppose the factors are `p` and `p + 2*d`, with midpoint `p + d`. A search
from the ceiling square root through offset `k` reaches their midpoint whenever
the squared half-gap fits the increase in the squared search bound. -/
theorem fermat_window (p d k : ℕ)
    (gap : d ^ 2 ≤ 2 * ceilSqrt (p * (p + 2 * d)) * k + k ^ 2) :
    let n := p * (p + 2 * d)
    let r := ceilSqrt n
    r ≤ p + d ∧ p + d ≤ r + k ∧ (p + d) ^ 2 = n + d ^ 2 := by
  let n := p * (p + 2 * d)
  let r := ceilSqrt n
  change d ^ 2 ≤ 2 * r * k + k ^ 2 at gap
  change r ≤ p + d ∧ p + d ≤ r + k ∧ (p + d) ^ 2 = n + d ^ 2
  have mid : (p + d) ^ 2 = n + d ^ 2 := by dsimp [n]; ring
  have lower : n ≤ r ^ 2 := ceilSqrt_le_iff.mp (le_refl r)
  refine ⟨ceilSqrt_le_iff.mpr (by omega), ?_, mid⟩
  apply Nat.mul_self_le_mul_self_iff.mp
  nlinarith only [mid, lower, gap]

/-- A search which excluded every square in its tested interval can also
exclude each proposed factor pair satisfying the half-gap bound. -/
theorem fermat_excludes_close_pair {n k p d : ℕ}
    (miss : ∀ a, ceilSqrt n ≤ a → a ≤ ceilSqrt n + k → ∀ b : ℕ, a ^ 2 ≠ n + b ^ 2)
    (gap : d ^ 2 ≤ 2 * ceilSqrt n * k + k ^ 2) :
    n ≠ p * (p + 2 * d) := by
  rintro rfl
  obtain ⟨lo, hi, hit⟩ := fermat_window p d k gap
  exact miss (p + d) lo hi d hit

/-- Test exactly `count` consecutive midpoints starting at the ceiling square root. -/
def fermatWindowMiss (n count : ℕ) : Bool :=
  (List.range count).all fun i =>
    let delta := (ceilSqrt n + i) ^ 2 - n
    decide (delta.sqrt ^ 2 ≠ delta)

/-- A finite computation certifies the exclusion even when the remaining factors are unknown. -/
theorem excludes_of_fermatWindowMiss {n k p d : ℕ}
    (miss : fermatWindowMiss n (k + 1) = true)
    (gap : d ^ 2 ≤ 2 * ceilSqrt n * k + k ^ 2) :
    n ≠ p * (p + 2 * d) := by
  apply fermat_excludes_close_pair ?_ gap
  intro a lo hi b hit
  let i := a - ceilSqrt n
  have index : i ∈ List.range (k + 1) := List.mem_range.mpr (by dsimp [i]; omega)
  have midpoint : ceilSqrt n + i = a := by dsimp [i]; omega
  have checked := List.all_eq_true.mp miss i index
  change decide (((ceilSqrt n + i) ^ 2 - n).sqrt ^ 2 ≠ (ceilSqrt n + i) ^ 2 - n) = true at checked
  simp [midpoint, hit, Nat.sqrt_eq'] at checked

example : 5959 = (80 - 21) * (80 + 21) :=
  fermat_split (by decide) (by decide)

/-- The 100-digit input used in the eight-midpoint cutoff benchmark. -/
def eightMidpointTarget : ℕ :=
  2500000000000000000000002828427129198665669804032100000002311766726231161188458433341755932316532737

/-- Eight square tests rule out every even factor gap up to twice the stated half-gap. -/
theorem eightMidpoint_exclusion (p d : ℕ) (h : d ≤ 26457513110645905905016165) :
    eightMidpointTarget ≠ p * (p + 2 * d) := by
  let r := 50000000000000000000000028284271291986656698040313
  have hi : ceilSqrt eightMidpointTarget ≤ r := ceilSqrt_le_iff.mpr (by decide)
  have lo : ¬ ceilSqrt eightMidpointTarget ≤ r - 1 := fun h' =>
    (by decide : ¬ eightMidpointTarget ≤ (r - 1) ^ 2) (ceilSqrt_le_iff.mp h')
  have start : ceilSqrt eightMidpointTarget = r := by dsimp [r] at *; omega
  apply excludes_of_fermatWindowMiss (k := 7)
  · rw [fermatWindowMiss, start, show List.range (7 + 1) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
    norm_num [r, eightMidpointTarget]
  · rw [start]
    exact (Nat.pow_le_pow_left h 2).trans (by decide)

end PrimeFactors
