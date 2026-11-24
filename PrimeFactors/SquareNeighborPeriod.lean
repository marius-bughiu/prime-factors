import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- Coordinates of (a + √(a²+1))^j. At j=1 these begin the continued fraction
[a; 2a, 2a, ...] when a is a positive integer. -/
def squareNeighborPair (a : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | j+1 =>
    let z := squareNeighborPair a j
    (a*z.1+(a^2+1)*z.2, z.1+a*z.2)

theorem squareNeighbor_convergent_recurrence (a : ℤ) (j : ℕ) :
    squareNeighborPair a (j+2) =
      (2*a*(squareNeighborPair a (j+1)).1 + (squareNeighborPair a j).1,
       2*a*(squareNeighborPair a (j+1)).2 + (squareNeighborPair a j).2) := by
  simp only [squareNeighborPair]
  ext <;> dsimp <;> ring

theorem squareNeighbor_norm (a : ℤ) (j : ℕ) :
    (squareNeighborPair a j).1^2-(a^2+1)*(squareNeighborPair a j).2^2 = (-1)^j := by
  induction j with
  | zero => simp [squareNeighborPair]
  | succ j ih =>
    rw [pow_succ (-1 : ℤ) j, ← ih]
    simp only [squareNeighborPair]
    ring

/-- Reducing the numerator modulo a²+1 leaves just the jth power of a. -/
theorem squareNeighbor_reduced {R : Type*} [CommRing R] (f : ℤ →+* R)
    (a : ℤ) (vanishes : f (a^2+1) = 0) (j : ℕ) :
    f (squareNeighborPair a j).1 = f a ^ j := by
  induction j with
  | zero => simp [squareNeighborPair]
  | succ j ih =>
    change f (a*(squareNeighborPair a j).1 + (a^2+1)*(squareNeighborPair a j).2) = _
    rw [map_add, map_mul, map_mul, vanishes, zero_mul, add_zero, ih, pow_succ, mul_comm]

/-- This covers every finite subset of convergents, regardless of prefix length.
Every integer-square dependency has normalized numerator equal to one or minus one. -/
theorem squareNeighbor_no_mixed_root {R : Type*} [CommRing R] (f : ℤ →+* R)
    (a : ℤ) (vanishes : f (a^2+1) = 0) (s : Finset ℕ)
    (square : IsSquare (∏ j ∈ s, ((squareNeighborPair a j).1^2 -
      (a^2+1)*(squareNeighborPair a j).2^2))) :
    (∏ j ∈ s, f (squareNeighborPair a j).1) = 1 ∨
      (∏ j ∈ s, f (squareNeighborPair a j).1) = -1 := by
  simp only [squareNeighbor_norm] at square
  rw [Finset.prod_pow_eq_pow_sum s (fun j => j) (-1 : ℤ)] at square
  simp only [squareNeighbor_reduced f a vanishes]
  rw [Finset.prod_pow_eq_pow_sum s (fun j => j) (f a)]
  obtain ⟨z, hz⟩ := (isSquare_iff_exists_sq _).mp square
  have positive : (-1 : ℤ)^(∑ j ∈ s, j) = 1 := by
    rcases neg_one_pow_eq_or ℤ (∑ j ∈ s, j) with h | h
    · exact h
    · rw [h] at hz
      nlinarith [sq_nonneg z]
  obtain ⟨k, hk⟩ := (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤ) ≠ 1)).mp positive
  have minus : f a ^ 2 = -1 := by
    simpa only [map_add, map_one, map_pow, add_eq_zero_iff_eq_neg] using vanishes
  rw [hk, ← two_mul, pow_mul, minus]
  exact neg_one_pow_eq_or R k

/-- A square minus one at the next midpoint explains the contrasting one-step
factorization when a = 2b². -/
theorem squareNeighbor_fermat (b : ℤ) :
    (2*b^2)^2+1 = (2*b^2-2*b+1)*(2*b^2+2*b+1) := by ring

end PrimeFactors
