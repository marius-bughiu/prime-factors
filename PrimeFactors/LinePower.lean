import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- Collisions persist under every common multiple of the degree. -/
theorem linePower_collision_multiple {R : Type*} [CommRing R] {x y : R}
    {e d : ℕ} (divides : e ∣ d)
    (collision : (Polynomial.dickson 1 (1 : R) e).eval x =
      (Polynomial.dickson 1 (1 : R) e).eval y) :
    (Polynomial.dickson 1 (1 : R) d).eval x =
      (Polynomial.dickson 1 (1 : R) d).eval y := by
  obtain ⟨k, rfl⟩ := divides
  rw [Nat.mul_comm, Polynomial.dickson_one_one_mul]
  simpa only [Polynomial.eval_comp] using
    congrArg (Polynomial.eval · (Polynomial.dickson 1 (1 : R) k)) collision

/-- Two unit traces coincide precisely for equal or inverse elements. -/
theorem linePower_trace_eq {F : Type*} [Field F] {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    x + x⁻¹ = y + y⁻¹ ↔ x = y ∨ x*y = 1 := by
  have h : (x * y) * ((x+x⁻¹) - (y+y⁻¹)) = (x-y)*(x*y-1) := by
    field_simp
    ring
  rw [← sub_eq_zero, ← sub_eq_zero (a := x*y) (b := 1), ← sub_eq_zero (a := x) (b := y),
    ← mul_eq_zero, ← h, mul_eq_zero, or_iff_right (mul_ne_zero hx hy)]

/-- A quadratic trace goes to 2 if its lift is annihilated by the degree. -/
theorem linePower_neutral {F : Type*} [Field F] {x : F} (hx : x ≠ 0) {d : ℕ} :
    (Polynomial.dickson 1 (1 : F) d).eval (x+x⁻¹) = 2 ↔ x^d = 1 := by
  rw [Polynomial.dickson_one_one_eval_add_inv x x⁻¹ (mul_inv_cancel₀ hx), inv_pow]
  have one_trace : (2 : F) = 1 + (1 : F)⁻¹ := by simp; ring
  rw [one_trace, linePower_trace_eq (pow_ne_zero d hx) one_ne_zero, mul_one, or_self]

/-- The two complementary factors of p+1 divide opposite shifts of q. Here
u=(B-A)v, a=A u+1, b=B u+1, p=2ab-1 and q=1+2B²va. -/
theorem linePower_opposite_shifts (A B v : ℤ) :
    let u := (B-A)*v
    let a := A*u+1
    let b := B*u+1
    let p := 2*a*b-1
    let q := 1+2*B^2*v*a
    p+1 ∣ q^2-1 := by
  dsimp
  use 2*B^2*v*(A*B*v+1)
  ring

/-- The degree N²-1 inherits the complete nonsplit order p+1. -/
theorem linePower_product_degree {p q : ℤ} (h : p+1 ∣ q^2-1) :
    p+1 ∣ (p*q)^2-1 := by
  obtain ⟨k, hk⟩ := h
  use (p-1)*q^2+k
  linear_combination hk

/-- Independent local hits of probabilities on opposite sides of one half
separate the hidden primes with probability at least one half. -/
theorem linePower_half_success (s t : ℚ) (hs : 1 ≤ 2*s) (ht : 2*t ≤ 1) :
    1 ≤ 2*(s+t-2*s*t) := by
  have h := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr ht)
  apply sub_nonneg.mp
  convert h using 1
  ring

end PrimeFactors
