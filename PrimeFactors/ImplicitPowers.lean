import PrimeFactors.Certificate
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Union
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors

/-- A stationary trace, written as a sum of two lifts congruent modulo m,
has discriminant zero modulo m². -/
theorem implicitPower_trace_square {m x y tau value : ℤ}
    (stationary : x ≡ y [ZMOD m]) (trace : tau ≡ x + y [ZMOD m ^ 2])
    (product : x * y ≡ value [ZMOD m ^ 2]) : tau ^ 2 ≡ 4 * value [ZMOD m ^ 2] := by
  have diff : m ∣ y - x := stationary.dvd
  have doubled : m ^ 2 ∣ (y - x) ^ 2 := pow_dvd_pow_of_dvd diff 2
  have cancel : (x + y) ^ 2 ≡ 4 * (x * y) [ZMOD m ^ 2] := by
    apply Int.modEq_iff_dvd.mpr
    convert Int.dvd_neg.mpr doubled using 1
    ring
  exact ((trace.pow 2).trans cancel).trans (product.mul_left 4)

/-- For fixed C = aN and exponent E, the possible short second weights
are roots of the same monic quadratic modulo m². -/
theorem implicitPower_weight_quadratic {m c b E tau : ℤ}
    (base : E ≡ c + b - tau [ZMOD m ^ 2]) (trace : tau ^ 2 ≡ 4 * (c * b) [ZMOD m ^ 2]) :
    m ^ 2 ∣ (c + b - E) ^ 2 - 4 * (c * b) := by
  have same : c + b - E ≡ tau [ZMOD m ^ 2] := by
    apply Int.modEq_iff_dvd.mpr
    convert Int.dvd_neg.mpr base.dvd using 1
    ring
  exact ((same.pow 2).trans trace).symm.dvd

/-- Three roots of a monic quadratic force its modulus to divide their
Vandermonde product, including over a composite modulus. -/
theorem implicitPower_vandermonde {m c E x y z : ℤ}
    (hx : m ∣ (c + x - E) ^ 2 - 4 * (c * x))
    (hy : m ∣ (c + y - E) ^ 2 - 4 * (c * y))
    (hz : m ∣ (c + z - E) ^ 2 - 4 * (c * z)) :
    m ∣ (x - y) * (x - z) * (y - z) := by
  convert dvd_add (dvd_add (dvd_mul_of_dvd_left hx (y - z))
    (dvd_mul_of_dvd_left hy (z - x))) (dvd_mul_of_dvd_left hz (x - y)) using 1
  ring

/-- A common integer-exponent class allows at most two distinct second
weights when the cube of their interval diameter is less than the modulus. -/
theorem implicitPower_at_most_two {m c E : ℤ} {width : ℕ} (weights : Finset ℤ)
    (roots : ∀ x ∈ weights, m ∣ (c + x - E) ^ 2 - 4 * (c * x))
    (diameter : ∀ x ∈ weights, ∀ y ∈ weights, (x - y).natAbs ≤ width)
    (small : width ^ 3 < m.natAbs) : weights.card ≤ 2 := by
  by_contra! many
  obtain ⟨x, hx, y, hy, z, hz, xy, xz, yz⟩ := Finset.two_lt_card.mp many
  have divides := implicitPower_vandermonde (roots x hx) (roots y hy) (roots z hz)
  have upper : ((x - y) * (x - z) * (y - z)).natAbs ≤ width ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, pow_succ, pow_two]
    exact Nat.mul_le_mul (Nat.mul_le_mul (diameter x hx y hy) (diameter x hx z hz))
      (diameter y hy z hz)
  exact (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr xy) (sub_ne_zero.mpr xz))
    (sub_ne_zero.mpr yz)) (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs divides (upper.trans_lt small))

/-- In the odd part of the remaining modulus, a fixed pair of weights
and a fixed exponent class determine the row residue. -/
theorem implicitPower_same_root {r c b E s t : ℤ} (unit : IsCoprime r (2 * b))
    (hs : E ≡ c + b - 2 * b * s [ZMOD r]) (ht : E ≡ c + b - 2 * b * t [ZMOD r]) :
    s ≡ t [ZMOD r] := by
  apply Int.modEq_iff_dvd.mpr
  apply unit.dvd_of_dvd_mul_left
  convert (ht.symm.trans hs).dvd using 1
  ring

/-- If both weights have two factors of l, removing one of them preserves
the defining lattice whenever m = l*r and l is coprime to r. A shortest
nonzero vector cannot have this extra factor in both normalized weights. -/
theorem implicitPower_divide_lattice {l r u v s n : ℤ} (cop : IsCoprime r l)
    (row : l*r ∣ (l^2*v)*s^2-(l^2*u)*n) :
    l*r ∣ (l*v)*s^2-(l*u)*n := by
  have h : r ∣ (l^2*v)*s^2-(l^2*u)*n := (dvd_mul_left r l).trans row
  have one : r ∣ l*(v*s^2-u*n) := by
    apply cop.dvd_of_dvd_mul_left
    convert h using 1
    ring
  have both := cop.dvd_of_dvd_mul_left one
  convert mul_dvd_mul_left l both using 1
  ring

/-- At a prime in the common content, dividing the trace by that content
leaves a nonzero quadratic or linear polynomial in the row residue. -/
theorem implicitPower_content_roots {K : Type*} [Field K] (rows : Finset K) {v t u : K}
    (nonzero : v ≠ 0 ∨ u ≠ 0) (roots : ∀ x ∈ rows, v*x^2-t*x+u=0) :
    rows.card ≤ 2 := by
  by_contra! many
  obtain ⟨x, hx, y, hy, z, hz, xy, xz, yz⟩ := Finset.two_lt_card.mp many
  have fx := roots x hx
  have fy := roots y hy
  have fz := roots z hz
  by_cases zero : v = 0
  · have distinct : t*(x-y) = 0 := by linear_combination fy - fx + (x^2-y^2)*zero
    have teq := (mul_eq_zero.mp distinct).resolve_right (sub_ne_zero.mpr xy)
    exact (nonzero.resolve_left (not_ne_iff.mpr zero)) (by simpa [zero, teq] using fx)
  · have vanished : v*((x-y)*(x-z)*(y-z)) = 0 := by
      linear_combination (y-z)*fx + (z-x)*fy + (x-y)*fz
    exact (mul_ne_zero zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr xy)
      (sub_ne_zero.mpr xz)) (sub_ne_zero.mpr yz))) vanished

/-- All shifted ranges in one known orbit can be replaced by their union.
A point of the union gives a collision on at least one of the original rows. -/
theorem implicitPower_shared_window {G : Type*} [Group G] (a x : G)
    (offsets : Finset ℤ) (window : ℤ → Finset ℤ) :
    (∃ k ∈ offsets, ∃ j ∈ window k, a ^ j = x * a ^ k) ↔
      ∃ e ∈ offsets.biUnion (fun k => (window k).image (fun j => j-k)), a ^ e = x := by
  constructor
  · rintro ⟨k, hk, j, hj, eq⟩
    refine ⟨j-k, Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩, ?_⟩
    rw [zpow_sub, eq, mul_inv_cancel_right]
  · rintro ⟨e, he, eq⟩
    obtain ⟨k, hk, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    refine ⟨k, hk, j, hj, ?_⟩
    calc
      a ^ j = a ^ (j-k+k) := by rw [sub_add_cancel]
      _ = x * a ^ k := by rw [zpow_add, eq]

/-- One actual block evaluation from the public 150235091 experiment.
The fold tracks the current root and product modulo N at each iteration. -/
theorem implicitPower_block_example :
    let n := 150235091
    let alpha := 81017472
    let point := 23098282
    let state := (List.range 55).foldl (fun (state : ℕ × ℕ) _ =>
      (state.1 * alpha % n, state.2 * (n + point - state.1) % n)) (1, 1)
    2 ^ 4900 % n = alpha ∧
      (2 ^ 1396 % n * (alpha ^ 30686 % n)) % n = point ∧
      state.2 = 56209319 ∧ Nat.gcd state.2 n = 10007 ∧ 10007 * 15013 = n := by
  decide +kernel

theorem implicitPower_exact_example : ExactFactorization 150235091 [10007, 15013] := by
  apply ExactFactorization.cons (n := 15013) (p := 10007) (by norm_num)
  exact ExactFactorization.cons (n := 1) (p := 15013) (by norm_num) exactFactorization_nil

end PrimeFactors
