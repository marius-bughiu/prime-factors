import PrimeFactors.QuotientStripLocalization

/-!
# Restricting factor coordinates with ordinary second moments

The strip's count, coordinate sums, squares, and cross product suffice for
both tests. A factor row lies on `xy = N`. Substitution converts its residual
Gram determinant to a quartic, and an integer linear projection to two
quadratic inequalities. Neither calculation requires a higher strip moment.
-/

namespace PrimeFactors.QuotientStripHyperbola

open Finset PrimeFactors.QuotientStripLocalization

/-- Determinant after deleting a proposed row on the hyperbola and clearing
the squared denominator. The six arguments are count, Σx, Σy, Σx², Σxy, Σy². -/
def quartic (t a b c d h N k : ℤ) : ℤ :=
  -(t*h-b^2)*k^4 - 2*(b*d-a*h)*k^3 +
    (det6 t a b c d h - (c*h-d^2) - 2*(a*b-t*d)*N)*k^2 -
    2*(a*d-b*c)*N*k - (t*c-a^2)*N^2

theorem quartic_at_product (t a b c d h k y : ℤ) :
    quartic t a b c d h (k*y) k =
      k^2 * det6 (t-1) (a-k) (b-y) (c-k^2) (d-k*y) (h-y^2) := by
  unfold quartic det6
  ring

/-- Every genuine factor row survives, including at singular moment matrices. -/
theorem factor_quartic_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x y : ι → ℤ) {i : ι} (mem : i ∈ s) {N : ℤ} (factor : x i*y i=N) :
    0 ≤ quartic s.card (∑ j ∈ s, x j) (∑ j ∈ s, y j) (∑ j ∈ s, x j^2)
      (∑ j ∈ s, x j*y j) (∑ j ∈ s, y j^2) N (x i) := by
  have erased (f : ι → ℤ) : ∑ j ∈ s.erase i, f j = (∑ j ∈ s, f j)-f i :=
    eq_sub_of_add_eq (sum_erase_add s f mem)
  have count : ((s.erase i).card : ℤ) = s.card-1 := by
    have := card_erase_add_one mem
    omega
  have rem := gram_nonneg (s.erase i) x y
  simp only [erased, count] at rem
  rw [← factor, quartic_at_product]
  exact mul_nonneg (sq_nonneg _) rem

/-- Projecting all points onto an integer linear form uses the same six moments. -/
theorem projection_window {ι : Type*} [DecidableEq ι] (s : Finset ι) (x y : ι → ℤ)
    (u v : ℤ) {i : ι} (mem : i ∈ s) :
    let t : ℤ := s.card
    let a := ∑ j ∈ s, x j
    let b := ∑ j ∈ s, y j
    let c := ∑ j ∈ s, x j^2
    let d := ∑ j ∈ s, x j*y j
    let h := ∑ j ∈ s, y j^2
    (t*(u*x i+v*y i) - (u*a+v*b))^2 ≤
      (t-1)*(t*(u^2*c+2*u*v*d+v^2*h)-(u*a+v*b)^2) := by
  dsimp only
  have marginal := marginal_window s (fun j => u*x j + v*y j) mem
  have sums : ∑ j ∈ s, (u*x j+v*y j) =
      u*(∑ j ∈ s, x j)+v*(∑ j ∈ s, y j) := by simp [sum_add_distrib, mul_sum]
  have squares : ∑ j ∈ s, (u*x j+v*y j)*(u*x j+v*y j) =
      u^2*(∑ j ∈ s, x j^2)+2*u*v*(∑ j ∈ s, x j*y j)+v^2*(∑ j ∈ s, y j^2) := by
    simp only [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  simpa only [sums, squares] using marginal

/-- With k>0, an integer projection interval on xy=N is equivalent to an
upper closed square bound and the complement of an open square bound. -/
theorem projection_at_product {u v k y N L H : ℤ} (up : 0<u) (kp : 0<k)
    (factor : k*y=N) :
    (L ≤ u*k+v*y ∧ u*k+v*y ≤ H) ↔
      ((2*u*k-H)^2 ≤ H^2-4*u*v*N ∧ L^2-4*u*v*N ≤ (2*u*k-L)^2) := by
  have pos : 0 < 4*u*k := by positivity
  have ident (z : ℤ) :
      (2*u*k-z)^2 - (z^2-4*u*v*N) = (4*u*k)*(u*k+v*y-z) := by
    rw [← factor]
    ring
  have hi : (2*u*k-H)^2 ≤ H^2-4*u*v*N ↔ u*k+v*y ≤ H := by
    rw [← sub_nonpos, ident]
    constructor
    · intro bound
      by_contra! bad
      exact (not_lt_of_ge bound) (mul_pos pos (sub_pos.mpr bad))
    · exact fun bound => mul_nonpos_of_nonneg_of_nonpos pos.le (sub_nonpos.mpr bound)
  have lo : L^2-4*u*v*N ≤ (2*u*k-L)^2 ↔ L ≤ u*k+v*y := by
    rw [← sub_nonneg, ident, mul_nonneg_iff_of_pos_left pos, sub_nonneg]
  rw [hi, lo, and_comm]

/-- The choice (u,v)=(-B,A) cancels covariance with x. Here A=tΣx²-(Σx)²,
B=tΣxy-ΣxΣy and H=tΣy²-(Σy)² are the centered second moments. -/
theorem regression_projection (A B H : ℤ) :
    (-B)*A+A*B=0 ∧ (-B)^2*A+2*(-B)*A*B+A^2*H=A*(A*H-B^2) := by
  constructor <;> ring

end PrimeFactors.QuotientStripHyperbola
