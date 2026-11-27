import Mathlib.Algebra.BigOperators.Intervals
import PrimeFactors.PrimitiveIntervalMoment

/-! Four boundary entries determine the second difference of the public
triangular gcd sum at any cutoff, including the empty initial box. -/
namespace PrimeFactors.TriangularGcdCurvature

open Finset PrimitiveIntervalMoment

def entry (n t : ℕ) : ℤ := 2 - (n.gcd t : ℤ)

noncomputable def total (n b : ℕ) : ℤ := ∑ w ∈ box b, entry n (w.1 + w.2)

/-- Below the smaller prime the integer sum represents the character aggregate. -/
theorem aggregate_eq_total {p q b : ℕ} [Fact p.Prime] [Fact q.Prime]
    (ord : p < q) (below : b < p) : aggregate p q b = (total (p*q) b : ℂ) := by
  rw [aggregate, total, Int.cast_sum]
  apply sum_congr rfl
  intro w hw
  rw [kernel_gcd ord below w hw]
  simp [entry]

private noncomputable def row (f : ℕ → ℤ) (a b : ℕ) : ℤ := ∑ j ∈ Icc 1 b, f (a+j)

private noncomputable def squareSum (f : ℕ → ℤ) (b : ℕ) : ℤ := ∑ i ∈ Icc 1 b, row f i b

private theorem total_eq_square (n b : ℕ) : total n b = squareSum (entry n) b := by
  simp [total, box, squareSum, row, sum_product]

private theorem row_top (f : ℕ → ℤ) (a b : ℕ) :
    row f a (b+1) = row f a b + f (a+(b+1)) :=
  sum_Icc_succ_top (by omega : 1 ≤ b+1) _

private theorem row_shift (f : ℕ → ℤ) (a b : ℕ) :
    row f (a+1) b - row f a b = f (a+b+1) - f (a+1) := by
  induction b with
  | zero => simp [row]
  | succ b ih =>
    rw [row_top, row_top]
    rw [show a+1+(b+1) = a+(b+1)+1 by omega, show a+(b+1) = a+b+1 by omega]
    omega

private theorem square_step (f : ℕ → ℤ) (b : ℕ) :
    squareSum f (b+1) = squareSum f b + 2*row f (b+1) b + f (2*b+2) := by
  unfold squareSum
  rw [sum_Icc_succ_top (by omega : 1 ≤ b+1)]
  simp_rw [row_top]
  rw [sum_add_distrib]
  have eq : (∑ i ∈ Icc 1 b, f (i+(b+1))) = row f (b+1) b := by
    apply sum_congr rfl
    intro i _
    rw [Nat.add_comm i]
  rw [eq, show (b+1)+(b+1) = 2*b+2 by omega]
  ring

private theorem next_row (f : ℕ → ℤ) (b : ℕ) :
    row f (b+2) (b+1) - row f (b+1) b = f (2*b+3) + f (2*b+2) - f (b+2) := by
  have h := row_shift f (b+1) b
  rw [show b+1+b+1 = 2*b+2 by omega, show b+1+1 = b+2 by omega] at h
  rw [row_top, show b+2+(b+1) = 2*b+3 by omega]
  omega

/-- The full second difference uses only the four indicated gcds. -/
theorem curvature (n b : ℕ) :
    total n (b+2) - 2*total n (b+1) + total n b =
      entry n (2*b+4) + 2*entry n (2*b+3) + entry n (2*b+2) - 2*entry n (b+2) := by
  simp only [total_eq_square]
  have first := square_step (entry n) b
  have second := square_step (entry n) (b+1)
  rw [show 2*(b+1)+2 = 2*b+4 by omega, show b+1+1 = b+2 by omega] at second
  have changeRow := next_row (entry n) b
  omega

theorem baseline {n b : ℕ} (d4 : n.gcd (2*b+4) = 1) (d3 : n.gcd (2*b+3) = 1)
    (d2 : n.gcd (2*b+2) = 1) (db : n.gcd (b+2) = 1) :
    total n (b+2) - 2*total n (b+1) + total n b = 2 := by
  rw [curvature]
  norm_num [entry, d4, d3, d2, db]

/-- When all three cutoffs are admissible, none of the boundary entries meet
either prime. -/
theorem interior {p q b : ℕ} [Fact p.Prime] [Fact q.Prime]
    (ord : p < q) (below : b+2 < p) (both : q ≤ 2*b+1) :
    total (p*q) (b+2) - 2*total (p*q) (b+1) + total (p*q) b = 2 := by
  have coprime {t : ℕ} (pos : 0 < t) (hi : t < 2*p) (np : t ≠ p) (nq : t ≠ q) :
      (p*q).gcd t = 1 := by rw [gcd_diagonal ord pos hi, if_neg np, if_neg nq]
  apply baseline <;> apply coprime <;> omega

/-- This is also the second difference predicted by the quadratic reading. -/
theorem value_curvature (n b s : ℤ) : value n (b+2) s - 2*value n (b+1) s + value n b s = 2 := by
  unfold value
  ring

/-- At the first two cutoffs the middle boundary entry meets 11 and then 13.
At the third cutoff the boundary has passed both prime diagonals. -/
theorem control_143 :
    total 143 6 - 2*total 143 5 + total 143 4 = -18 ∧
    total 143 7 - 2*total 143 6 + total 143 5 = -22 ∧
    total 143 8 - 2*total 143 7 + total 143 6 = 2 ∧
    Nat.gcd 143 11 = 11 ∧ Nat.gcd 143 13 = 13 := by
  rw [curvature 143 4, curvature 143 5, curvature 143 6]
  decide +kernel

end PrimeFactors.TriangularGcdCurvature
