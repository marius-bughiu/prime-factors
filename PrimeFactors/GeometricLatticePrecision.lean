import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-! Exact sufficient precision for one lattice with rows `M X^i` (i<r)
and a monic polynomial of degree r, centered before scaling the columns.
The length guarantee is conditional on the usual first-vector estimate for
LLL with delta 3/4 (Lenstra, Lenstra and Lovász, 1982, Proposition 1.6, (1.9),
<https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1982f/art.pdf>).
The strict public test involves integers only. -/
namespace PrimeFactors.GeometricLatticePrecision

open Finset

/-- The last row contains the shifted monic polynomial. -/
noncomputable def basis (r : ℕ) (M B : ℤ) (f : Fin (r+1) → ℤ) : Matrix (Fin (r+1)) (Fin (r+1)) ℤ :=
  fun i j => (if i=Fin.last r then f j else if i=j then M else 0)*B^j.val

theorem determinant (r : ℕ) (M B : ℤ) (f : Fin (r+1) → ℤ) (monic : f (Fin.last r)=1) :
    (basis r M B f).det = M^r * B^((r+1).choose 2) := by
  rw [Matrix.det_of_lowerTriangular]
  · simp only [basis,ite_true,prod_mul_distrib,prod_pow_eq_pow_sum]
    have diag : (∏ i : Fin (r+1), if i=Fin.last r then f i else M) = M^r := by
      rw [Fin.prod_univ_castSucc]
      simp [Fin.castSucc_ne_last,monic]
    have ex : (∑ i : Fin (r+1), i.val) = (r+1).choose 2 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => i),sum_range_id,Nat.choose_two_right]
    rw [diag,ex]
  · intro i j h
    change i<j at h
    have ne : i≠Fin.last r := fun eq => (not_lt_of_ge (Fin.le_last j)) (eq ▸ h)
    simp [basis,ne,ne_of_lt h]

/-- Fourth-power inequality after cancelling the common factor M^(4r). -/
def cost (r B : ℕ) : ℕ :=
  (r+1)^(2*(r+1)) * 2^(r*(r+1)) * B^(2*r*(r+1))

/-- The smallest precision passing the strict sufficient bound. -/
def precision (n r B : ℕ) : ℕ := Nat.log (n^4) (cost r B) + 1

theorem precision_iff {n B : ℕ} (hn : 1<n) (hb : 0<B) (r k : ℕ) :
    cost r B < (n^k)^4 ↔ precision n r B ≤ k := by
  have hn4 : 1<n^4 := one_lt_pow₀ hn (by decide)
  have cp : 0<cost r B := by unfold cost; positivity
  have changePower : (n^k)^4=(n^4)^k := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
  rw [changePower]
  unfold precision
  constructor
  · intro h
    by_contra! e
    have bound := Nat.pow_le_pow_right (by omega : 0<n^4)
      (show k≤Nat.log (n^4) (cost r B) by omega)
    exact (not_lt_of_ge (bound.trans (Nat.pow_log_le_self _ cp.ne'))) h
  · intro h
    exact (Nat.lt_pow_succ_log_self hn4 _).trans_le (Nat.pow_le_pow_right (by omega) h)

private theorem exponents (r : ℕ) : ((r+1).choose 2)*4=2*r*(r+1) := by
  have two : 2*((r+1).choose 2)=(r+1)*r := by
    simpa [Nat.mul_comm] using (Nat.succ_mul_choose_eq r 1).symm
  nlinarith only [two]

/-- If the integer squared norm obeys the classical LLL first-vector bound,
the public precision test forces the scaled row's absolute column sum below M.
Its lattice membership and nonzero status are supplied by the reduction. -/
theorem short {r B M : ℕ} (pos : 0<M) (v : Fin (r+1) → ℕ)
    (lll : (∑ i, v i^2)^(2*(r+1)) ≤ 2^(r*(r+1))*(M^r * B^((r+1).choose 2))^4)
    (room : cost r B < M^4) : (∑ i, v i)<M := by
  have cs : (∑ i, v i)^2 ≤ (r+1)*(∑ i, v i^2) := by
    simpa using (sum_mul_sq_le_sq_mul_sq (R:=ℕ) univ (fun _ : Fin (r+1) => 1) v)
  have nn := Nat.pow_le_pow_left cs (2*(r+1))
  rw [mul_pow] at nn
  have row := nn.trans (Nat.mul_le_mul_left ((r+1)^(2*(r+1))) lll)
  have det4 : (M^r * B^((r+1).choose 2))^4=M^(r*4)*B^(2*r*(r+1)) := by
    rw [mul_pow,←pow_mul,←pow_mul,exponents]
  rw [det4] at row
  have raised : (∑ i, v i)^(4*(r+1)) ≤ cost r B*M^(r*4) := by
    calc
      _ = ((∑ i, v i)^2)^(2*(r+1)) := by rw [←pow_mul]; congr 1; ring
      _ ≤ _ := row
      _ = _ := by unfold cost; ring
  have rhs : M^4*M^(r*4)=M^(4*(r+1)) := by rw [←pow_add]; congr 1; ring
  have lt := raised.trans_lt (Nat.mul_lt_mul_of_pos_right room (pow_pos pos _))
  rw [rhs] at lt
  exact lt_of_not_ge (fun h => (not_le_of_gt lt) (Nat.pow_le_pow_left h _))

/-- A row satisfying the LLL estimate at or above the computed precision. -/
theorem short_at_precision {n r B k : ℕ} (hn : 1<n) (hb : 0<B)
    (enough : precision n r B ≤ k) (row : Fin (r+1) → ℤ)
    (lll : (∑ i, (row i).natAbs^2)^(2*(r+1)) ≤
      2^(r*(r+1))*((n^k)^r * B^((r+1).choose 2))^4) :
    (∑ i, (row i).natAbs)<n^k :=
  short (pow_pos (by omega) _) _ lll ((precision_iff hn hb r k).mpr enough)

/-- The width-21 example has centered radius 11 and trial degree 3. -/
theorem example_precision : precision 30607 3 11 = 2 := by
  have iff := precision_iff (by decide : 1<30607) (by decide : 0<11) 3
  have low := (iff 1).mpr.mt (by decide +kernel)
  have high := (iff 2).mp (by decide +kernel)
  omega

end PrimeFactors.GeometricLatticePrecision
