import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

namespace PrimeFactors.NormAuxiliary

open Polynomial
open scoped BigOperators

/-- The determinant multiplier for the two forms 1-z and 1+z. Each pair
of evaluation sites contributes -2 times its ordinary difference. -/
theorem basis_eval_det {n : ℕ} (z : Fin n → ℚ) :
    (Matrix.projVandermonde (fun i => 1-z i) (fun i => 1+z i)).det =
    (∏ i : Fin n, (-2 : ℚ)^(Finset.Ioi i).card) * (Matrix.vandermonde z).det := by
  rw [Matrix.det_projVandermonde, Matrix.det_vandermonde]
  have diff (i j : Fin n) :
      (1-z j)*(1+z i)-(1-z i)*(1+z j)=(-2)*(z j-z i) := by ring
  simp_rw [diff, Finset.prod_mul_distrib, Finset.prod_const]

/-- One parity block of the coefficient basis. -/
noncomputable def basisPoly {n : ℕ} (i : Fin n) : ℚ[X] :=
  (1-X)^(i:ℕ)*(1+X)^(i.rev:ℕ)

/-- Exact determinant of the coefficient basis, with one factor -2 for
each unordered pair of columns. The two parity blocks are used separately. -/
theorem basis_det (n : ℕ) :
    (Matrix.of fun (i j : Fin n) => (basisPoly j).coeff i).det =
      ∏ i : Fin n, (-2 : ℚ)^(Finset.Ioi i).card := by
  let v (i : Fin n) : ℚ := (i:ℕ)
  have vinj : Function.Injective v := by
    intro i j h
    apply Fin.ext
    change ((i:ℕ):ℚ)=((j:ℕ):ℚ) at h
    exact_mod_cast h
  have bound (i : Fin n) : (basisPoly i).natDegree < n := by
    have a : (1-X : ℚ[X]).natDegree ≤ 1 := by compute_degree
    have b : (1+X : ℚ[X]).natDegree ≤ 1 := by compute_degree
    have aa := natDegree_pow_le (p := (1-X : ℚ[X])) (n := (i:ℕ))
    have bb := natDegree_pow_le (p := (1+X : ℚ[X])) (n := (i.rev:ℕ))
    have top := (natDegree_mul_le (p := (1-X : ℚ[X])^(i:ℕ))
      (q := (1+X : ℚ[X])^(i.rev:ℕ))).trans (add_le_add
        (aa.trans (Nat.mul_le_mul_left _ a)) (bb.trans (Nat.mul_le_mul_left _ b)))
    simp only [Nat.mul_one, Fin.val_rev] at top
    dsimp [basisPoly]
    omega
  have matrices : Matrix.projVandermonde (fun i => 1-v i) (fun i => 1+v i) =
      Matrix.vandermonde v * (Matrix.of fun (i j : Fin n) => (basisPoly j).coeff i) := by
    ext i j
    have ev : (basisPoly j).eval (v i) =
        ∑ k ∈ Finset.range n, (basisPoly j).coeff k*(v i)^k := by
      exact Polynomial.eval₂_eq_sum_range' (RingHom.id ℚ) (bound j) (v i)
    rw [← Fin.sum_univ_eq_sum_range] at ev
    simpa [Matrix.projVandermonde_apply, Matrix.mul_apply, Matrix.vandermonde_apply,
      basisPoly, mul_comm] using ev
  have eq := basis_eval_det v
  rw [matrices, Matrix.det_mul, mul_comm (∏ i : Fin n, _)] at eq
  exact mul_left_cancel₀ (Matrix.det_vandermonde_ne_zero_iff.mpr vinj) eq

/-- All nonnegative points of the unit quarter-circle have a parameter from
zero through one. The parametrization uses no trigonometric evaluation. -/
theorem parameter_exists {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (circle : a^2+b^2=1) :
    ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 ∧ a*(1+z^2)=1-z^2 ∧ b*(1+z^2)=2*z := by
  have pos : 0 < 1+a := by linarith
  refine ⟨b/(1+a), div_nonneg hb pos.le, ?_, ?_, ?_⟩
  · rw [div_le_one pos]
    nlinarith [sq_nonneg a]
  · field_simp
    linear_combination (a+1)*circle
  · field_simp
    linear_combination b*(1+a)*circle

/-- Substituting z=base+step*u in a monomial gives a lower triangular
coefficient matrix. Its determinant depends only on the cell width. -/
theorem affine_det (n : ℕ) (base step : ℚ) :
    (Matrix.of (fun (i j : Fin n) => ((i:ℕ).choose j : ℚ)*base^((i:ℕ)-j)*step^(j:ℕ))).det =
      step^(∑ i : Fin n, (i:ℕ)) := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [← Finset.prod_pow_eq_pow_sum]
  · intro i j h
    have hij : (i:ℕ) < (j:ℕ) := h
    simp [Nat.choose_eq_zero_of_lt hij]

/-- Clearing the positive denominator gives an exact degree-four
polynomial for the five quadratic monomials. -/
theorem quadratic_pullback (z U V x y a b c e f : ℝ)
    (hx : x*(1+z^2)=U*(1-z^2)) (hy : y*(1+z^2)=V*(2*z)) :
    (a+b*x+c*x^2+e*y+f*x*y)*(1+z^2)^2 =
    a*(1+z^2)^2+b*U*(1-z^2)*(1+z^2)+c*U^2*(1-z^2)^2+
      e*V*(2*z)*(1+z^2)+f*U*V*(2*z)*(1-z^2) := by
  calc
    _ = a*(1+z^2)^2+b*(x*(1+z^2))*(1+z^2)+c*(x*(1+z^2))^2+
      e*(y*(1+z^2))*(1+z^2)+f*(x*(1+z^2))*(y*(1+z^2)) := by ring
    _ = _ := by rw [hx,hy]; ring

/-- A coefficient vector with small absolute sum bounds the real polynomial
on the whole closed unit interval (and its reflection). -/
theorem local_value_bound {n : ℕ} (v : Fin n → ℝ) {u : ℝ} (unit : |u| ≤ 1) :
    |∑ j, v j*u^(j:ℕ)| ≤ ∑ j, |v j| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul, abs_pow]
  simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ (n := (j:ℕ)) (abs_nonneg u) unit)
    (abs_nonneg (v j))

/-- The cost of restoring the exact row amplitudes is controlled by the
error of each amplitude and the integer combination that LLL returned. -/
theorem rounding_error {ι : Type*} [Fintype ι] (c a rounded values : ι → ℝ)
    {eps K : ℝ} (close : ∀ i, |a i-rounded i| ≤ eps)
    (bounded : ∀ i, |values i| ≤ K) :
    |(∑ i, c i*a i*values i)-(∑ i, c i*rounded i*values i)| ≤
      (∑ i, |c i|)*eps*K := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [show c i*a i*values i-c i*rounded i*values i=c i*((a i-rounded i)*values i) by ring,
    abs_mul,abs_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (close i) (bounded i) (abs_nonneg _) ((abs_nonneg _).trans (close i)))
    (abs_nonneg _)

/-- An integer evaluation whose scaled approximation and error have total
magnitude less than one must vanish. -/
theorem small_integer_zero {v : ℤ} {scale approx e : ℝ} (s : 1 ≤ scale)
    (error : |(v:ℝ)*scale-approx| ≤ e) (budget : |approx|+e < 1) : v=0 := by
  have triangle := abs_add_le ((v:ℝ)*scale-approx) approx
  rw [sub_add_cancel] at triangle
  have size : |(v:ℝ)| *scale < 1 := by
    rw [← abs_of_nonneg (le_trans zero_le_one s), ← abs_mul]
    linarith
  have small : |(v:ℝ)| < 1 :=
    lt_of_le_of_lt (by simpa using (mul_le_mul_of_nonneg_left s (abs_nonneg (v:ℝ)))) size
  have bounds := abs_lt.mp small
  obtain ⟨lo,hi⟩ := bounds
  have lower : (-1:ℤ) < v := by exact_mod_cast lo
  have upper : v < (1:ℤ) := by exact_mod_cast hi
  omega

/-- Eliminating the second coordinate leaves a univariate polynomial. -/
noncomputable def eliminant (d T : ℤ) (P Q : ℤ[X]) : ℤ[X] :=
  C d*P^2+(X^2-C T)*Q^2

theorem point_is_root {d T x y : ℤ} {P Q : ℤ[X]} (norm : x^2+d*y^2=T)
    (curve : P.eval x+y*Q.eval x=0) : (eliminant d T P Q).IsRoot x := by
  rw [IsRoot, eliminant]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  have hp : P.eval x= -(y*Q.eval x) := by linarith
  rw [hp, ← norm]
  ring

/-- At auxiliary degree D the eliminant has at most degree 2D. -/
theorem eliminant_degree {d T : ℤ} {P Q : ℤ[X]} {D : ℕ} (p : P.natDegree ≤ D)
    (q : Q.natDegree+1 ≤ D) : (eliminant d T P Q).natDegree ≤ 2*D := by
  have x2 : (X^2-C T : ℤ[X]).natDegree ≤ 2 := by compute_degree
  have p2 := (natDegree_pow_le (p := P) (n := 2)).trans (Nat.mul_le_mul_left 2 p)
  have q2 := natDegree_pow_le (p := Q) (n := 2)
  have left := (natDegree_mul_le (p := C d) (q := P^2)).trans
    (Nat.add_le_add_left p2 _)
  simp only [natDegree_C, Nat.zero_add] at left
  have right := (natDegree_mul_le (p := X^2-C T) (q := Q^2)).trans (Nat.add_le_add x2 q2)
  exact natDegree_add_le_of_degree_le left (by omega)

/-- The elimination polynomial can vanish identically only for the zero
auxiliary curve. Outside the ellipse its evaluation is a sum of squares
with positive coefficients. -/
theorem eliminant_ne_zero {d T : ℤ} (hd : 0 < d) {P Q : ℤ[X]}
    (nz : P ≠ 0 ∨ Q ≠ 0) : eliminant d T P Q ≠ 0 := by
  intro e
  have vanishes (x : ℤ) (hx : T < x^2) : P.IsRoot x ∧ Q.IsRoot x := by
    have val := congrArg (Polynomial.eval x) e
    simp [eliminant] at val
    have zp := mul_nonneg hd.le (sq_nonneg (P.eval x))
    have zq := mul_nonneg (sub_nonneg.mpr hx.le) (sq_nonneg (Q.eval x))
    have hp : d*(P.eval x)^2=0 := by linarith
    have hq : (x^2-T)*(Q.eval x)^2=0 := by linarith
    exact ⟨sq_eq_zero_iff.mp ((mul_eq_zero.mp hp).resolve_left hd.ne'),
      sq_eq_zero_iff.mp ((mul_eq_zero.mp hq).resolve_left (sub_pos.mpr hx).ne')⟩
  have huge (a : ℤ) : ∃ x, a < x ∧ T < x^2 := by
    let x := max (max a T) 1 + 1
    have ha : a < x := by dsimp [x]; omega
    have ht : T < x := by dsimp [x]; omega
    have h1 : 1 ≤ x := by dsimp [x]; omega
    exact ⟨x, ha, ht.trans_le (by nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ x by omega)])⟩
  rcases nz with hp | hq
  · obtain ⟨a, maximal⟩ := P.exists_max_root hp
    obtain ⟨x, ax, xt⟩ := huge a
    exact (not_le_of_gt ax) (maximal x (vanishes x xt).1)
  · obtain ⟨a, maximal⟩ := Q.exists_max_root hq
    obtain ⟨x, ax, xt⟩ := huge a
    exact (not_le_of_gt ax) (maximal x (vanishes x xt).2)

end PrimeFactors.NormAuxiliary
