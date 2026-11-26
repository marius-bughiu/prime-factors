import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Polynomial.Reverse
import PrimeFactors.TranslatedHasse
import Mathlib.Tactic

/-! Moments on the diagonal of powers of a cubic and binomial translation of a Hankel matrix. -/
namespace PrimeFactors.HankelTranslation

open Finset Polynomial Matrix
variable {R : Type*} [CommRing R]

noncomputable def moment (B Cc : R) (n : ℕ) : R :=
  (((1 + C B * X^2 + C Cc * X^3 : R[X])^n).coeff n)

noncomputable def hankel (s : ℕ→R) (n : ℕ) : R :=
  (Matrix.of (fun i j : Fin n => s (i.val+j.val))).det

private noncomputable def functional (s : ℕ → R) : R[X] →ₗ[R] R :=
  Polynomial.lsum fun j => (LinearMap.id : R →ₗ[R] R).smulRight (s j)

private theorem value_monomial (s : ℕ → R) (j : ℕ) (v : R) :
    functional s (monomial j v) = v*s j := by
  simp [functional, Polynomial.lsum_apply, LinearMap.smulRight_apply]

noncomputable def translate (a : R) (s : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ range (n+1), (a^(n-k)*(n.choose k:R))*s k

private theorem value_shift (a : R) (s : ℕ→R) (n : ℕ) :
    functional s ((X+C a)^n) = translate a s n := by
  nontriviality R
  have h := (((X+C a : R[X])^n).as_sum_range' (n+1) (by simp))
  calc
    _ = _ := congrArg (functional s) h
    _ = _ := by simp only [map_sum,value_monomial,coeff_X_add_C_pow,translate]

/-- Changing every moment by its binomial translation preserves each Hankel determinant. -/
theorem invariant (s : ℕ→R) (a : R) (n : ℕ) :
    hankel (translate a s) n = hankel s n := by
  classical
  nontriviality R
  let P (i : Fin n) := (X+C a)^i.val
  let M : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => (P j).coeff i
  let H : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => s (i.val+j.val)
  have detM : M.det=1 := Matrix.det_matrixOfPolynomials P
    (fun i => natDegree_pow_X_add_C i.val a) (fun i => (monic_X_add_C a).pow i.val)
  have expand (i : Fin n) : P i=∑ j : Fin n, monomial j.val (M j i) := by
    change P i = ∑ j : Fin n, monomial j.val ((P i).coeff j.val)
    exact ((P i).as_sum_range' n (by simp [P])).trans
      (Fin.sum_univ_eq_sum_range (fun j => monomial j ((P i).coeff j)) n).symm
  have eq : Matrix.of (fun i j : Fin n => translate a s (i.val+j.val)) = M.transpose*H*M := by
    ext i j
    change translate a s (i.val+j.val) = _
    rw [←value_shift,pow_add]
    change functional s (P i * P j) = _
    rw [expand i,expand j]
    simp only [Finset.sum_mul,Finset.mul_sum,map_sum,monomial_mul_monomial,value_monomial,
      Matrix.mul_apply,Matrix.transpose_apply,H,Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  change (Matrix.of _).det=H.det
  rw [eq,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,detM,one_mul,mul_one]

/-- Reading degree n in the nth power converts adding a linear term into binomial translation. -/
theorem diagonal_shift (P : R[X]) (a : R) (n : ℕ) :
    ((P+C a*X)^n).coeff n = translate a (fun k => (P^k).coeff k) n := by
  classical
  rw [add_pow,finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro k hk
  have le := Nat.le_of_lt_succ (mem_range.mp hk)
  rw [mul_pow,←C_pow]
  have eq : P^k*(C (a^(n-k))*X^(n-k))*(n.choose k:R[X]) =
      (C (a^(n-k)*(n.choose k:R))*P^k)*X^(n-k) := by rw [map_mul, map_natCast]; ring
  rw [eq,coeff_mul_X_pow',if_pos (Nat.sub_le n k),coeff_C_mul]
  rw [Nat.sub_sub_self le]

theorem cubic_hankel (a B Cc : R) (n : ℕ) :
    hankel (fun k => (((1+C B*X^2+C Cc*X^3+C a*X : R[X])^k).coeff k)) n =
      hankel (moment B Cc) n := by
  simp_rw [diagonal_shift]
  exact invariant (moment B Cc) a n

private theorem reflected_power (P : R[X]) (degree : P.natDegree≤3) (m : ℕ) :
    reflect (3*m) (P^m) = (reflect 3 P)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ,pow_succ,pow_succ,reflect_mul (P^m) P _ degree,ih]
    exact natDegree_pow_le.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left m degree)

private theorem reflected_cubic (c : R) :
    reflect 3 ((X+C c)^3-(X+C c)) =
      (1+C (3*c^2-1)*X^2+C (c^3-c)*X^3+C (3*c)*X : R[X]) := by
  have split : ((X+C c)^3-(X+C c) : R[X]) =
      X^3+C (3*c)*X^2+C (3*c^2-1)*X^1+C (c^3-c) := by
    simp only [map_sub,map_mul,map_pow,map_ofNat,map_one]
    ring
  rw [split]
  simp only [reflect_add,reflect_monomial,reflect_C_mul_X_pow,reflect_C]
  norm_num [revAt]
  ring

/-- The actual translated Hasse readings have the same Hankel determinants as
the centered cubic with coefficients 3c²−1 and c³−c. -/
theorem hasse_hankel (c : R) (n : ℕ) :
    hankel (fun m => TranslatedHasse.value m c) n =
      hankel (moment (3*c^2-1) (c^3-c)) n := by
  have eq (m : ℕ) : TranslatedHasse.value m c =
      (((1+C (3*c^2-1)*X^2+C (c^3-c)*X^3+C (3*c)*X : R[X])^m).coeff m) := by
    rw [←reflected_cubic,←reflected_power _ (by compute_degree),coeff_reflect,
      revAt_le (show m≤3*m by omega),show 3*m-m=2*m by omega]
    rfl
  simp_rw [eq]
  exact cubic_hankel _ _ _ _

end PrimeFactors.HankelTranslation
