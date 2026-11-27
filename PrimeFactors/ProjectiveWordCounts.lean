import PrimeFactors.ProjectiveFixedLines
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Fixed lines under powers of one matrix

In dimension two a power is of the form uA + vI. At any field component it
therefore preserves the original fixed lines unless it is scalar, in which
case every line is fixed. The statement concerns a single generator.
-/

namespace PrimeFactors.ProjectiveWordCounts

open ProjectiveFixedLines

variable {R : Type*} [CommRing R]

/-- Read the entries of an ordinary two-by-two matrix in the affine chart convention. -/
noncomputable def entries (A : Matrix (Fin 2) (Fin 2) R) : Coeff R := ⟨A 0 0, A 0 1, A 1 0, A 1 1⟩

theorem entries_det (A : Matrix (Fin 2) (Fin 2) R) : det (entries A) = A.det :=
  (Matrix.det_fin_two A).symm

/-- Cayley–Hamilton in dimension two, including the zeroth power. -/
theorem power_linear (A : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    ∃ u v : R, A^n = u • A + v • (1 : Matrix (Fin 2) (Fin 2) R) := by
  induction n with
  | zero => exact ⟨0, 1, by simp⟩
  | succ n ih =>
    obtain ⟨u, v, eq⟩ := ih
    refine ⟨u*(A 0 0 + A 1 1) + v, -u*A.det, ?_⟩
    rw [pow_succ, eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.det_fin_two] <;> ring

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- A nonscalar power has the same individual fixed lines. This holds also in
characteristic two, where a discriminant test alone would be insufficient. -/
theorem fixed_power {A : Matrix (Fin 2) (Fin 2) F} (unit : A.det ≠ 0)
    (n : ℕ) (non : ¬scalar (entries (A^n))) : fixed (entries (A^n)) = fixed (entries A) := by
  obtain ⟨u, v, h⟩ := power_linear A n
  have un : u ≠ 0 := by
    rintro rfl
    apply non
    simp [h, scalar, entries, Matrix.one_apply]
  have unitA : det (entries A) ≠ 0 := by simpa [entries_det] using unit
  have unitPower : det (entries (A^n)) ≠ 0 := by
    rw [entries_det, Matrix.det_pow]
    exact pow_ne_zero n unit
  ext line
  cases line with
  | none => simp [infinity_mem, h, entries, Matrix.one_apply, un]
  | some z =>
    rw [finite_mem _ unitPower, finite_mem _ unitA, h]
    simp only [entries, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Fin.isValue, ne_eq, Fin.zero_ne_one, not_false_eq_true, if_false, if_true,
      (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, mul_zero, add_zero, mul_one]
    constructor
    · intro zero
      apply (mul_eq_zero.mp (show u*(A 1 0*(z*z)+(A 1 1-A 0 0)*z+-A 0 1) = 0 by
        linear_combination zero)).resolve_left un
    · intro zero
      linear_combination u*zero

/-- A scalar power fixes the entire local projective line, even when the
original matrix had no fixed lines. -/
theorem scalar_power {A : Matrix (Fin 2) (Fin 2) F} (unit : A.det ≠ 0)
    (n : ℕ) (s : scalar (entries (A^n))) :
    (fixed (entries (A^n))).card = Fintype.card F + 1 := by
  apply scalar_count _ _ s
  rw [entries_det, Matrix.det_pow]
  exact pow_ne_zero n unit

/-- If both component powers remain nonscalar, the CRT count is unchanged. -/
theorem two_nonscalar_powers {E : Type*} [Field E] [DecidableEq E] [Fintype E]
    {A : Matrix (Fin 2) (Fin 2) F} {B : Matrix (Fin 2) (Fin 2) E}
    (ua : A.det ≠ 0) (ub : B.det ≠ 0) (n m : ℕ)
    (sa : ¬scalar (entries (A^n))) (sb : ¬scalar (entries (B^m))) :
    (both (entries (A^n)) (entries (B^m))).card = (both (entries A) (entries B)).card := by
  rw [both_count, both_count, fixed_power ua n sa, fixed_power ub m sb]

end PrimeFactors.ProjectiveWordCounts
