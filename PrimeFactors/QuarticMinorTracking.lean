import PrimeFactors.QuarticDeterminantFactor

namespace PrimeFactors.QuarticMinorTracking

open Finset Matrix QuarticDeterminantFactor

set_option maxRecDepth 8192 in
/-- The coefficient of the omitted row when expanding the constant polynomial n²
is the corresponding normalized minor up to sign. No common root is required. -/
theorem coefficient_is_minor (n t : ℤ) (hn : n≠0) (U V : Rows) (inverse : V*U=1) :
    (minor (U*canonical n t)).natAbs = n.natAbs*(V 0 0).natAbs := by
  let A := U*canonical n t
  have id : V*A=canonical n t := by dsimp [A]; rw [←Matrix.mul_assoc,inverse,Matrix.one_mul]
  have lin : (∑ i : Fin 5, V 0 i • A i) = (canonical n t) 0 := by
    funext j
    have h := congrArg (fun M : Rows => M 0 j) id
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.mul_apply] using h
  let B := A.updateRow 0 ((canonical n t) 0)
  have changed : B.det=V 0 0*A.det := by
    dsimp only [B]
    rw [←lin,Matrix.det_updateRow_sum]
    exact smul_eq_mul ..
  have tail : B.submatrix Fin.succ Fin.succ=A.submatrix Fin.succ Fin.succ := by
    ext i j
    simp [B,Matrix.submatrix_apply,Matrix.updateRow_ne]
  have expand : B.det=n^2*minor A := by
    rw [Matrix.det_succ_row_zero,Fin.sum_univ_succ]
    have off (j : Fin 4) : B 0 j.succ=0 := by fin_cases j <;> rfl
    have top : B 0 0=n^2 := rfl
    simp [top,off,minor,tail]
  have unit : U.det.natAbs=1 := by
    have h : V.det.natAbs * U.det.natAbs = 1 := by
      simpa only [Matrix.det_mul,Matrix.det_one,Int.natAbs_mul,Int.natAbs_one] using
        congrArg (fun M : Rows => M.det.natAbs) inverse
    exact (by simpa using h : V.det.natAbs=1 ∧ U.det.natAbs=1).2
  have raw := congrArg Int.natAbs (expand.symm.trans changed)
  have scaled : n.natAbs^2*(minor A).natAbs = n.natAbs^2*(n.natAbs*(V 0 0).natAbs) := by
    simpa only [A,Matrix.det_mul,det_canonical,Int.natAbs_mul,Int.natAbs_pow,unit,one_mul,
      pow_succ,mul_one,mul_assoc,mul_left_comm,mul_comm] using raw
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Int.natAbs_pos.mpr hn) 2) scaled

end PrimeFactors.QuarticMinorTracking
