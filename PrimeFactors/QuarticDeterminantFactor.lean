import PrimeFactors.QuarticDivisorWindow
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Int.GCD

namespace PrimeFactors.QuarticDeterminantFactor

open Matrix Finset QuarticDivisorWindow QuarticFactorLane
open scoped Matrix

abbrev Rows := Matrix (Fin 5) (Fin 5) ℤ

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

/-- Ascending coefficients of the five public jet generators. -/
def canonical (n t : ℤ) : Rows :=
  ![![n^2,0,0,0,0], ![-n*t,n,0,0,0], ![t^2,-2*t,1,0,0],
    ![0,t^2,-2*t,1,0], ![0,0,t^2,-2*t,1]]

noncomputable def evaluate (A : Rows) (x : ℤ) := A *ᵥ (fun i => x^i.val)

theorem evaluate_row (A : Rows) (x : ℤ) (i : Fin 5) :
    evaluate A x i = value (weights (A i)) 1 x := by
  simp [evaluate, Matrix.mulVec, dotProduct, Fin.sum_univ_five, weights, value]
  rfl

/-- Discard the first column and the one row not required to vanish. -/
noncomputable def minor (A : Rows) := (A.submatrix Fin.succ Fin.succ).det

theorem det_canonical (n t : ℤ) : (canonical n t).det = n^3 := by
  rw [det_of_lowerTriangular]
  · simp [Fin.prod_univ_succ, canonical]
    ring
  · intro i j h
    change i < j at h
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide +kernel)

theorem values (n t x : ℤ) :
    evaluate (canonical n t) x =
      ![n^2, n*(x-t), (x-t)^2, x*(x-t)^2, x^2*(x-t)^2] := by
  funext i
  rw [evaluate_row]
  fin_cases i <;> simp [canonical, weights, value] <;> ring

/-- The evaluation ideal has positive generator gcd(N,x−t)² (or zero for N=x−t=0). -/
theorem evaluation_image (n t x a : ℤ) :
    (∀ i, a ∣ evaluate (canonical n t) x i) ↔ a ∣ (Int.gcd n (x-t):ℤ)^2 := by
  rw [values]
  constructor
  · intro h
    obtain ⟨u,hu⟩ := h 0
    obtain ⟨v,hv⟩ := h 1
    obtain ⟨w,hw⟩ := h 2
    simp at hu hv hw
    let b := Int.gcdA n (x-t)
    let c := Int.gcdB n (x-t)
    have bez : (Int.gcd n (x-t):ℤ) = n*b+(x-t)*c := Int.gcd_eq_gcd_ab _ _
    refine ⟨u*b^2+2*v*b*c+w*c^2,?_⟩
    rw [bez]
    linear_combination b^2*hu + (2*b*c)*hv + c^2*hw
  · intro h i
    have ln : (Int.gcd n (x-t):ℤ) ∣ n := Int.gcd_dvd_left
    have lr : (Int.gcd n (x-t):ℤ) ∣ x-t := Int.gcd_dvd_right
    have m : a ∣ n*(x-t) := h.trans (by simpa [pow_two] using mul_dvd_mul ln lr)
    have s := h.trans (pow_dvd_pow_of_dvd lr 2)
    fin_cases i
    · exact h.trans (pow_dvd_pow_of_dvd ln 2)
    · exact m
    · exact s
    · exact dvd_mul_of_dvd_right s _
    · exact dvd_mul_of_dvd_right s _

private theorem linear_image {v : Fin 5 → ℤ} (K : Rows) {a : ℤ} (h : ∀ i, a ∣ v i) (j : Fin 5) :
    a ∣ (K *ᵥ v) j := by
  change a ∣ ∑ i, K j i*v i
  apply Finset.dvd_sum
  intro i _
  exact dvd_mul_of_dvd_right (h i) _

/-- Evaluation at x becomes column zero by a determinant-preserving column operation. -/
theorem eval_minor (A : Rows) (x : ℤ) (zeros : ∀ i : Fin 4, evaluate A x i.succ = 0) :
    A.det = evaluate A x 0 * minor A := by
  let B : Rows := A.updateCol 0 (evaluate A x)
  have same : B.det = A.det := by
    have column : evaluate A x = fun k => ∑ i : Fin 5, (x^i.val) • A k i := by
      funext k
      change (∑ i : Fin 5, A k i*x^i.val) = ∑ i : Fin 5, x^i.val*A k i
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    dsimp only [B]
    rw [column,Matrix.det_updateCol_sum]
    simp
  have tail : B.submatrix Fin.succ Fin.succ = A.submatrix Fin.succ Fin.succ := by
    ext i j
    simp [B,Matrix.submatrix_apply,Matrix.updateCol_ne]
  rw [← same, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [B,Matrix.updateCol_self, zeros, tail, minor]

/-- With four zero pairings, the leftover pairing generates the original image ideal.
This change-of-basis statement works for any five integer evaluation coordinates. -/
theorem one_remaining_image (B U V : Rows) (nodes : Fin 5 → ℤ) (inv : V*U=1)
    (zeros : ∀ i : Fin 4, ((U*B) *ᵥ nodes) i.succ = 0) (a : ℤ) :
    (∀ j, a ∣ (B *ᵥ nodes) j) ↔ a ∣ ((U*B) *ᵥ nodes) 0 := by
  have src := (Matrix.mulVec_mulVec nodes U B).symm
  have rev : B *ᵥ nodes = V *ᵥ ((U*B) *ᵥ nodes) := by
    rw [src,Matrix.mulVec_mulVec _ V U,inv,Matrix.one_mulVec]
  constructor
  · intro h
    rw [src]
    exact linear_image U h 0
  · intro h j
    rw [rev]
    apply linear_image V _ j
    intro i
    refine Fin.cases h (fun k => ?_) i
    rw [zeros k]
    exact dvd_zero _

/-- Four vanishing rows in an integral change of basis leave an evaluation of absolute value g². -/
theorem remaining_value (n t x : ℤ) (U V : Rows) (inv : V*U=1)
    (zeros : ∀ i : Fin 4, evaluate (U*canonical n t) x i.succ = 0) :
    (evaluate (U*canonical n t) x 0).natAbs = (Int.gcd n (x-t))^2 := by
  have test (a : ℤ) : a ∣ (Int.gcd n (x-t):ℤ)^2 ↔ a ∣ evaluate (U*canonical n t) x 0 :=
    (evaluation_image n t x a).symm.trans
      (one_remaining_image (canonical n t) U V (fun i => x^i.val) inv zeros a)
  have left := (test _).mpr (dvd_refl _)
  have right := (test _).mp (dvd_refl _)
  exact Nat.dvd_antisymm (by simpa only [Int.natAbs_pow,Int.natAbs_ofNat] using Int.natAbs_dvd_natAbs.mpr left)
    (by simpa only [Int.natAbs_pow,Int.natAbs_ofNat] using Int.natAbs_dvd_natAbs.mpr right)

theorem determinant_law (n t x : ℤ) (U V : Rows) (inv : V*U=1)
    (zeros : ∀ i : Fin 4, evaluate (U*canonical n t) x i.succ = 0) :
    (minor (U*canonical n t)).natAbs * (Int.gcd n (x-t))^2 = n.natAbs^3 := by
  have one : V.det.natAbs * U.det.natAbs = 1 := by
    simpa only [Matrix.det_mul,Matrix.det_one,Int.natAbs_mul,Int.natAbs_one] using congrArg (fun M : Rows => M.det.natAbs) inv
  have unit : U.det.natAbs = 1 := (by simpa using one : V.det.natAbs=1 ∧ U.det.natAbs=1).2
  have split := congrArg Int.natAbs (eval_minor (U*canonical n t) x zeros)
  simpa [det_mul, det_canonical, Int.natAbs_mul, Int.natAbs_pow, unit, remaining_value n t x U V inv zeros, mul_comm] using split.symm

/-- Multiplying the offset by the public unit stride identifies its gcd with the factor. -/
theorem progression_gcd (d q : ℕ) (c s t x : ℤ)
    (cop : IsCoprime ((d:ℤ)*q) s) (anchor : (d:ℤ)*q ∣ c+s*t) (point : c+s*x=d) :
    Int.gcd ((d:ℤ)*q) (x-t) = d := by
  let g := Int.gcd ((d:ℤ)*q) (x-t)
  have dn : (d:ℤ) ∣ (d:ℤ)*q := dvd_mul_right _ _
  have ds : (d:ℤ) ∣ s*(x-t) := by
    rw [show s*(x-t)=(c+s*x)-(c+s*t) by ring,point]
    exact dvd_sub (dvd_refl _) (dn.trans anchor)
  have dg := Int.dvd_coe_gcd dn (cop.of_mul_left_left.dvd_of_dvd_mul_left ds)
  have gn : (g:ℤ) ∣ (d:ℤ)*q := Int.gcd_dvd_left
  have goff : (g:ℤ) ∣ x-t := Int.gcd_dvd_right
  have gd : (g:ℤ) ∣ d := by
    rw [← point, show c+s*x=(c+s*t)+s*(x-t) by ring]
    exact dvd_add (gn.trans anchor) (dvd_mul_of_dvd_right goff s)
  exact Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp gd) (Int.natCast_dvd_natCast.mp dg)

/-- With N=dq and d=c+sx, the public four-row minor identifies the cofactor square. -/
theorem factor_minor (d q : ℕ) (positive : 0<d) (c s t x : ℤ) (U V : Rows)
    (inv : V*U=1) (cop : IsCoprime ((d:ℤ)*q) s)
    (anchor : (d:ℤ)*q ∣ c+s*t) (point : c+s*x=d)
    (zeros : ∀ i : Fin 4, evaluate (U*canonical ((d:ℤ)*q) t) x i.succ = 0) :
    (minor (U*canonical ((d:ℤ)*q) t)).natAbs = (d*q)*q^2 := by
  have ident := determinant_law ((d:ℤ)*q) t x U V inv zeros
  rw [progression_gcd d q c s t x cop anchor point,Int.natAbs_mul,Int.natAbs_ofNat,
    Int.natAbs_ofNat] at ident
  apply Nat.eq_of_mul_eq_mul_right (pow_pos positive 2)
  calc
    _ = (d*q)^3 := ident
    _ = _ := by ring

end PrimeFactors.QuarticDeterminantFactor
