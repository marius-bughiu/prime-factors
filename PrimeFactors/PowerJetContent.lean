import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Ring

namespace PrimeFactors.PowerJetContent

open Finset Matrix
open scoped Matrix

/-- A positive jet depth gives gcd(N,z)^m as evaluation content, and at depth zero
the constant generator 1 gives the same formula. Extra powers up to k do not change it. -/
theorem power_content (n z a : ℤ) (m k : ℕ) (mk : m ≤ k) :
    (∀ i ≤ k, a ∣ n^(m-i)*z^i) ↔ a ∣ (Int.gcd n z : ℤ)^m := by
  constructor
  · intro h
    let b := Int.gcdA n z
    let c := Int.gcdB n z
    have bez : (Int.gcd n z : ℤ) = z*c+n*b := by rw [add_comm]; exact Int.gcd_eq_gcd_ab n z
    rw [bez,add_pow]
    apply Finset.dvd_sum
    intro i hi
    have within := Nat.le_of_lt_succ (mem_range.mp hi)
    apply (h i (within.trans mk)).trans
    refine ⟨c^i*b^(m-i)*↑(m.choose i),?_⟩
    rw [mul_pow,mul_pow]
    ring
  · intro h i hi
    have ln : (Int.gcd n z : ℤ) ∣ n := Int.gcd_dvd_left
    have lz : (Int.gcd n z : ℤ) ∣ z := Int.gcd_dvd_right
    by_cases im : i ≤ m
    · apply h.trans
      have prod := mul_dvd_mul (pow_dvd_pow_of_dvd ln (m-i)) (pow_dvd_pow_of_dvd lz i)
      rwa [← pow_add, Nat.sub_add_cancel im] at prod
    · simpa [Nat.sub_eq_zero_of_le (by omega : m ≤ i)] using
        h.trans ((pow_dvd_pow_of_dvd lz m).trans (pow_dvd_pow z (by omega : m ≤ i)))

abbrev Rows (k : ℕ) := Matrix (Fin (k+1)) (Fin (k+1)) ℤ

/-- Rows in powers of Y=X−t. The weight is N^(m−i) for i<m and one for i≥m. -/
noncomputable def basis (k m : ℕ) (n : ℤ) : Rows k := Matrix.diagonal (fun i => n^(m-i.val))

noncomputable def minor {k : ℕ} (A : Rows k) : ℤ := (A.submatrix Fin.succ Fin.succ).det

theorem basis_content (n z a : ℤ) (m k : ℕ) (mk : m ≤ k) :
    (∀ i, a ∣ (basis k m n *ᵥ (fun j => z^j.val)) i) ↔ a ∣ (Int.gcd n z : ℤ)^m := by
  simp only [basis,Matrix.mulVec_diagonal]
  rw [← power_content n z a m k mk]
  exact ⟨fun h i hi => h ⟨i,by omega⟩,fun h i => h i.val (by omega)⟩

theorem det_basis (n : ℤ) (m k : ℕ) (mk : m ≤ k) :
    (basis k m n).det = n^(m+m.choose 2) := by
  rw [basis,Matrix.det_diagonal,Finset.prod_pow_eq_pow_sum]
  congr 1
  calc
    (∑ i : Fin (k+1), (m-i.val)) = ∑ i ∈ range (k+1), (m-i) :=
      Fin.sum_univ_eq_sum_range (fun i => m-i) _
    _ = ∑ i ∈ range (m+1), (m-i) := by
      apply Eq.symm
      apply sum_subset (range_mono (by omega : m+1≤k+1))
      intro i _ hi
      exact Nat.sub_eq_zero_of_le (by simp at hi; omega)
    _ = ∑ i ∈ range (m+1), i := by
      simpa using (sum_range_reflect id (m+1))
    _ = (m+1).choose 2 := by rw [sum_range_id,Nat.choose_two_right]
    _ = m+m.choose 2 := by rw [Nat.choose_succ_succ,Nat.choose_one_right]

/-- In any degree, replacing column zero by the row pairings gives a single cofactor
when all but row zero vanish. The coordinates may be affine, homogeneous, or arbitrary. -/
theorem determinant_pairing {k : ℕ} (A : Rows k) (v : Fin (k+1) → ℤ)
    (zeros : ∀ i : Fin k, (A *ᵥ v) i.succ = 0) :
    v 0 * A.det = (A *ᵥ v) 0 * minor A := by
  let B : Rows k := A.updateCol 0 (A *ᵥ v)
  have same : B.det = v 0 * A.det := by
    have column : A *ᵥ v = fun j => ∑ i, v i • A j i := by
      funext j
      change (∑ i : Fin (k+1), A j i*v i) = ∑ i : Fin (k+1), v i*A j i
      exact sum_congr rfl fun i _ => mul_comm _ _
    dsimp only [B]
    rw [column,Matrix.det_updateCol_sum]
    rfl
  have tail : B.submatrix Fin.succ Fin.succ = A.submatrix Fin.succ Fin.succ := by
    ext i j
    simp [B,Matrix.submatrix_apply,Matrix.updateCol_ne]
  rw [← same,Matrix.det_succ_column_zero,Fin.sum_univ_succ]
  simp [B,Matrix.updateCol_self,zeros,tail,minor]

/-- An invertible change of integral basis leaves the common divisors of its image unchanged. -/
theorem one_remaining {k : ℕ} (B U V : Rows k) (v : Fin (k+1) → ℤ) (inv : V*U=1)
    (zeros : ∀ i : Fin k, ((U*B) *ᵥ v) i.succ = 0) (a : ℤ) :
    (∀ i, a ∣ (B *ᵥ v) i) ↔ a ∣ ((U*B) *ᵥ v) 0 := by
  have lin (K : Rows k) (w : Fin (k+1) → ℤ) (h : ∀ i, a ∣ w i) (j : Fin (k+1)) :
      a ∣ (K *ᵥ w) j := by
    change a ∣ ∑ i, K j i*w i
    exact dvd_sum fun i _ => dvd_mul_of_dvd_right (h i) _
  have src := (Matrix.mulVec_mulVec v U B).symm
  have rev : B *ᵥ v = V *ᵥ ((U*B) *ᵥ v) := by rw [src,Matrix.mulVec_mulVec _ V U,inv,Matrix.one_mulVec]
  constructor
  · intro h
    rw [src]
    exact lin U _ h 0
  · intro h j
    rw [rev]
    apply lin V _ _ j
    intro i
    refine Fin.cases h (fun r => ?_) i
    rw [zeros r]
    exact dvd_zero _

theorem determinant_content (m k : ℕ) (mk : m ≤ k) (n z : ℤ) (U V : Rows k) (inv : V*U=1)
    (zeros : ∀ i : Fin k, ((U*basis k m n) *ᵥ (fun j => z^j.val)) i.succ = 0) :
    (minor (U*basis k m n)).natAbs * (Int.gcd n z)^m = n.natAbs^(m+m.choose 2) := by
  let v := fun j : Fin (k+1) => z^j.val
  let A := U*basis k m n
  have test (a : ℤ) : a ∣ (Int.gcd n z : ℤ)^m ↔ a ∣ (A *ᵥ v) 0 :=
    (basis_content n z a m k mk).symm.trans (one_remaining _ U V v inv zeros a)
  have left := (test _).mpr (dvd_refl _)
  have right := (test _).mp (dvd_refl _)
  have image : ((A *ᵥ v) 0).natAbs = (Int.gcd n z)^m :=
    Nat.dvd_antisymm
      (by simpa only [Int.natAbs_pow,Int.natAbs_ofNat] using Int.natAbs_dvd_natAbs.mpr left)
      (by simpa only [Int.natAbs_pow,Int.natAbs_ofNat] using Int.natAbs_dvd_natAbs.mpr right)
  have unit : U.det.natAbs=1 := by
    have h := congrArg (fun T : Rows k => T.det.natAbs) inv
    have both : V.det.natAbs=1 ∧ U.det.natAbs=1 := by
      simpa [Matrix.det_mul,Int.natAbs_mul] using h
    exact both.2
  have pair : A.det = (A *ᵥ v) 0 * minor A := by
    simpa [v] using determinant_pairing A v zeros
  have prod := congrArg Int.natAbs pair.symm
  rw [Int.natAbs_mul,image] at prod
  simpa [A,det_mul,det_basis n m k mk,Int.natAbs_mul,Int.natAbs_pow,unit,mul_comm] using prod

/-- Under the arithmetic gcd condition, divide out the public factor N^(m choose 2).
The remaining minor magnitude is the mth power of q. -/
theorem factor_minor (m k : ℕ) (mk : m ≤ k) (d q : ℕ) (positive : 0<d) (z : ℤ)
    (factor : Int.gcd ((d:ℤ)*q) z = d) (U V : Rows k) (inv : V*U=1)
    (zeros : ∀ i : Fin k, ((U*basis k m ((d:ℤ)*q)) *ᵥ (fun j => z^j.val)) i.succ = 0) :
    (minor (U*basis k m ((d:ℤ)*q))).natAbs = (d*q)^(m.choose 2) * q^m := by
  have ident := determinant_content m k mk ((d:ℤ)*q) z U V inv zeros
  rw [factor,Int.natAbs_mul,Int.natAbs_ofNat,Int.natAbs_ofNat] at ident
  apply Nat.eq_of_mul_eq_mul_right (pow_pos positive m)
  calc
    _ = (d*q)^(m+m.choose 2) := ident
    _ = _ := by rw [pow_add,mul_pow]; ring

end PrimeFactors.PowerJetContent
