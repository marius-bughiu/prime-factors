import PrimeFactors.QuarticDeterminantFactor
import Mathlib.RingTheory.Coprime.Lemmas

namespace PrimeFactors.DivisorWindowQuotient

/-- In coordinates Y=X−t suppose the true root is a and N=dq. For a polynomial
(Y−a)R(Y), let C=R(0), L=R'(0). These are exactly the two remaining jet conditions.
No assumption on higher coefficients of R is needed. -/
theorem quotient_coefficients {d q a C L : ℤ} (da : d ∣ a)
    (cop : IsCoprime d q) (unit : IsCoprime q a) :
    ((d*q)^2 ∣ -a*C ∧ d*q ∣ C-a*L) ↔ d*q^2 ∣ C ∧ q ∣ L := by
  constructor
  · rintro ⟨const,lin⟩
    have qsq : q^2 ∣ C := by
      apply unit.pow_left.dvd_of_dvd_mul_left
      have h := (pow_dvd_pow_of_dvd (dvd_mul_left q d) 2).trans const
      simpa only [neg_mul, dvd_neg] using h
    have c_d : d ∣ C := by
      have h := (dvd_mul_right d q).trans lin
      simpa only [sub_add_cancel] using dvd_add h (dvd_mul_of_dvd_left da L)
    have c_q := (dvd_pow_self q (by decide : 2≠0)).trans qsq
    have l_q : q ∣ L := by
      apply unit.dvd_of_dvd_mul_left
      have h := (dvd_mul_left q d).trans lin
      simpa only [sub_sub_cancel] using dvd_sub c_q h
    exact ⟨cop.pow_right.mul_dvd c_d qsq,l_q⟩
  · rintro ⟨⟨v,hc⟩,⟨u,hl⟩⟩
    obtain ⟨h,ha⟩ := da
    rw [hc,hl,ha]
    constructor
    · exact ⟨-h*v,by ring⟩
    · exact ⟨q*v-h*u,by ring⟩

open Matrix Finset

/-- After dividing by the common linear factor, the three high coefficients
of a quotient-basis row are an integral combination of (q,0,0),(0,1,0),(0,0,1).
Multiplying back by Y−a takes (B,C,D) to (B−aC,C−aD,D) in those columns. -/
noncomputable def highTransform (q a : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![q,0,0; -a,1,0; 0,-a,1]

theorem high_det (q a : ℤ) : (highTransform q a).det=q := by
  simp [highTransform,Matrix.det_fin_three]

noncomputable def tripleMinor (U : Matrix (Fin 4) (Fin 4) ℤ) (q a : ℤ) (i : Fin 4) : ℤ :=
  ((U.submatrix i.succAbove Fin.succ) * highTransform q a).det

/-- For four quotient rows forming a full basis the four high-column minors
have gcd |q|. This is an identity of common divisors, valid for any signed q. -/
theorem triple_content (U : Matrix (Fin 4) (Fin 4) ℤ) (unit : IsUnit U.det)
    (q a z : ℤ) : (∀ i : Fin 4, z ∣ tripleMinor U q a i) ↔ z ∣ q := by
  have eq (i : Fin 4) : tripleMinor U q a i = (U.submatrix i.succAbove Fin.succ).det*q := by
    rw [tripleMinor,Matrix.det_mul,high_det]
  constructor
  · intro each
    have h : z ∣ U.det*q := by
      rw [Matrix.det_succ_column_zero,Finset.sum_mul]
      apply Finset.dvd_sum
      intro i _
      have H := each i
      rw [eq i] at H
      rw [mul_assoc]
      exact dvd_mul_of_dvd_right H _
    exact unit.dvd_mul_left.mp h
  · intro div i
    rw [eq]
    exact dvd_mul_of_dvd_right div _

end PrimeFactors.DivisorWindowQuotient
