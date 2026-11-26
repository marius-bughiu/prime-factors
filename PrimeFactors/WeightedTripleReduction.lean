import PrimeFactors.WeightedMultiplierPopulation
import PrimeFactors.AffineExcessSingle

/-! Proportional rows are redundant in a three-row square relation.
In particular all three pairwise determinants of a relation with three
nonsquare remainders must be nonzero. -/

namespace PrimeFactors.WeightedTripleReduction
open WeightedMultiplierPopulation

/-- If two positive remainders come from proportional rows and their product
times a third remainder is a square, the third remainder is already a square. -/
theorem square_of_proportional {r s A B d e n f z : ℕ}
    (first : A^2=d+4*r*n) (second : B^2=e+4*s*n)
    (dp : 0<d) (ep : 0<e) (same : s*A^2=r*B^2) (square : d*e*f=z^2) :
    IsSquare f := by
  have ap : 0<A := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    simp only [zero_pow (by decide : 2≠0)] at first
    omega
  have cross : B^2*d=A^2*e := by
    have h : (B:ℤ)^2*d=(A:ℤ)^2*e := by
      have ha : (A:ℤ)^2=d+4*(r:ℤ)*n := by exact_mod_cast first
      have hb : (B:ℤ)^2=e+4*(s:ℤ)*n := by exact_mod_cast second
      have hr : (s:ℤ)*A^2=(r:ℤ)*B^2 := by exact_mod_cast same
      linear_combination (A:ℤ)^2*hb-(B:ℤ)^2*ha+4*(n:ℤ)*hr
    exact_mod_cast h
  have eq : (B*d)^2=A^2*(d*e) := by
    calc
      _ = (B^2*d)*d := by ring
      _ = _ := by rw [cross]; ring
  obtain ⟨w,_,hw⟩ := AffineExcessSingle.remove_square ap eq
  have wp : 0<w := by
    have hp := Nat.mul_pos dp ep
    apply Nat.pos_of_ne_zero
    rintro rfl
    simp only [zero_pow (by decide : 2≠0)] at hw
    omega
  have reduced : z^2=w^2*f := by rw [hw,square]
  obtain ⟨k,_,hk⟩ := AffineExcessSingle.remove_square wp reduced
  exact ⟨k,by rw [←hk,pow_two]⟩

/-- A third nonsquare remainder in a square relation certifies that the
determinant of the first two rows is positive. -/
theorem positive_difference {r s A B d e n f z : ℕ}
    (first : A^2=d+4*r*n) (second : B^2=e+4*s*n)
    (dp : 0<d) (ep : 0<e) (square : d*e*f=z^2) (nf : ¬IsSquare f) :
    0<difference (r,s) A B := by
  apply Nat.pos_of_ne_zero
  intro zero
  have same : (s:ℤ)*A^2=(r:ℤ)*B^2 := sub_eq_zero.mp (Int.natAbs_eq_zero.mp zero)
  exact nf (square_of_proportional first second dp ep (by exact_mod_cast same) square)

end PrimeFactors.WeightedTripleReduction
