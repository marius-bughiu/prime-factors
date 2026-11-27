import PrimeFactors.JacobiPeriodSquareClass

/-! Coordinates for positive pairs whose product is a bounded scale times
a square. The common coordinate is their gcd. -/

namespace PrimeFactors.SquareScalePairCoordinates

/-- Removing the gcd leaves coprime factors. The product of their squarefree
parts divides every positive scale witnessing a square for the original pair. -/
theorem coordinates {A B t y L : ℕ} (hA : 0<A) (hB : 0<B) (ht : 0<t) (limit : t≤L)
    (hit : A*B=t*y^2) :
    ∃ d u v x z : ℕ, 0<d ∧ 0<u ∧ 0<v ∧ 0<x ∧ 0<z ∧
      A=d*u*x^2 ∧ B=d*v*z^2 ∧ u*v≤L ∧ u*v∣t ∧ d=A.gcd B ∧ Squarefree (u*v) := by
  let d := A.gcd B
  have dp : 0<d := Nat.gcd_pos_of_pos_left B hA
  have reduced : (A/d).Coprime (B/d) := Nat.coprime_div_gcd_div_gcd dp
  obtain ⟨u,x,up,xp,left,ufree⟩ := Nat.sq_mul_squarefree_of_pos
    (Nat.div_pos (Nat.gcd_le_left B hA) dp)
  obtain ⟨v,z,vp,zp,right,vfree⟩ := Nat.sq_mul_squarefree_of_pos
    (Nat.div_pos (Nat.gcd_le_right _ hB) dp)
  have cop : u.Coprime v := (reduced.of_dvd_left (left ▸ dvd_mul_left u (x^2))).of_dvd_right
    (right ▸ dvd_mul_left v (z^2))
  have free := (Nat.squarefree_mul cop).mpr ⟨ufree,vfree⟩
  have formA : A=d*u*x^2 := calc
    A = d*(A/d) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)).symm
    _ = _ := by rw [←left]; ring
  have formB : B=d*v*z^2 := calc
    B = d*(B/d) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)).symm
    _ = _ := by rw [←right]; ring
  have same : (u*v)*(d*x*z)^2=t*y^2 := calc
    _ = (d*u*x^2)*(d*v*z^2) := by ring
    _ = _ := by rw [←formA,←formB,hit]
  have yp : 0<y := by
    by_contra! zero
    rw [Nat.eq_zero_of_le_zero zero,pow_succ,mul_zero,mul_zero] at hit
    exact (Nat.mul_pos hA hB).ne' hit
  obtain ⟨w,_,scale⟩ := JacobiPeriodSquareClass.square_class free yp same
  have divides : u*v ∣ t := ⟨w^2,scale⟩
  exact ⟨d,u,v,x,z,dp,up,vp,xp,zp,formA,formB,(Nat.le_of_dvd ht divides).trans limit,
    divides,rfl,free⟩

/-- A member bound on either factor transfers directly to its square coordinate. -/
theorem member_le_iff {A d u x H : ℕ} (form : A=d*u*x^2) : x^2*d*u≤H ↔ A≤H := by
  rw [show x^2*d*u=d*u*x^2 by ring, ←form]

end PrimeFactors.SquareScalePairCoordinates
