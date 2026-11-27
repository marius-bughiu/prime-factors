import PrimeFactors.NormDirections
import PrimeFactors.OffsetCoordinateMultiplicity
import Mathlib.Data.Rat.Lemmas

/-! Every supplied root of a nonsquare signed D with (abs D) ≤ 6 gives a short
primitive point of norm ±N or ±2N, by weighted two-dimensional Gauss reduction. -/
namespace PrimeFactors.SmallDiscriminantLattice

/-- A signed norm representation with an invertible denominator at the given
root. Its height uses the positive definite form even when D is positive. -/
structure Representation (N : ℕ) (D : ℤ) (r : ZMod N) where
  x : ℤ
  y : ℤ
  m : ℤ
  norm : x^2-D*y^2=m*N
  multiplier : 0<m.natAbs ∧ m.natAbs≤2
  height : x^2+(abs D)*y^2<3*(N:ℤ)
  hermite : 3*(x^2+(abs D)*y^2)^2 ≤ 4*(abs D)*(N:ℤ)^2
  point : (x:ZMod N)=r*y
  primitive : IsCoprime x y
  unit : IsUnit (y:ZMod N)

private theorem small_coprime {m : ℤ} {N : ℕ} (odd : Odd N) (small : m.natAbs≤2)
    (nz : m≠0) : IsCoprime m (N:ℤ) := by
  have two : IsCoprime (2:ℤ) (N:ℤ) := (Nat.prime_two.coprime_iff_not_dvd.mpr
    (fun h => odd.not_two_dvd_nat h)).isCoprime
  rcases (show m=1 ∨ m= -1 ∨ m=2 ∨ m= -2 by omega) with e|e|e|e <;> rw [e]
  · exact isCoprime_one_left
  · exact isCoprime_one_left.neg_left
  · exact two
  · exact two.neg_left

/-- Weighted Gauss reduction of the lattice determined by r gives a primitive
short representation. Oddness of N suffices even if N has repeated factors. -/
theorem exists_representation {N : ℕ} (np : 0<N) (odd : Odd N) {D : ℤ}
    (dp : 0<(abs D)) (small : (abs D)≤6) (ns : ¬IsSquare (D:ℚ)) (r : ZMod N) (root : r^2=D) :
    Nonempty (Representation N D r) := by
  letI : NeZero N := ⟨np.ne'⟩
  let R : ℤ := r.val
  have castR : (R:ZMod N)=r := by simp [R]
  have npz : 0<(N:ℤ) := by exact_mod_cast np
  obtain ⟨a,b,u,w,basis,ordered,reduced⟩ :=
    OffsetCoordinateMultiplicity.exists_reduced (-R) (c:=(N:ℤ)) dp npz
  let x : ℤ := N*a-(-R)*b
  let z : ℤ := N*u-(-R)*w
  have det : x*w-z*b=N := by dsimp [x,z]; linear_combination (N:ℤ)*basis
  change x^2+(abs D)*b^2 ≤ z^2+(abs D)*w^2 at ordered
  change |2*(x*z+(abs D)*b*w)| ≤ x^2+(abs D)*b^2 at reduced
  have hermite := NormDirections.reduced_bound dp.le (congrArg (·^2) det) ordered
    (by simpa only [abs_mul,show |(2:ℤ)|=2 from rfl] using reduced)
  have height : x^2+(abs D)*b^2<3*(N:ℤ) := by
    apply lt_of_not_ge
    intro big
    have h := pow_le_pow_left₀ (by positivity : 0≤3*(N:ℤ)) big 2
    nlinarith only [h,hermite,mul_le_mul_of_nonneg_right small (sq_nonneg (N:ℤ)),sq_pos_of_pos npz]
  have point : (x:ZMod N)=r*b := by simp [x,castR]
  have rr : (N:ℤ) ∣ R^2-D := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [castR,root,sub_self]
  obtain ⟨e,he⟩ := rr
  let c := R*a+e*b
  let m := a*x+c*b
  have norm : x^2-D*b^2=m*N := by
    dsimp [m,c,x]
    linear_combination b^2*he
  have nonzero : m≠0 := by
    rintro h
    rw [h,zero_mul] at norm
    by_cases bz : b=0
    · rw [bz] at norm det
      simp at norm
      simp [norm] at det
      omega
    · apply ns
      apply (isSquare_iff_exists_sq _).mpr
      have sq : (x:ℚ)^2=(D:ℚ)*(b:ℚ)^2 := by exact_mod_cast sub_eq_zero.mp norm
      exact ⟨(x:ℚ)/b,by rw [div_pow,sq,mul_div_cancel_right₀ _ (pow_ne_zero 2 (by exact_mod_cast bz))]⟩
  have ms : m.natAbs≤2 := by
    have ub := mul_le_mul_of_nonneg_right (le_abs_self D) (sq_nonneg b)
    have lb := mul_le_mul_of_nonneg_right (neg_abs_le D) (sq_nonneg b)
    have lo : (-3:ℤ)*N < m*N := by nlinarith only [ub,norm,height,sq_nonneg x]
    have hi : m*N < (3:ℤ)*N := by nlinarith only [lb,norm,height,sq_nonneg x]
    have h₁ := (mul_lt_mul_right npz).mp lo
    have h₂ := (mul_lt_mul_right npz).mp hi
    omega
  obtain ⟨h,j,bez⟩ := small_coprime odd ms nonzero
  have prim : IsCoprime x b := by
    refine ⟨h*a+j*w, h*c-j*z,?_⟩
    change h*(a*x+c*b)+j*N=1 at bez
    linear_combination bez+j*det
  have bunit : IsUnit (b:ZMod N) := by
    obtain ⟨l,i,lin⟩ := prim
    have rel := congrArg (fun t:ℤ => (t:ZMod N)) lin
    push_cast at rel
    rw [point] at rel
    apply isCoprime_zero_right.mp
    refine ⟨(l:ZMod N)*r+i,0,?_⟩
    linear_combination rel
  exact ⟨⟨x,b,m,norm,⟨Int.natAbs_pos.mpr nonzero,ms⟩,height,hermite,point,prim,bunit⟩⟩

/-- Two inequivalent roots give a proper gcd of the short coordinates.
Changing the coordinates without changing the underlying sign class leaves
the same gcd as direct comparison of the roots. -/
theorem cross_gcd {N : ℕ} [NeZero N] {D : ℤ} {r t : ZMod N}
    (u : Representation N D r) (v : Representation N D t) :
    ((u.x:ZMod N)*v.y-(v.x:ZMod N)*u.y).val.gcd N = (r-t).val.gcd N := by
  let w := (u.unit.mul v.unit).unit
  have wz : (w:ZMod N)=(u.y:ZMod N)*v.y := (u.unit.mul v.unit).unit_spec
  have eq : (u.x:ZMod N)*v.y-(v.x:ZMod N)*u.y=(w:ZMod N)*r-w*t := by
    rw [u.point,v.point,wz]
    ring
  rw [eq,maskedRelations_unit_gcd]

theorem split {N : ℕ} [NeZero N] {D : ℤ} {r t : ZMod N}
    (u : Representation N D r) (v : Representation N D t) (rr : r^2=D) (tr : t^2=D)
    (diff : r≠t) (opposite : r≠-t) :
    let g := ((u.x:ZMod N)*v.y-(v.x:ZMod N)*u.y).val.gcd N
    1<g ∧ g<N := by simpa only [cross_gcd u v] using maskedRelations_split (rr.trans tr.symm) diff opposite

end PrimeFactors.SmallDiscriminantLattice
