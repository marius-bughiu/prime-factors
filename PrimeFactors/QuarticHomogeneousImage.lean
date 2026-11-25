import PrimeFactors.QuarticDeterminantFactor

namespace PrimeFactors.QuarticHomogeneousImage

open Matrix QuarticDeterminantFactor
open scoped Matrix

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

/-- Degree-four projective evaluation at the primitive pair (u,v).
When v is nonzero this clears the denominator of evaluation at u/v. -/
noncomputable def point (u v : ℤ) : Fin 5 → ℤ := ![v^4,u*v^3,u^2*v^2,u^3*v,u^4]

theorem canonical_values (n t u v : ℤ) :
    canonical n t *ᵥ point u v =
      ![n^2*v^4,n*(u-t*v)*v^3,(u-t*v)^2*v^2,
        u*(u-t*v)^2*v,u^2*(u-t*v)^2] := by
  funext i
  fin_cases i <;> simp [canonical,point,Matrix.mulVec,dotProduct,Fin.sum_univ_five] <;> ring

private theorem square_image (n k a : ℤ) :
    (a∣n^2 ∧ a∣n*k ∧ a∣k^2) ↔ a∣(Int.gcd n k:ℤ)^2 := by
  have eq := evaluation_image n 0 k a
  rw [values] at eq
  simp only [sub_zero] at eq
  constructor
  · rintro ⟨hn,hm,hk⟩
    apply eq.mp
    intro i
    fin_cases i
    · exact hn
    · exact hm
    · exact hk
    · exact dvd_mul_of_dvd_right hk _
    · exact dvd_mul_of_dvd_right hk _
  · intro h
    exact ⟨eq.mpr h 0,eq.mpr h 1,eq.mpr h 2⟩

/-- Every common divisor of the five homogeneous values divides g², and
conversely, including at infinity and when N or u−tv is zero. -/
theorem homogeneous_image (n t u v a : ℤ) (cop : IsCoprime u v) :
    (∀ i, a∣(canonical n t *ᵥ point u v) i) ↔ a∣(Int.gcd n (u-t*v):ℤ)^2 := by
  rw [canonical_values,←square_image]
  let k := u-t*v
  obtain ⟨b,c,bez⟩ := cop
  have kc : IsCoprime k v := ⟨b,c+b*t,by dsimp [k]; linear_combination bez⟩
  constructor
  · intro h
    have vv : a∣k^2*v^2 := h 2
    have uv : a∣u*k^2*v := h 3
    have uu : a∣u^2*k^2 := h 4
    obtain ⟨j,hj⟩ := vv
    obtain ⟨l,hl⟩ := uv
    obtain ⟨m,hm⟩ := uu
    have kk : a∣k^2 := by
      refine ⟨m*b^2+2*l*b*c+j*c^2,?_⟩
      calc
        k^2 = k^2*(b*u+c*v)^2 := by rw [bez]; ring
        _ = _ := by linear_combination b^2*hm+(2*b*c)*hl+c^2*hj
    have ac := (kc.pow_left (m:=2)).of_isCoprime_of_dvd_left kk
    exact ⟨(ac.pow_right (n:=4)).dvd_of_dvd_mul_right (h 0),
      (ac.pow_right (n:=3)).dvd_of_dvd_mul_right (h 1),kk⟩
  · rintro ⟨hn,hm,hk⟩ i
    fin_cases i
    · exact dvd_mul_of_dvd_left hn _
    · exact dvd_mul_of_dvd_left hm _
    · exact dvd_mul_of_dvd_left hk _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hk _) _
    · exact dvd_mul_of_dvd_right hk _

/-- At a common primitive rational zero of four basis rows the fifth
homogeneous value has absolute value exactly g². -/
theorem remaining_homogeneous (n t u v : ℤ) (U V : Rows) (inv : V*U=1)
    (cop : IsCoprime u v)
    (zeros : ∀ i : Fin 4, ((U*canonical n t) *ᵥ point u v) i.succ=0) :
    (((U*canonical n t) *ᵥ point u v) 0).natAbs = (Int.gcd n (u-t*v))^2 := by
  let y := ((U*canonical n t) *ᵥ point u v) 0
  let g := (Int.gcd n (u-t*v):ℤ)^2
  have image (a : ℤ) : a∣y ↔ a∣g :=
    (one_remaining_image (canonical n t) U V (point u v) inv zeros a).symm.trans
      (homogeneous_image n t u v a cop)
  have left := (image y).mp (dvd_refl _)
  have right := (image g).mpr (dvd_refl _)
  exact Nat.dvd_antisymm
    (by simpa only [g,Int.natAbs_pow,Int.natAbs_ofNat] using Int.natAbs_dvd_natAbs.mpr left)
    (by simpa only [g,Int.natAbs_pow,Int.natAbs_ofNat] using Int.natAbs_dvd_natAbs.mpr right)

/-- The normalized principal minor up to sign is the coefficient V₀₀
representing N² in the changed basis. Homogenization contributes v⁴ to
the representation of the constant row. -/
theorem coefficient_identity (n t u v : ℤ) (U V : Rows) (inv : V*U=1)
    (cop : IsCoprime u v)
    (zeros : ∀ i : Fin 4, ((U*canonical n t) *ᵥ point u v) i.succ=0) :
    (V 0 0).natAbs * (Int.gcd n (u-t*v))^2 = (n.natAbs*v.natAbs^2)^2 := by
  have rev : canonical n t *ᵥ point u v = V *ᵥ ((U*canonical n t) *ᵥ point u v) := by
    rw [Matrix.mulVec_mulVec,←Matrix.mul_assoc,inv,Matrix.one_mul]
  have rep := congrFun rev 0
  rw [canonical_values] at rep
  have eq : n^2*v^4 = V 0 0 * (((U*canonical n t) *ᵥ point u v) 0) := by
    change n^2*v^4 = ∑ i, V 0 i*(((U*canonical n t) *ᵥ point u v) i) at rep
    simpa only [Fin.sum_univ_succ,zeros,mul_zero,Finset.sum_const_zero,add_zero] using rep
  have absEq := congrArg Int.natAbs eq
  rw [Int.natAbs_mul,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_pow,
      remaining_homogeneous n t u v U V inv cop zeros] at absEq
  rw [←absEq]
  ring

/-- An explicit square even when u/v is not an integer. -/
theorem coefficient_square (n t u v : ℤ) (nonzero : n≠0) (U V : Rows) (inv : V*U=1)
    (cop : IsCoprime u v)
    (zeros : ∀ i : Fin 4, ((U*canonical n t) *ᵥ point u v) i.succ=0) :
    (V 0 0).natAbs = ((n.natAbs*v.natAbs^2)/(Int.gcd n (u-t*v)))^2 := by
  let g := Int.gcd n (u-t*v)
  have gp : 0<g := Int.gcd_pos_of_ne_zero_left _ nonzero
  have gd : g ∣ n.natAbs := by
    simpa only [Int.natAbs_ofNat] using
      Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_left (a:=n) (b:=u-t*v))
  have divides := dvd_mul_of_dvd_left gd (v.natAbs^2)
  apply Nat.eq_of_mul_eq_mul_right (pow_pos gp 2)
  rw [←Nat.mul_pow,Nat.div_mul_cancel divides]
  exact coefficient_identity n t u v U V inv cop zeros

end PrimeFactors.QuarticHomogeneousImage
