import PrimeFactors.GeometricReadingLift

/-! Six scalar samples determine the three quadratic readings. Three samples
already give the two first directional coefficients. All input samples can be
independently reduced before taking the signed differences. -/

namespace PrimeFactors.GeometricReadingStencil
open Finset Polynomial GeometricReadingLift

/-- An integer representative of the first derivative modulo n². -/
def slope (n : ℕ) (plus minus : ℤ) : ℤ :=
  (plus-minus)/(n:ℤ) * (((n^2+1)/2 : ℕ) : ℤ)

/-- One positive sample after subtracting a first derivative known modulo n². -/
noncomputable def quadratic (n : ℕ) (plus zero lin : ℤ) : ZMod n :=
  (((plus-zero-(n:ℤ)*lin)/(n:ℤ)^2 : ℤ) : ZMod n)

noncomputable def linear (n : ℕ) (plus zero : ℤ) : ZMod n :=
  (((plus-zero)/(n:ℤ) : ℤ) : ZMod n)

theorem slope_correct {n : ℕ} (odd : Odd n) (F : ℤ[X]) {plus minus : ℤ}
    (hp : plus ≡ F.eval (n:ℤ) [ZMOD (n:ℤ)^3])
    (hm : minus ≡ F.eval (-(n:ℤ)) [ZMOD (n:ℤ)^3]) :
    slope n plus minus ≡ F.coeff 1 [ZMOD (n:ℤ)^2] := by
  obtain ⟨ap,hp⟩ := hp.symm.dvd
  obtain ⟨am,hm⟩ := hm.symm.dvd
  rw [taylor_three F (n:ℤ)] at hp
  rw [taylor_three F (-(n:ℤ))] at hm
  let E := F.divX.divX.divX.eval (n:ℤ)+F.divX.divX.divX.eval (-(n:ℤ))+ap-am
  have diff : plus-minus=(n:ℤ)*(2*F.coeff 1+n^2*E) := by
    dsimp only [E]
    linear_combination hp-hm
  have os := Nat.odd_iff.mp (odd.pow (n:=2))
  have o := Nat.odd_iff.mp odd
  have nz : (n:ℤ)≠0 := by exact_mod_cast (show n≠0 by omega)
  let halfSq : ℤ := ((n^2+1)/2 : ℕ)
  have twice : 2*halfSq=(n:ℤ)^2+1 := by
    change (2:ℤ)*(((n^2+1)/2:ℕ):ℤ)=_
    exact_mod_cast (show 2*((n^2+1)/2)=n^2+1 by omega)
  rw [slope,diff,Int.mul_ediv_cancel_left _ nz,Int.modEq_iff_dvd]
  refine ⟨-(F.coeff 1+E*halfSq),?_⟩
  change F.coeff 1-(2*F.coeff 1+(n:ℤ)^2*E)*halfSq=_
  linear_combination -F.coeff 1*twice

theorem quadratic_correct {n : ℕ} (pos : 0<n) (F : ℤ[X]) {plus zero lin : ℤ}
    (hp : plus ≡ F.eval (n:ℤ) [ZMOD (n:ℤ)^3])
    (hz : zero ≡ F.eval 0 [ZMOD (n:ℤ)^3])
    (hl : lin ≡ F.coeff 1 [ZMOD (n:ℤ)^2]) :
    quadratic n plus zero lin=F.coeff 2 := by
  obtain ⟨ap,hp⟩ := hp.symm.dvd
  obtain ⟨az,hz⟩ := hz.symm.dvd
  obtain ⟨al,hl⟩ := hl.symm.dvd
  rw [taylor_three F (n:ℤ)] at hp
  rw [←coeff_zero_eq_eval_zero] at hz
  let E := F.divX.divX.divX.eval (n:ℤ)+ap-az-al
  have diff : plus-zero-(n:ℤ)*lin=(n:ℤ)^2*(F.coeff 2+n*E) := by
    dsimp only [E]
    linear_combination hp-hz-(n:ℤ)*hl
  have nz : (n:ℤ)≠0 := by exact_mod_cast pos.ne'
  rw [quadratic,diff,Int.mul_ediv_cancel_left _ (pow_ne_zero _ nz)]
  push_cast
  rw [ZMod.natCast_self,zero_mul,add_zero]

theorem linear_correct {n : ℕ} (pos : 0<n) (F : ℤ[X]) {plus zero : ℤ}
    (hp : plus ≡ F.eval (n:ℤ) [ZMOD (n:ℤ)^2])
    (hz : zero ≡ F.eval 0 [ZMOD (n:ℤ)^2]) :
    linear n plus zero=F.coeff 1 := by
  obtain ⟨ap,hp⟩ := hp.symm.dvd
  obtain ⟨az,hz⟩ := hz.symm.dvd
  rw [taylor_three F (n:ℤ)] at hp
  rw [←coeff_zero_eq_eval_zero] at hz
  let E := F.coeff 2+(n:ℤ)*F.divX.divX.divX.eval (n:ℤ)+ap-az
  have diff : plus-zero=(n:ℤ)*(F.coeff 1+n*E) := by
    dsimp only [E]
    linear_combination hp-hz
  have nz : (n:ℤ)≠0 := by exact_mod_cast pos.ne'
  rw [linear,diff,Int.mul_ediv_cancel_left _ nz]
  push_cast
  rw [ZMod.natCast_self,zero_mul,add_zero]

/-- The three evaluation directions have a common constant and affine first
coefficient. These properties hold before any reduction modulo n. -/
theorem affine (I : Finset ℕ) (y g : ℤ) :
    (product I y g (-1)).coeff 1 =
      2*(product I y g 0).coeff 1-(product I y g 1).coeff 1 := by
  have const (S : Finset ℕ) (z : ℤ) :
      (product S y g z).coeff 0=∏ i ∈ S, (y-g^i) := by
    simp [coeff_zero_eq_eval_zero,eval_product]
  let f := GeometricMatchMoments.directionalFactor (R:=ℤ)
  have lin (z : ℤ) (i : ℕ) : (f y g z i).coeff 1=y*z-g^i*i := by
    simp only [f,GeometricMatchMoments.directionalFactor,coeff_sub,coeff_add,coeff_one_add_X_pow,coeff_C,coeff_C_mul_X,
      coeff_C_mul]
    simp
  have zero (z : ℤ) (i : ℕ) : (f y g z i).coeff 0=y-g^i := by
    simp [f,GeometricMatchMoments.directionalFactor,coeff_zero_eq_eval_zero]
  classical
  induction I using Finset.induction_on with
  | empty => simp [product]; ring
  | insert i I hi ih =>
    have ext (z : ℤ) : product (insert i I) y g z=f y g z i*product I y g z := by
      simp [product,f,hi]
    simp only [ext,mul_coeff_one,lin,zero,const]
    rw [ih]
    ring

theorem six {n : ℕ} (odd : Odd n) (I : Finset ℕ) (y g : ℤ)
    {zero p0 m0 p1 m1 pNeg : ℤ}
    (hz : zero ≡ (product I y g 0).eval 0 [ZMOD (n:ℤ)^3])
    (h0 : p0 ≡ (product I y g 0).eval (n:ℤ) [ZMOD (n:ℤ)^3])
    (h0m : m0 ≡ (product I y g 0).eval (-(n:ℤ)) [ZMOD (n:ℤ)^3])
    (h1 : p1 ≡ (product I y g 1).eval (n:ℤ) [ZMOD (n:ℤ)^3])
    (h1m : m1 ≡ (product I y g 1).eval (-(n:ℤ)) [ZMOD (n:ℤ)^3])
    (hn : pNeg ≡ (product I y g (-1)).eval (n:ℤ) [ZMOD (n:ℤ)^3]) :
    let read := GeometricDoubleMatch.reading I (y:ZMod n) g
    second n p0 m0 zero=read 0 ∧ second n p1 m1 zero=read 1 ∧
      quadratic n pNeg zero (2*slope n p0 m0-slope n p1 m1)=read (-1) := by
  have const (z : ℤ) : (product I y g 0).eval 0=(product I y g z).eval 0 := by simp [eval_product]
  have z1 := hz
  rw [const 1] at z1
  have zn := hz
  rw [const (-1)] at zn
  have o := Nat.odd_iff.mp odd
  have s0 := slope_correct odd _ h0 h0m
  have s1 := slope_correct odd _ h1 h1m
  have lin : 2*slope n p0 m0-slope n p1 m1 ≡ (product I y g (-1)).coeff 1 [ZMOD (n:ℤ)^2] := by
    rw [affine]
    exact (s0.mul_left 2).sub s1
  have cvt (z : ℤ) : ((product I y g z).coeff 2 : ZMod n)=
      GeometricDoubleMatch.reading I (y:ZMod n) g (z:ZMod n) := by
    rw [second_eq_reading]
    exact GeometricDoubleMatch.map_reading (Int.castRingHom (ZMod n)) I y g z
  refine ⟨?_,?_,?_⟩
  · simpa using ((extract odd _ h0 h0m hz).2.trans (cvt 0))
  · simpa using ((extract odd _ h1 h1m z1).2.trans (cvt 1))
  · simpa using ((quadratic_correct (by omega : 0<n) _ hn zn lin).trans (cvt (-1)))

theorem three {n : ℕ} (pos : 0<n) (I : Finset ℕ) (y g : ℤ) {zero p0 p1 : ℤ}
    (hz : zero ≡ (product I y g 0).eval 0 [ZMOD (n:ℤ)^2])
    (h0 : p0 ≡ (product I y g 0).eval (n:ℤ) [ZMOD (n:ℤ)^2])
    (h1 : p1 ≡ (product I y g 1).eval (n:ℤ) [ZMOD (n:ℤ)^2]) :
    linear n p0 zero=(product I y g 0).coeff 1 ∧
      linear n p1 zero=(product I y g 1).coeff 1 := by
  have same : (product I y g 0).eval 0=(product I y g 1).eval 0 := by simp [eval_product]
  exact ⟨linear_correct pos _ h0 hz,linear_correct pos _ h1 (same ▸ hz)⟩

end PrimeFactors.GeometricReadingStencil
