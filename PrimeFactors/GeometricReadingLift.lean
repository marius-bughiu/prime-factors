import PrimeFactors.GeometricDoubleMatch
import PrimeFactors.GeometricMatchMoments

/-! Recover low coefficients of a geometric product from scalar evaluations
modulo n³. Sample representatives may be reduced independently. -/

namespace PrimeFactors.GeometricReadingLift
open Finset Polynomial

/-- Three exact coefficients and the remaining integer quotient. -/
theorem taylor_three (F : ℤ[X]) (t : ℤ) :
    F.eval t = F.coeff 0+t*F.coeff 1+t^2*F.coeff 2+t^3*F.divX.divX.divX.eval t := by
  have step (P : ℤ[X]) : P.eval t=P.divX.eval t*t+P.coeff 0 := by
    simpa only [eval_add,eval_mul,eval_X,eval_C] using
      (congrArg (Polynomial.eval t) (divX_mul_X_add P)).symm
  calc
    F.eval t = F.divX.eval t*t+F.coeff 0 := step F
    _ = _ := by
      rw [step F.divX,step F.divX.divX]
      simp only [coeff_divX]
      ring

/-- The canonical inverse of two for an odd positive modulus. -/
noncomputable def half (n : ℕ) : ZMod n := ((n+1)/2 : ℕ)

theorem two_half {n : ℕ} (odd : Odd n) : 2*half n=1 := by
  have o := Nat.odd_iff.mp odd
  have eq : 2*((n+1)/2)=n+1 := by omega
  have c := congrArg (fun i:ℕ => (i:ZMod n)) eq
  simpa [half] using c

/-- Integer division is performed after subtracting the sample representatives. -/
noncomputable def first (n : ℕ) (plus minus : ℤ) : ZMod n :=
  (((plus-minus)/(n:ℤ) : ℤ) : ZMod n)*half n

noncomputable def second (n : ℕ) (plus minus zero : ℤ) : ZMod n :=
  (((plus+minus-2*zero)/(n:ℤ)^2 : ℤ) : ZMod n)*half n

theorem extract {n : ℕ} (odd : Odd n) (F : ℤ[X]) {plus minus zero : ℤ}
    (hp : plus ≡ F.eval (n:ℤ) [ZMOD (n:ℤ)^3])
    (hm : minus ≡ F.eval (-(n:ℤ)) [ZMOD (n:ℤ)^3])
    (hz : zero ≡ F.eval 0 [ZMOD (n:ℤ)^3]) :
    first n plus minus=F.coeff 1 ∧ second n plus minus zero=F.coeff 2 := by
  obtain ⟨ap,hp⟩ := hp.symm.dvd
  obtain ⟨am,hm⟩ := hm.symm.dvd
  obtain ⟨az,hz⟩ := hz.symm.dvd
  rw [taylor_three F (n:ℤ)] at hp
  rw [taylor_three F (-(n:ℤ))] at hm
  rw [←coeff_zero_eq_eval_zero] at hz
  let rp := F.divX.divX.divX.eval (n:ℤ)
  let rm := F.divX.divX.divX.eval (-(n:ℤ))
  change _ - (_+_+_+(n:ℤ)^3*rp)=_ at hp
  change _ - (_+_+_+(-(n:ℤ))^3*rm)=_ at hm
  have one : plus-minus=(n:ℤ)*(2*F.coeff 1+n^2*(rp+rm+ap-am)) := by
    linear_combination hp-hm
  have two : plus+minus-2*zero=(n:ℤ)^2*(2*F.coeff 2+n*(rp-rm+ap+am-2*az)) := by
    linear_combination hp+hm-2*hz
  have np := Nat.odd_iff.mp odd
  have nz : (n:ℤ)≠0 := by exact_mod_cast (show n≠0 by omega)
  constructor
  · rw [first,one,Int.mul_ediv_cancel_left _ nz]
    push_cast
    rw [ZMod.natCast_self]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,zero_mul,add_zero]
    calc
      (2:ZMod n)*(F.coeff 1)*half n=(F.coeff 1:ZMod n)*(2*half n) := by ring
      _ = _ := by rw [two_half odd,mul_one]
  · rw [second,two,Int.mul_ediv_cancel_left _ (pow_ne_zero 2 nz)]
    push_cast
    rw [ZMod.natCast_self,zero_mul,add_zero]
    calc
      (2:ZMod n)*(F.coeff 2)*half n=(F.coeff 2:ZMod n)*(2*half n) := by ring
      _ = _ := by rw [two_half odd,mul_one]

/-- Scalar product evaluated by the numerical routine. -/
noncomputable def product {R : Type*} [CommRing R] (I : Finset ℕ) (y g z : R) : R[X] :=
  ∏ i ∈ I, GeometricMatchMoments.directionalFactor y g z i

theorem eval_product {R : Type*} [CommRing R] (I : Finset ℕ) (y g z t : R) :
    (product I y g z).eval t = ∏ i ∈ I, (y*(1+z*t) - (g*(1+t))^i) := by
  rw [product,eval_prod]
  apply prod_congr rfl
  intro i _
  simp only [GeometricMatchMoments.directionalFactor,eval_sub,eval_add,eval_mul,eval_C,
    eval_X,eval_pow,eval_one,mul_pow]
  ring

private theorem factor_agrees {R : Type*} [CommRing R] (y g z : R) (i : ℕ) :
    X^3 ∣ GeometricMatchMoments.directionalFactor y g z i -
      GeometricDoubleMatch.factor y g z i := by
  rw [X_pow_dvd_iff]
  intro d hd
  interval_cases d <;> simp only [GeometricMatchMoments.directionalFactor,GeometricDoubleMatch.factor,
    coeff_sub,coeff_add,coeff_C_mul_X,coeff_C_mul,coeff_one_add_X_pow,coeff_C,coeff_X_mul,coeff_X] <;>
    simp <;> ring

private theorem product_agrees {R : Type*} [CommRing R] (I : Finset ℕ) (y g z : R) :
    X^3 ∣ product I y g z - ∏ i ∈ I, GeometricDoubleMatch.factor y g z i := by
  classical
  unfold product
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih =>
    let a := GeometricMatchMoments.directionalFactor y g z i
    let b := GeometricDoubleMatch.factor y g z i
    let A := ∏ j ∈ I, GeometricMatchMoments.directionalFactor y g z j
    let B := ∏ j ∈ I, GeometricDoubleMatch.factor y g z j
    simp only [prod_insert hi]
    change X^3 ∣ a*A-b*B
    rw [show a*A-b*B=(a-b)*A+b*(A-B) by ring]
    exact dvd_add (dvd_mul_of_dvd_left (factor_agrees y g z i) A) (dvd_mul_of_dvd_right ih b)

theorem second_eq_reading {R : Type*} [CommRing R] (I : Finset ℕ) (y g z : R) :
    (product I y g z).coeff 2 = GeometricDoubleMatch.reading I y g z := by
  have same := X_pow_dvd_iff.mp (product_agrees I y g z) 2 (by decide)
  simpa only [coeff_sub,sub_eq_zero,GeometricDoubleMatch.reading] using same

/-- Three samples of the integer geometric product return precisely the
quadratic reading over ZMod n used by the local matching theorems. -/
theorem geometric {n : ℕ} (odd : Odd n) (I : Finset ℕ) (y g z : ℤ)
    {plus minus zero : ℤ}
    (hp : plus ≡ ∏ i ∈ I, (y*(1+z*n)-(g*(1+n))^i) [ZMOD (n:ℤ)^3])
    (hm : minus ≡ ∏ i ∈ I, (y*(1+z*(-(n:ℤ)))-(g*(1+(-(n:ℤ))))^i) [ZMOD (n:ℤ)^3])
    (hz : zero ≡ ∏ i ∈ I, (y-g^i) [ZMOD (n:ℤ)^3]) :
    second n plus minus zero=GeometricDoubleMatch.reading I (y:ZMod n) g z := by
  have ex := (extract odd (product I y g z) (by simpa only [eval_product] using hp)
    (by simpa only [eval_product] using hm) (by simpa [eval_product] using hz)).2
  rw [second_eq_reading] at ex
  exact ex.trans (GeometricDoubleMatch.map_reading (Int.castRingHom (ZMod n)) I y g z)

end PrimeFactors.GeometricReadingLift
