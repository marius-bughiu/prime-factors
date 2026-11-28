import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-! If the midpoint is a multiple of u and the half-gap a multiple of v,
the product determines the square of the normalized half-gap modulo u².
A bound on the half-gap controls how many lifts of that one residue suffice. -/
namespace PrimeFactors.SumGapDivisorReadout

/-- Least residue of −N / v² modulo u². The intended moduli are coprime. -/
noncomputable def residue (N u v : ℕ) : ℕ :=
  ((-((N : ℕ) : ZMod (u^2))) * (((v^2 : ℕ) : ZMod (u^2)))⁻¹).val

/-- The j-th nonnegative integer with the measured square remainder. -/
noncomputable def lift (N u v j : ℕ) : ℕ := residue N u v + u^2*j

/-- Pair obtained by taking ordinary integer square roots at one specified lift. -/
noncomputable def candidate (N u v j : ℕ) : ℕ×ℕ :=
  let d := v*(lift N u v j).sqrt
  let h := (N+d^2).sqrt
  (h-d,h+d)

theorem residue_eq {N u v c e : ℕ} (cop : u.Coprime v)
    (eqn : N+(v*e)^2=(u*c)^2) : residue N u v = e^2 % u^2 := by
  let m := u^2
  have unit : IsUnit (((v^2 : ℕ) : ZMod m)) :=
    (ZMod.isUnit_iff_coprime ..).mpr ((cop.symm.pow_left 2).pow_right 2)
  have lifted : (N : ZMod m) + ((v^2 : ℕ) : ZMod m)*((e^2 : ℕ) : ZMod m)=0 := by
    have h := congrArg (fun z : ℕ => (z : ZMod m)) eqn
    rw [mul_pow,mul_pow] at h
    change ((N+v^2*e^2 : ℕ) : ZMod m)=((m*c^2 : ℕ) : ZMod m) at h
    simpa only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul] using h
  have neg : -(N : ZMod m)=((v^2 : ℕ) : ZMod m)*((e^2 : ℕ) : ZMod m) :=
    neg_eq_iff_add_eq_zero.mpr lifted
  unfold residue
  change ((-(N : ZMod m))*(((v^2 : ℕ) : ZMod m))⁻¹).val=_
  rw [neg,mul_comm (((v^2 : ℕ) : ZMod m)) _,mul_assoc,ZMod.mul_inv_of_unit _ unit,mul_one]
  exact ZMod.val_natCast _ _

theorem lift_eq {N u v c e : ℕ} (cop : u.Coprime v)
    (eqn : N+(v*e)^2=(u*c)^2) : lift N u v (e^2/u^2)=e^2 := by
  rw [lift,residue_eq cop eqn,Nat.mod_add_div]

/-- The actual index is below J exactly when the normalized half-gap squared
is below J times the modulus. This includes the one-lift case e < u. -/
theorem index_lt {u e J : ℕ} (pos : 0<u) :
    e^2/u^2 < J ↔ e^2 < J*u^2 := Nat.div_lt_iff_lt_mul (pow_pos pos 2)

theorem pair_eq {p q N u v c e : ℕ} (cop : u.Coprime v)
    (mid : p+v*e=u*c) (top : q=p+2*v*e) (product : p*q=N) :
    candidate N u v (e^2/u^2)=(p,q) := by
  have eqn : N+(v*e)^2=(u*c)^2 := by rw [←product,top,←mid]; ring
  rw [candidate,lift_eq cop eqn,Nat.sqrt_eq',eqn,Nat.sqrt_eq',←mid]
  exact Prod.ext (by simp) (by dsimp; rw [top]; ring)

/-- If d=v*e is below u*v, the least residue itself is the integer square.
The absolute size of the midpoint does not enter this condition. -/
theorem first_pair {p q N u v c e : ℕ} (cop : u.Coprime v)
    (mid : p+v*e=u*c) (top : q=p+2*v*e) (product : p*q=N) (small : e<u) :
    candidate N u v 0=(p,q) := by
  have bound := Nat.pow_lt_pow_left small (by decide : 2≠0)
  simpa only [Nat.div_eq_of_lt bound] using pair_eq cop mid top product

/-- Fixed public choices u=11 and v=7. The first product has half-gap 35.
At the second, the zeroth square remainder is 23 and the next lift is 144. -/
theorem controls :
    residue 37979 11 7=25 ∧ candidate 37979 11 7 0=(163,233) ∧
    residue 536113 11 7=23 ∧ lift 536113 11 7 1=144 ∧
    4^2<residue 536113 11 7 ∧ residue 536113 11 7<5^2 ∧
    candidate 536113 11 7 1=(653,821) ∧
    Nat.Prime 163 ∧ Nat.Prime 233 ∧ Nat.Prime 653 ∧ Nat.Prime 821 := by
  have r₁ : residue 37979 11 7=25 := residue_eq (c:=18) (e:=5) (by decide) (by decide)
  have r₂ : residue 536113 11 7=23 := residue_eq (c:=67) (e:=12) (by decide) (by decide)
  refine ⟨r₁,first_pair (c:=18) (e:=5) (by decide) (by decide) (by decide)
      (by decide) (by decide),r₂,?_,?_,?_,?_,by norm_num,by norm_num,by norm_num,by norm_num⟩
  · rw [lift,r₂]
    decide
  · rw [r₂]
    decide
  · rw [r₂]
    decide
  · exact pair_eq (c:=67) (e:=12) (by decide) (by decide) (by decide) (by decide)

end PrimeFactors.SumGapDivisorReadout
