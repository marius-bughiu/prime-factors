import PrimeFactors.TargetNormMultiplier
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum.LegendreSymbol

/-! A primitive conic point recovers the requested square root modulo the
whole squarefree input. A multiplier already represented by the quadratic
norm gives an invertible map on rational affine conics. -/
namespace PrimeFactors.TargetNormConic

open TargetNormMultiplier

theorem denominator_coprime {k N D X Y T : ℕ} (sf : Squarefree N) (cop : k.Coprime N)
    (eqn : X^2 = k*N*Y^2 + D*T^2) (primitive : X.Coprime Y) : T.Coprime N := by
  apply Nat.coprime_of_dvd
  intro p hp ht hn
  apply denominator_unit (k:=N) (N:=k) hp (by simpa [Nat.mul_comm k N] using eqn)
    primitive hn _ _ ht
  · simpa [pow_two] using (Nat.squarefree_iff_prime_squarefree.mp sf p hp)
  · exact fun hk => Nat.not_coprime_of_dvd_of_dvd hp.one_lt hk hn cop

/-- Every primitive solution supplies X/T as an actual square root modulo
the possibly composite input N. No factors of N enter the expression. -/
theorem root_from_point {k N D X Y T : ℕ} (sf : Squarefree N) (cop : k.Coprime N)
    (eqn : X^2 = k*N*Y^2 + D*T^2) (primitive : X.Coprime Y) :
    ((X : ZMod N) * (↑(ZMod.unitOfCoprime T (denominator_coprime sf cop eqn primitive))⁻¹ : ZMod N))^2
      = D := by
  let u := ZMod.unitOfCoprime T (denominator_coprime sf cop eqn primitive)
  have hu : (T : ZMod N) = u := (ZMod.coe_unitOfCoprime ..).symm
  have row := congrArg (fun x : ℕ => (x : ZMod N)) eqn
  push_cast at row
  simp only [ZMod.natCast_self, mul_zero, zero_mul, zero_add] at row
  change ((X : ZMod N) * (↑u⁻¹ : ZMod N))^2 = _
  rw [mul_pow, row, hu, mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]

/-- The equation x²−2t²=A, obtained from the original conic by dividing
by Y² at a point with Y nonzero. -/
def Points (A : ℚ) := {v : ℚ × ℚ // v.1^2 - 2*v.2^2 = A}

private theorem norm_mul (x t u v : ℚ) :
    (x*u + 2*t*v)^2 - 2*(x*v + t*u)^2 = (x^2-2*t^2)*(u^2-2*v^2) := by ring

/-- Multiplication by u+v√2 gives a rational bijection from the k=1
points to all k-points. Its inverse uses (u−v√2)/k. -/
noncomputable def change_multiplier {k : ℚ} (N u v : ℚ) (norm : u^2-2*v^2=k) (unit : k≠0) :
    Points N ≃ Points (k*N) where
  toFun z := ⟨(z.1.1*u+2*z.1.2*v, z.1.1*v+z.1.2*u), by
    change (_+_)^2-2*(_+_)^2=_
    rw [norm_mul,z.property,norm,mul_comm]⟩
  invFun z := ⟨((z.1.1*u-2*z.1.2*v)/k, (z.1.2*u-z.1.1*v)/k), by
    change (_/k)^2-2*(_/k)^2=N
    field_simp
    linear_combination k*z.property + (z.1.1^2-2*z.1.2^2)*norm⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      field_simp
      linear_combination z.1.1*norm
    · dsimp
      field_simp
      linear_combination z.1.2*norm
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      field_simp
      linear_combination z.1.1*norm
    · dsimp
      field_simp
      linear_combination z.1.2*norm

/-- For odd inputs the public mod-16 gate is just the two residue classes
1 and 7 modulo 8. -/
theorem odd_gate (A : ℕ) (odd : Odd A) :
    pass16 (A : ZMod 16) 2 ↔ A%8=1 ∨ A%8=7 := by
  have h : ∀ a : ZMod 16, a.val%2=1 → (pass16 a 2 ↔ a.val%8=1 ∨ a.val%8=7) := by
    unfold pass16
    decide +kernel
  simpa only [ZMod.val_natCast,Nat.mod_mod_of_dvd A (by decide : 8∣16)] using
    h (A : ZMod 16) (by simpa only [ZMod.val_natCast,Nat.mod_mod_of_dvd A (by decide : 2∣16)]
                            using Nat.odd_iff.mp odd)

/-- Both readily available signs pass on this balanced input, yet its
prime divisor 19 precludes a primitive point for k=1. -/
theorem public_pass_551 :
    Nat.Prime 19 ∧ Nat.Prime 29 ∧ 19*29=(551:ℕ) ∧ jacobiSym 2 551=1 ∧
    pass16 (551 : ZMod 16) 2 ∧
    ∀ X Y T : ℕ, X.Coprime Y → X^2 ≠ 551*Y^2+2*T^2 := by
  refine ⟨by decide,by decide,by decide,by norm_num,?_,?_⟩
  · exact (odd_gate 551 (by decide)).mpr (by decide)
  · intro X Y T prim eqn
    letI : Fact (Nat.Prime 19) := ⟨by decide⟩
    have sign := multiplier_sign (k:=551) (N:=1) (D:=2) (ell:=19)
      (by simpa only [Nat.mul_one] using eqn) prim (by decide) (by decide) (by decide) (by decide)
    norm_num at sign

end PrimeFactors.TargetNormConic
