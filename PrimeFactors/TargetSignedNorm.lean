import PrimeFactors.TargetNormMultiplier
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Squarefree

/-! Necessary multiplier, target-prime and mod-16 tests before searching for
a primitive signed norm X² − k N Y² = D T². -/
namespace PrimeFactors.TargetSignedNorm

/-- A prime of valuation one in the coefficient of Y² cannot divide T.
The signed target and all three coordinates are arbitrary integers. -/
theorem denominator_unit {A p : ℕ} {X Y T D : ℤ} (hp : p.Prime)
    (norm : X^2-(A:ℤ)*Y^2=D*T^2) (primitive : IsCoprime X Y)
    (divides : p ∣ A) (once : ¬p^2 ∣ A) : ¬(p:ℤ) ∣ T := by
  intro ht
  have prime := Nat.prime_iff_prime_int.mp hp
  have pa : (p:ℤ) ∣ A := by exact_mod_cast divides
  have hx : (p:ℤ) ∣ X := prime.dvd_of_dvd_pow (show (p:ℤ) ∣ X^2 by
    rw [sub_eq_iff_eq_add.mp norm]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_pow ht (by decide : 2≠0)) D)
      (dvd_mul_of_dvd_left pa (Y^2)))
  have hy : ¬(p:ℤ) ∣ Y := fun h => prime.not_unit (primitive.isUnit_of_dvd' hx h)
  have left : (p:ℤ)^2 ∣ (A:ℤ)*Y^2 := by
    have diff := dvd_sub (pow_dvd_pow_of_dvd hx 2)
      (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ht 2) D)
    rwa [show X^2-D*T^2=(A:ℤ)*Y^2 by linarith only [norm]] at diff
  obtain ⟨j,hj⟩ := divides
  have small : (p:ℤ) ∣ (j:ℤ)*Y^2 := (mul_dvd_mul_iff_left prime.ne_zero).mp (by
    simpa only [hj,Nat.cast_mul,pow_two,mul_assoc] using left)
  have pj := (prime.dvd_mul.mp small).resolve_right fun sq => hy (prime.dvd_of_dvd_pow sq)
  obtain ⟨u,hu⟩ := Int.natCast_dvd_natCast.mp pj
  exact once ⟨u, by rw [hj,hu,pow_two,mul_assoc]⟩

private theorem once_product {k N p : ℕ} (hp : p.Prime) (once : ¬p^2 ∣ k)
    (miss : ¬p ∣ N) : ¬p^2 ∣ k*N :=
  fun h => once (((hp.coprime_iff_not_dvd.mpr miss).pow_left 2).dvd_of_dvd_mul_right h)

/-- At a prime dividing k once and missing N the signed D is a square. -/
theorem multiplier_square {k N p : ℕ} [hp : Fact p.Prime] {X Y T D : ℤ}
    (norm : X^2-(k*N:ℕ)*Y^2=D*T^2) (primitive : IsCoprime X Y)
    (divides : p ∣ k) (once : ¬p^2 ∣ k) (miss : ¬p ∣ N) : IsSquare (D:ZMod p) := by
  have tn : (T:ZMod p) ≠ 0 := fun h => denominator_unit hp.out norm primitive
    (divides.mul_right N) (once_product hp.out once miss) ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp h)
  have modNorm := congrArg (fun z : ℤ => (z:ZMod p)) norm
  push_cast at modNorm
  rw [(ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr divides,zero_mul,zero_mul,sub_zero] at modNorm
  apply (isSquare_iff_exists_sq _).mpr
  exact ⟨(X:ZMod p)/T, by rw [div_pow,modNorm,mul_div_cancel_right₀ _ (pow_ne_zero _ tn)]⟩

theorem multiplier_sign {k N p : ℕ} [Fact p.Prime] {X Y T D : ℤ}
    (norm : X^2-(k*N:ℕ)*Y^2=D*T^2) (primitive : IsCoprime X Y)
    (divides : p ∣ k) (once : ¬p^2 ∣ k) (miss : ¬p ∣ N) (unit : ¬(p:ℤ) ∣ D) :
    legendreSym p D = 1 :=
  (legendreSym.eq_one_iff p (fun h => unit ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp h))).mpr
    (multiplier_square norm primitive divides once miss)

/-- Every divisor of |D| admits a square root of kN, including |D| itself. -/
theorem target_square {k N m : ℕ} {X Y T D : ℤ}
    (norm : X^2-(k*N:ℕ)*Y^2=D*T^2) (primitive : IsCoprime X Y) (divides : m ∣ D.natAbs) :
    IsSquare ((k*N : ℕ) : ZMod m) := by
  obtain ⟨r,h,_⟩ := WeightedMultiplierPell.primitive_class norm primitive.symm
  have lift := (dvd_mul_of_dvd_left (Int.natCast_dvd.mpr divides) (T^2)).trans h
  have modRoot := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr lift
  push_cast at modRoot
  apply (isSquare_iff_exists_sq _).mpr
  exact ⟨(r:ZMod m),by push_cast; exact (sub_eq_zero.mp modRoot).symm⟩

theorem target_sign {k N p : ℕ} [Fact p.Prime] {X Y T D : ℤ}
    (norm : X^2-(k*N:ℕ)*Y^2=D*T^2) (primitive : IsCoprime X Y)
    (divides : p ∣ D.natAbs) (unit : ¬p ∣ k*N) : legendreSym p (↑(k*N:ℕ) : ℤ)=1 :=
  (legendreSym.eq_one_iff' p (fun h => unit ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h))).mpr
    (target_square norm primitive divides)

/-- Use the original primitive mod-16 table on the signed residue D mod 16. -/
theorem primitive_pass16 {k N : ℕ} {X Y T D : ℤ}
    (norm : X^2-(k*N:ℕ)*Y^2=D*T^2) (primitive : IsCoprime X Y) :
    TargetNormMultiplier.pass16 ((k*N:ℕ):ZMod 16) (D:ZMod 16) := by
  apply (TargetNormMultiplier.pass16_iff ..).mpr
  refine ⟨X,Y,T,?_,?_⟩
  · have parity (x : ℤ) (even : (x:ZMod 16).val%2≠1) : (2:ℤ) ∣ x := by
      have v := ZMod.val_intCast (n:=16) x
      exact Int.dvd_of_emod_eq_zero (by omega)
    by_contra! even
    exact (Nat.prime_iff_prime_int.mp Nat.prime_two).not_unit
      (primitive.isUnit_of_dvd' (parity X even.1) (parity Y even.2))
  · have h := congrArg (fun z : ℤ => (z:ZMod 16)) (sub_eq_iff_eq_add.mp norm)
    push_cast at h ⊢
    rw [h,add_comm]

/-- A hit whose denominator is invertible yields the actual public square root X/T. -/
theorem readout {k N : ℕ} {X Y T D : ℤ} (norm : X^2-(k*N:ℕ)*Y^2=D*T^2)
    (unit : IsUnit (T:ZMod N)) : ((X:ZMod N)*(T:ZMod N)⁻¹)^2 = (D:ZMod N) := by
  have h := congrArg (fun z : ℤ => (z:ZMod N)) norm
  push_cast at h
  rw [ZMod.natCast_self,mul_zero,zero_mul,sub_zero] at h
  rw [mul_pow,h,mul_assoc,← mul_pow,ZMod.mul_inv_of_unit _ unit,one_pow,mul_one]

/-- For squarefree N coprime to k the primitive norm forces T to be invertible.
This includes every product of distinct primes. -/
theorem denominator_coprime {k N : ℕ} {X Y T D : ℤ}
    (norm : X^2-(k*N:ℕ)*Y^2=D*T^2) (primitive : IsCoprime X Y)
    (sqfree : Squarefree N) (cop : k.Coprime N) : T.natAbs.Coprime N := by
  apply Nat.coprime_of_dvd
  intro p hp ht pn
  have pk := hp.coprime_iff_not_dvd.mp (cop.symm.coprime_dvd_left pn)
  have once : ¬p^2 ∣ N := by simpa [pow_two] using Nat.squarefree_iff_prime_squarefree.mp sqfree p hp
  have absent := once_product hp once pk
  rw [Nat.mul_comm] at absent
  exact denominator_unit hp norm primitive (dvd_mul_of_dvd_right pn k) absent (Int.natCast_dvd.mpr ht)

/-- The readout requires no extra denominator assumption on a primitive
row for a squarefree modulus coprime to the multiplier. -/
theorem readout_of_squarefree {k N : ℕ} {X Y T D : ℤ}
    (norm : X^2-(k*N:ℕ)*Y^2=D*T^2) (primitive : IsCoprime X Y)
    (sqfree : Squarefree N) (cop : k.Coprime N) : ((X:ZMod N)*(T:ZMod N)⁻¹)^2 = (D:ZMod N) := by
  have c : IsCoprime T (N:ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr
    (by simpa only [Int.gcd,Int.natAbs_natCast] using denominator_coprime norm primitive sqfree cop)
  apply readout norm
  apply isCoprime_zero_right.mp
  simpa using c.map (Int.castRingHom (ZMod N))

end PrimeFactors.TargetSignedNorm
