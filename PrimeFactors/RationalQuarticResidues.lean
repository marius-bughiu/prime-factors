import PrimeFactors.PrimePower
import Mathlib.Data.Nat.Factorization.Induction

/-! A rational representation of N by x⁴+4y⁴ gives representations at every
modulus coprime to its denominator. Extra witnesses over the denominator
primes suffice to cover every positive modulus. -/
namespace PrimeFactors.RationalQuarticResidues

open private PrimeFactors.lift_unit_square_root from PrimeFactors.PrimePower

def Rep (N m : ℕ) : Prop := ∃ x y : ZMod m, x^4+4*y^4=(N : ZMod m)

/-- A common denominator invertible modulo m can be cleared in either direction. -/
theorem invert_denominator {N d a b m : ℕ} (eq : d^4*N=a^4+4*b^4) (cop : d.Coprime m) :
    Rep N m := by
  let u := ZMod.unitOfCoprime d cop
  have val : (u : ZMod m)=(d:ZMod m) := ZMod.coe_unitOfCoprime ..
  have shape : (d:ZMod m)^4*N=(a:ZMod m)^4+4*(b:ZMod m)^4 := by
    exact_mod_cast congrArg (fun n : ℕ => (n:ZMod m)) eq
  let z : ZMod m := ↑u⁻¹
  have cancel : (d:ZMod m)*z=1 := by rw [←val]; exact u.mul_inv
  refine ⟨a*z,b*z,?_⟩
  calc
    _ = ((a:ZMod m)^4+4*(b:ZMod m)^4)*z^4 := by ring
    _ = N*((d:ZMod m)*z)^4 := by rw [←shape]; ring
    _ = _ := by rw [cancel]; simp

theorem crt {N a b : ℕ} (cop : a.Coprime b) (a_ok : Rep N a) (b_ok : Rep N b) : Rep N (a*b) := by
  obtain ⟨x,y,left⟩ := a_ok
  obtain ⟨u,v,right⟩ := b_ok
  let cr := ZMod.chineseRemainder cop
  refine ⟨cr.symm (x,u),cr.symm (y,v),cr.injective ?_⟩
  rw [map_add,map_mul,map_pow,map_pow,map_ofNat,map_natCast,cr.apply_symm_apply,cr.apply_symm_apply]
  exact Prod.ext left right

/-- Only the primes dividing the supplied rational denominator need a separate
representation at each power. CRT then supplies both coordinates modulo m. -/
theorem all_moduli {N d a b : ℕ} (eq : d^4*N=a^4+4*b^4)
    (at_denominator : ∀ p : ℕ, p.Prime → p∣d → ∀ e : ℕ, Rep N (p^e)) (m : ℕ) :
    0<m → Rep N m := by
  induction m using Nat.recOnPrimeCoprime with
  | h0 => omega
  | hp p e prime =>
    intro _
    by_cases hit : p∣d
    · exact at_denominator p prime hit e
    · exact invert_denominator eq ((prime.coprime_iff_not_dvd.mpr hit).symm.pow_right e)
  | h a b ha hb cop left right => exact fun _ => crt cop (left (by omega)) (right (by omega))

/-- Lift a nonzero fourth root at an odd prime by lifting two square roots.
The first square root is chosen to retain the square of the seed residue. -/
theorem fourth_unit_lifts {p : ℕ} [Fact p.Prime] (odd : p≠2) (D r : ℤ)
    (unit : (r:ZMod p)≠0) (seed : (r:ZMod p)^4=(D:ZMod p)) (e : ℕ) :
    ∃ z : ZMod (p^e), z^4=(D:ZMod (p^e)) := by
  cases e with
  | zero => rw [pow_zero]; exact ⟨0,Subsingleton.elim ..⟩
  | succ k =>
    have base : (p:ℤ)∣D-(r^2)^2 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [←seed]
      ring
    have nonzero : ((r^2:ℤ):ZMod p)≠0 := by simpa only [Int.cast_pow] using pow_ne_zero 2 unit
    obtain ⟨w,at_p,divides⟩ := PrimeFactors.lift_unit_square_root odd nonzero base k
    rw [Int.cast_pow] at at_p
    have w_square : IsSquare (w:ZMod p) := ⟨r,by simpa only [pow_two] using at_p⟩
    obtain ⟨z,hz⟩ := (isSquare_primePow_iff_of_unit odd w (at_p ▸ pow_ne_zero 2 unit) k).mpr w_square
    have rd := (ZMod.intCast_zmod_eq_zero_iff_dvd (D-w^2) (p^(k+1))).mpr (by exact_mod_cast divides)
    push_cast at rd
    refine ⟨z,?_⟩
    calc
      z^4 = (z*z)^2 := by ring
      _ = (w:ZMod (p^(k+1)))^2 := by rw [←hz]
      _ = _ := (sub_eq_zero.mp rd).symm

private theorem unscale_two {m : ℕ} (cop : Nat.Coprime 2 m) {D z : ZMod m} (hz : z^4=4*D) :
    ∃ y : ZMod m, 4*y^4=D := by
  let u := ZMod.unitOfCoprime 2 cop
  let y : ZMod m := z*↑u⁻¹
  have two : (u:ZMod m)=2 := ZMod.coe_unitOfCoprime ..
  have cancel : (2:ZMod m)*y=z := by
    change (2:ZMod m)*(z*↑u⁻¹)=z
    rw [mul_left_comm,←two,Units.mul_inv,mul_one]
  have four : IsUnit (4 : ZMod m) := by
    have hu := u.isUnit.mul u.isUnit
    rw [two] at hu
    simpa only [show (2:ZMod m)*2=4 by norm_num] using hu
  refine ⟨y,four.mul_left_cancel ?_⟩
  calc
    (4:ZMod m)*(4*y^4) = (2*y)^4 := by ring
    _ = 4*D := by rw [cancel,hz]

/-- A single nonsingular solution modulo an odd prime supplies a solution at
all powers. Either coordinate may supply the nonzero partial derivative. -/
theorem smooth_lift {p N : ℕ} (prime : p.Prime) (odd : p≠2) (x y : ZMod p)
    (shape : x^4+4*y^4=(N:ZMod p)) (smooth : x≠0 ∨ y≠0) (e : ℕ) : Rep N (p^e) := by
  letI : Fact p.Prime := ⟨prime⟩
  obtain ⟨a,rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨b,rfl⟩ := ZMod.intCast_surjective y
  rcases smooth with left|right
  · let D : ℤ := N-4*b^4
    have seed : (a:ZMod p)^4=(D:ZMod p) := by dsimp [D]; push_cast; linear_combination shape
    obtain ⟨z,hz⟩ := fourth_unit_lifts odd D a left seed e
    refine ⟨z,b,?_⟩
    dsimp [D] at hz; push_cast at hz; linear_combination hz
  · let D : ℤ := N-a^4
    have two : (2:ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    have unit : ((2*b:ℤ):ZMod p)≠0 := by push_cast; exact mul_ne_zero two right
    have seed : ((2*b:ℤ):ZMod p)^4=((4*D:ℤ):ZMod p) := by
      dsimp [D]; push_cast; linear_combination 4*shape
    obtain ⟨z,hz⟩ := fourth_unit_lifts odd (4*D) (2*b) unit seed e
    rw [Int.cast_mul,Int.cast_ofNat] at hz
    have cop : Nat.Coprime 2 (p^e) := ((Nat.coprime_primes Nat.prime_two prime).mpr odd.symm).pow_right _
    obtain ⟨w,hw⟩ := unscale_two cop hz
    refine ⟨a,w,?_⟩
    dsimp [D] at hw; push_cast at hw; linear_combination hw

/-- Even exponents permit independent sign changes in the two coordinates. -/
theorem integer_iff_natural (N : ℕ) : (∃ x y : ℤ, x^4+4*y^4=N) ↔ ∃ x y : ℕ, x^4+4*y^4=N := by
  constructor
  · rintro ⟨x,y,h⟩
    have absolute (z : ℤ) : (z.natAbs:ℤ)^4=z^4 := by
      calc
        _ = ((z.natAbs:ℤ)^2)^2 := by ring
        _ = _ := by rw [Int.natAbs_sq]; ring
    refine ⟨x.natAbs,y.natAbs,?_⟩
    exact_mod_cast (show (x.natAbs:ℤ)^4+4*(y.natAbs:ℤ)^4=N by rw [absolute,absolute]; exact h)
  · rintro ⟨x,y,h⟩
    exact ⟨x,y,by exact_mod_cast h⟩

/-- All congruence tests accept this rational value, while even allowing zero
for either coordinate produces no ordinary natural-number representation. -/
theorem counterexample :
    (5:ℕ)^4*22789=59^4+4*27^4 ∧ (∀ m>0, Rep 22789 m) ∧
    ¬∃ x y : ℕ, x^4+4*y^4=22789 := by
  have identity : (5:ℕ)^4*22789=59^4+4*27^4 := by decide +kernel
  refine ⟨identity,all_moduli identity (fun p pp hd e => ?_),?_⟩
  · have eq := (Nat.prime_dvd_prime_iff_eq pp Nat.prime_five).mp hd
    subst p
    exact smooth_lift Nat.prime_five (by decide) 0 1 (by decide +kernel) (Or.inr (by decide)) e
  · rintro ⟨x,y,eq⟩
    have xl : x<13 := by
      by_contra! big
      have := Nat.pow_le_pow_left big 4
      norm_num at this
      omega
    have yl : y<9 := by
      by_contra! big
      have := Nat.pow_le_pow_left big 4
      norm_num at this
      omega
    exact (by decide +kernel : ∀ a : Fin 13, ∀ b : Fin 9, a.val^4+4*b.val^4≠22789) ⟨x,xl⟩ ⟨y,yl⟩ eq

theorem no_integer_point : ¬∃ x y : ℤ, x^4+4*y^4=22789 :=
  (integer_iff_natural 22789).not.mpr counterexample.2.2

end PrimeFactors.RationalQuarticResidues
