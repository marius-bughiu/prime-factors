import PrimeFactors.RationalQuarticResidues
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-! Odd local tests for the cleared quartic equation a⁴+4b⁴=N d⁴.
The denominator is a positive natural number. At primes congruent to one
modulo four the construction permits the denominator to be divisible by the
prime. Numerator primitivity is checked modulo the prime, at every depth. -/
namespace PrimeFactors.QuarticOddLocalPoints

def Local (N p e : ℕ) : Prop := ∃ a b d : ℕ, 0<d ∧ (¬p∣a ∨ ¬p∣b) ∧
    a^4+4*b^4 ≡ N*d^4 [MOD p^e]

private theorem equation_iff (N a b d m : ℕ) :
    a^4+4*b^4 ≡ N*d^4 [MOD m] ↔ (a:ZMod m)^4+4*(b:ZMod m)^4=(N:ZMod m)*(d:ZMod m)^4 := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rfl

/-- A root of -1 supplies a nonsingular fourth root of -4. The same positive
denominator p and the same unit numerator b=1 work at every depth. -/
theorem split_points {p : ℕ} (prime : p.Prime) (split : p%4=1) (N e : ℕ) :
    ∃ a : ℕ, a^4+4*1^4 ≡ N*p^4 [MOD p^e] := by
  letI : Fact p.Prime := ⟨prime⟩
  have odd : p≠2 := by omega
  have two : (2:ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨i,hi⟩ := (isSquare_iff_exists_sq (-1:ZMod p)).mp (ZMod.exists_sq_eq_neg_one_iff.mpr (by omega))
  have hneg : (1+i)^4=-(4:ZMod p) := calc
    (1+i)^4 = ((1+i)^2)^2 := by ring
    _ = (2*i)^2 := by
      have h : (1+i)^2=2*i := by linear_combination -hi
      rw [h]
    _ = -4 := by linear_combination -4*hi
  have four : (4:ZMod p)≠0 := by simpa only [show (2:ZMod p)^2=4 by ring] using pow_ne_zero 2 two
  have unit : 1+i≠0 := by intro z; simp [z] at hneg; exact four hneg
  let D : ℤ := (N:ℤ)*p^4-4
  obtain ⟨r,hr⟩ := ZMod.intCast_surjective (1+i)
  have seed : (r:ZMod p)^4=(D:ZMod p) := by simpa [hr,D] using hneg
  obtain ⟨z,hz⟩ := RationalQuarticResidues.fourth_unit_lifts odd D r (hr ▸ unit) seed e
  letI : NeZero (p^e) := ⟨pow_ne_zero _ prime.ne_zero⟩
  refine ⟨z.val,(equation_iff N z.val 1 p _).mpr ?_⟩
  simp only [ZMod.natCast_zmod_val,Nat.cast_one,one_pow,mul_one]
  dsimp [D] at hz
  push_cast at hz
  linear_combination hz

private theorem square_as_fourth {p : ℕ} [Fact p.Prime] (inert : p%4=3) (a : ZMod p) :
    (a^((p+1)/4))^4=a^2 := by
  rw [←pow_mul,show (p+1)/4*4=p+1 by omega,pow_succ,ZMod.pow_card,pow_two]

/-- At an inert odd prime every residue is a fourth power plus four times a
fourth power. This statement includes zero at depth one. -/
theorem inert_seed {p : ℕ} (prime : p.Prime) (inert : p%4=3) (n : ZMod p) :
    ∃ x y : ZMod p, x^4+4*y^4=n := by
  letI : Fact p.Prime := ⟨prime⟩
  have odd : p≠2 := by omega
  have two : (2:ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨r,s,shape⟩ := ZMod.sq_add_sq p n
  refine ⟨r^((p+1)/4),(s/2)^((p+1)/4),?_⟩
  rw [square_as_fourth inert,square_as_fourth inert,←shape]
  congr 1
  field_simp [two]
  ring

/-- In the inert case an input unit lifts with the fixed denominator one.
The two natural representatives cannot both vanish modulo p. -/
theorem inert_units {N p : ℕ} (prime : p.Prime) (inert : p%4=3) (unit : ¬p∣N) (e : ℕ) :
    ∃ a b : ℕ, (¬p∣a ∨ ¬p∣b) ∧ a^4+4*b^4 ≡ N*1^4 [MOD p^e] := by
  by_cases zero : e=0
  · subst e
    exact ⟨1,0,Or.inl prime.not_dvd_one,by simp [Nat.ModEq,Nat.mod_one]⟩
  letI : Fact p.Prime := ⟨prime⟩
  letI : NeZero (p^e) := ⟨pow_ne_zero _ prime.ne_zero⟩
  have nonzero := (ZMod.natCast_zmod_eq_zero_iff_dvd N p).mp.mt unit
  obtain ⟨x,y,h⟩ := inert_seed prime inert (N:ZMod p)
  have smooth : x≠0 ∨ y≠0 := by
    by_cases hx : x=0
    · exact Or.inr (fun hy => nonzero (by simpa [hx,hy] using h.symm))
    · exact Or.inl hx
  obtain ⟨z,w,hw⟩ := RationalQuarticResidues.smooth_lift prime (by omega) x y h smooth e
  have top : z.val^4+4*w.val^4 ≡ N*1^4 [MOD p^e] := (equation_iff ..).mpr (by simpa using hw)
  refine ⟨z.val,w.val,?_,top⟩
  by_cases left : p∣z.val
  · refine Or.inr (fun right => nonzero ?_)
    have base := (equation_iff ..).mp (top.of_dvd (dvd_pow_self p zero))
    have l := (ZMod.natCast_zmod_eq_zero_iff_dvd z.val p).mpr left
    have r := (ZMod.natCast_zmod_eq_zero_iff_dvd w.val p).mpr right
    simpa only [l,r,zero_pow (by decide : 4≠0),mul_zero,add_zero,Nat.cast_one,one_pow,mul_one] using base.symm
  · exact Or.inl left

/-- If an inert prime divides N, both numerator coordinates vanish modulo
that prime for every denominator. -/
theorem inert_coordinates {p N a b d : ℕ} (prime : p.Prime) (inert : p%4=3) (div : p∣N)
    (point : a^4+4*b^4 ≡ N*d^4 [MOD p]) : p∣a ∧ p∣b := by
  letI : Fact p.Prime := ⟨prime⟩
  have odd : p≠2 := by omega
  have two : (2:ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have eq := (equation_iff ..).mp point
  rw [(ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr div,zero_mul] at eq
  have neg : ((a:ZMod p)^2)^2=-(2*(b:ZMod p)^2)^2 := by linear_combination eq
  have bz : (b:ZMod p)=0 := by
    by_contra nz
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (mul_ne_zero two (pow_ne_zero 2 nz)) neg inert
  have az : (a:ZMod p)=0 := by simpa [bz] using eq
  exact ⟨(ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp az,(ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp bz⟩

/-- If p divides N exactly once, even the denominator must vanish modulo p
in every solution modulo p². Thus no projectively primitive triple exists. -/
theorem inert_all_three {p N a b d : ℕ} (prime : p.Prime) (inert : p%4=3)
    (div : p∣N) (once : ¬p^2∣N) (point : a^4+4*b^4 ≡ N*d^4 [MOD p^2]) : p∣a ∧ p∣b ∧ p∣d := by
  obtain ⟨da,db⟩ := inert_coordinates prime inert div (point.of_dvd (dvd_pow_self p (by decide : 2≠0)))
  have lift {z : ℕ} (dvd : p∣z) : p^2∣z^4 :=
    (pow_dvd_pow_of_dvd dvd 2).trans (pow_dvd_pow z (by decide : 2≤4))
  have van := dvd_add (lift da) (dvd_mul_of_dvd_right (lift db) 4)
  have prod := Nat.modEq_zero_iff_dvd.mp (point.symm.trans (Nat.modEq_zero_iff_dvd.mpr van))
  refine ⟨da,db,?_⟩
  by_contra nd
  have cop := ((prime.coprime_iff_not_dvd.mpr nd).pow_left 2).pow_right 4
  exact once (cop.dvd_of_dvd_mul_right prod)

theorem all_iff {p N : ℕ} (prime : p.Prime) (odd : p≠2) :
    (∀ e : ℕ, Local N p e) ↔ p%4=1 ∨ ¬p∣N := by
  constructor
  · intro h
    by_contra! bad
    have inert : p%4=3 := by have := prime.eq_two_or_odd.resolve_left odd; omega
    obtain ⟨a,b,d,_,primitive,point⟩ := h 1
    rw [pow_one] at point
    obtain ⟨da,db⟩ := inert_coordinates prime inert bad.2 point
    exact primitive.elim (· da) (· db)
  · intro h e
    by_cases split : p%4=1
    · obtain ⟨a,point⟩ := split_points prime split N e
      exact ⟨a,1,p,prime.pos,Or.inr prime.not_dvd_one,point⟩
    · have inert : p%4=3 := by have := prime.eq_two_or_odd.resolve_left odd; omega
      obtain ⟨a,b,prim,point⟩ := inert_units prime inert (h.resolve_left split) e
      exact ⟨a,b,1,by decide,prim,point⟩

end PrimeFactors.QuarticOddLocalPoints
