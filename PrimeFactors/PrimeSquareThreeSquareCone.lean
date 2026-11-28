import PrimeFactors.ThreeSquareCone
import PrimeFactors.PrimePowerCount

/-! Lifts of ternary sums of squares from an odd prime to its square.
A nonzero point has two free digits; at the zero target every lift of
the origin is a point. -/
namespace PrimeFactors.PrimeSquareThreeSquareCone

open Finset ThreeSquareCone
open private PrimeFactors.digit_card from PrimeFactors.PrimePowerCount

variable {p : ℕ} [Fact p.Prime]
private abbrev R (p : ℕ) := ZMod (p^2)
private noncomputable abbrev red (p : ℕ) := firstPrimeDigit p 1
private abbrev Digit (x : ZMod p) := {a : R p // red p a=x}

/-- All lifts of a prescribed residue triple that represent t. Each coordinate
in this subtype already has its specified residue modulo p. -/
abbrev Fiber (w : ZMod p × ZMod p × ZMod p) (t : ZMod (p^2)) :=
  {u : Digit w.1 × Digit w.2.1 × Digit w.2.2 //
    u.1.val^2+u.2.1.val^2+u.2.2.val^2=t}

private theorem digit_count (x : ZMod p) : Nat.card (Digit x)=p := by
  simpa using PrimeFactors.digit_card 1 x

private noncomputable def squareDigit (odd : p≠2) {c : ZMod p} (nz : c≠0) :
    Digit c ≃ Digit (c^2) :=
  (discriminantDigitEquiv odd 1 0 nz).trans (Equiv.subtypeEquivRight (fun _ => by simp))

private theorem square_val (odd : p≠2) {c : ZMod p} (nz : c≠0) (z : Digit c) :
    ((squareDigit odd nz) z).val=z.val^2 := by
  change z.val^2-4*0=z.val^2
  ring

private theorem last_regular (odd : p≠2) {x y z : ZMod p} {t : R p}
    (eq : x^2+y^2+z^2=red p t) (nz : z≠0) :
    Nat.card (Fiber (x,y,z) t)=p^2 := by
  let e := squareDigit odd nz
  let drop (v : Fiber (x,y,z) t) : Digit x × Digit y := (v.val.1,v.val.2.1)
  have bij : Function.Bijective drop := by
    constructor
    · rintro ⟨⟨a,b,c⟩,h⟩ ⟨⟨a',b',c'⟩,h'⟩ same
      change (a,b)=(a',b') at same
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
      have csq : c.val^2=c'.val^2 := by
        change a.val^2+b.val^2+c.val^2=t at h
        change a.val^2+b.val^2+c'.val^2=t at h'
        linear_combination h-h'
      have ce : c=c' := e.injective (Subtype.ext (by simpa only [e,square_val] using csq))
      subst c'
      rfl
    · rintro ⟨a,b⟩
      let target : Digit (z^2) := ⟨t-a.val^2-b.val^2, by
        rw [map_sub,map_sub,map_pow,map_pow,a.property,b.property,←eq]
        ring⟩
      let c := e.symm target
      have hc := congrArg Subtype.val (e.apply_symm_apply target)
      change ((squareDigit odd nz) c).val= t-a.val^2-b.val^2 at hc
      rw [square_val] at hc
      exact ⟨⟨(a,b,c),by change a.val^2+b.val^2+c.val^2=t; linear_combination hc⟩,rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective drop bij),Nat.card_prod,digit_count,digit_count,pow_two]

private def rotate (x y z : ZMod p) (t : R p) : Fiber (x,y,z) t ≃ Fiber (y,z,x) t where
  toFun u := ⟨(u.val.2.1,u.val.2.2,u.val.1),by
    have h := u.property
    change u.val.1.val^2+u.val.2.1.val^2+u.val.2.2.val^2=t at h
    change u.val.2.1.val^2+u.val.2.2.val^2+u.val.1.val^2=t
    linear_combination h⟩
  invFun u := ⟨(u.val.2.2,u.val.1,u.val.2.1),by
    have h := u.property
    change u.val.1.val^2+u.val.2.1.val^2+u.val.2.2.val^2=t at h
    change u.val.2.2.val^2+u.val.1.val^2+u.val.2.1.val^2=t
    linear_combination h⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- At every regular point, fixing the higher digits of two coordinates
uniquely determines the other one. This works for any lift of the target. -/
theorem regular_lifts (odd : p≠2) {w : ZMod p × ZMod p × ZMod p} {t : R p}
    (on : w∈points (ZMod p) (red p t)) (nz : w≠(0,0,0)) :
    Nat.card (Fiber w t)=p^2 := by
  obtain ⟨x,y,z⟩ := w
  have eq : x^2+y^2+z^2=red p t := mem_points.mp on
  by_cases z0 : z=0
  · by_cases x0 : x=0
    · have yn : y≠0 := by rintro rfl; simp [x0,z0] at nz
      rw [Nat.card_congr (rotate x y z t),Nat.card_congr (rotate y z x t)]
      exact last_regular odd (by linear_combination eq) yn
    · rw [Nat.card_congr (rotate x y z t)]
      exact last_regular odd (by linear_combination eq) x0
  · exact last_regular odd eq z0

private theorem zero_square (a : Digit (0:ZMod p)) : a.val^2=0 := by
  have h := a.property
  obtain ⟨v,hv⟩ := ZMod.natCast_zmod_surjective a.val
  rw [←hv, map_natCast] at h
  obtain ⟨b,hb⟩ := (ZMod.natCast_zmod_eq_zero_iff_dvd v p).mp h
  rw [←hv, hb, ←Nat.cast_pow, mul_pow]
  exact (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr (dvd_mul_right ..)

/-- Every one of the p³ lifts of the zero triple represents zero modulo p². -/
theorem origin_lifts (p : ℕ) [Fact p.Prime] :
    Nat.card (Fiber (p:=p) (0,0,0) 0)=p^3 := by
  have all (u : Digit (0:ZMod p) × Digit (0:ZMod p) × Digit (0:ZMod p)) :
      u.1.val^2+u.2.1.val^2+u.2.2.val^2=0 := by simp [zero_square]
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv all),Nat.card_prod,Nat.card_prod,
    digit_count]
  ring

private noncomputable def reduce (v : R p × R p × R p) : ZMod p × ZMod p × ZMod p :=
  (red p v.1,red p v.2.1,red p v.2.2)

private noncomputable def allLifts (t : R p) :
    (Σ w : ↥(points (ZMod p) (red p t)), Fiber w.val t) ≃ ↥(points (R p) t) where
  toFun v := ⟨(v.2.val.1.val,v.2.val.2.1.val,v.2.val.2.2.val),
    mem_points.mpr v.2.property⟩
  invFun v := ⟨⟨reduce v.val,mem_points.mpr (by
      change (red p v.val.1)^2+(red p v.val.2.1)^2+(red p v.val.2.2)^2=red p t
      simpa only [map_add,map_pow] using congrArg (red p) (mem_points.mp v.property))⟩,
    ⟨(⟨v.val.1,rfl⟩,⟨v.val.2.1,rfl⟩,⟨v.val.2.2,rfl⟩),mem_points.mp v.property⟩⟩
  left_inv := by
    rintro ⟨⟨⟨x,y,z⟩,w⟩,⟨⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩⟩,h⟩⟩
    change red p a=x at ha
    change red p b=y at hb
    change red p c=z at hc
    subst x; subst y; subst z
    rfl
  right_inv _ := rfl

/-- The all-zero target has a singular contribution of p³ and
p² lifts at each of the p²−1 other points over the prime field. -/
theorem prime_square (p : ℕ) [Fact p.Prime] (odd : p≠2) :
    (points (ZMod (p^2)) 0).card=(p^2-1)*p^2+p^3 := by
  classical
  let S := points (ZMod p) (red p 0)
  let O : ↥S := ⟨(0,0,0),by simp [S]⟩
  rw [←Nat.card_eq_finsetCard,←Nat.card_congr (allLifts (p:=p) 0),Nat.card_sigma]
  change (∑ w : ↥S, Nat.card (Fiber w.val 0))=_
  rw [←sum_erase_add _ _ (mem_univ O)]
  have origin : Nat.card (Fiber O.val 0)=p^3 := origin_lifts p
  have other : ∀ w∈(univ.erase O), Nat.card (Fiber w.val 0)=p^2 := by
    intro w hw
    exact regular_lifts odd w.property (fun h => (mem_erase.mp hw).1 (Subtype.ext h))
  rw [origin,sum_congr rfl other,sum_const,card_erase_of_mem (mem_univ O),card_univ,
    Fintype.card_coe,nsmul_eq_mul]
  simp [S,prime_zero p odd]

/-- Direct enumeration at 3 gives 99 triples modulo 9. -/
theorem three : (points (ZMod 9) 0).card=99 := by decide +kernel

end PrimeFactors.PrimeSquareThreeSquareCone
