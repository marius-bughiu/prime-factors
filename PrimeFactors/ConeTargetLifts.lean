import PrimeFactors.ConeUnitTarget
import PrimeFactors.PrimeSquareThreeSquareCone

/-! How much information remains in the next digits of a three-square target. -/
namespace PrimeFactors.ConeTargetLifts

open Finset ThreeSquareCone PrimeSquareThreeSquareCone
open private PrimeFactors.PrimeSquareThreeSquareCone.allLifts
  PrimeFactors.PrimeSquareThreeSquareCone.zero_square from PrimeFactors.PrimeSquareThreeSquareCone

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

/-- Each point above a nonzero residue has two free higher digits. -/
theorem prime_unit (odd : p≠2) (t : ℤ) (unit : (t : ZMod p)≠0) :
    (points (ZMod (p^2)) t).card=p^2*(points (ZMod p) t).card := by
  classical
  rw [←Nat.card_eq_finsetCard,←Nat.card_congr (PrimeFactors.PrimeSquareThreeSquareCone.allLifts (p:=p) t),
    Nat.card_sigma]
  have h (w : ↥(points (ZMod p) (firstPrimeDigit p 1 (t : ZMod (p^2))))) :
      Nat.card (Fiber w.val (t : ZMod (p^2)))=p^2 := by
    apply regular_lifts odd w.property
    intro zero
    have on := mem_points.mp w.property
    simp [zero] at on
    exact unit on.symm
  simp only [h, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul, map_intCast, Nat.cast_id, mul_comm]

private theorem change_modulus {a b : ℕ} [NeZero a] [NeZero b] (eq : a=b) (t : ℤ) :
    (points (ZMod a) t).card=(points (ZMod b) t).card := by subst b; rfl

/-- For a unit target, every next digit at modulus N² gives the same
count, which is N² times the count already present at modulus N. -/
theorem unit_lift (ne : p≠q) (op : p≠2) (oq : q≠2) (t : ℤ)
    (unit : t.natAbs.Coprime (p*q)) :
    (points (ZMod ((p*q)^2)) t).card=(p*q)^2*(points (ZMod (p*q)) t).card := by
  have co := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr ne
  have nonzero (r : ℕ) [Fact r.Prime] (div : r∣p*q) : (t : ZMod r)≠0 := by
    intro zero
    have divides := (ZMod.intCast_zmod_eq_zero_iff_dvd t r).mp zero
    have hr : r∣t.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr divides
    exact (Fact.out : r.Prime).not_dvd_one (unit ▸ Nat.dvd_gcd hr div)
  rw [change_modulus (mul_pow p q 2),ConeUnitTarget.total_mul_int ((co.pow_left 2).pow_right 2),
    prime_unit op t (nonzero p (dvd_mul_right ..)),prime_unit oq t (nonzero q (dvd_mul_left ..)),
    ConeUnitTarget.total_mul_int co]
  ring

/-- A target divisible by p but nonzero modulo p² has exactly p² lifts
above each nonzero cone point and none above the origin. -/
theorem prime_first_order (odd : p≠2) (t : ℤ) (low : (t:ZMod p)=0)
    (high : (t:ZMod (p^2))≠0) :
    (points (ZMod (p^2)) t).card=(p^2-1)*p^2 := by
  classical
  let S := points (ZMod p) (firstPrimeDigit p 1 (t : ZMod (p^2)))
  let O : ↥S := ⟨(0,0,0),by simp [S,low]⟩
  rw [←Nat.card_eq_finsetCard,←Nat.card_congr (PrimeFactors.PrimeSquareThreeSquareCone.allLifts
    (p:=p) (t : ZMod (p^2))),Nat.card_sigma]
  change (∑ w : ↥S, Nat.card (Fiber w.val (t:ZMod (p^2))))=_
  rw [←sum_erase_add _ _ (mem_univ O)]
  have origin : Nat.card (Fiber O.val (t:ZMod (p^2)))=0 := by
    apply Nat.card_eq_zero.mpr
    apply Or.inl
    refine ⟨fun v => high ?_⟩
    have h := v.property
    change v.val.1.val^2+v.val.2.1.val^2+v.val.2.2.val^2=(t:ZMod (p^2)) at h
    rw [PrimeFactors.PrimeSquareThreeSquareCone.zero_square v.val.1,
      PrimeFactors.PrimeSquareThreeSquareCone.zero_square v.val.2.1,
      PrimeFactors.PrimeSquareThreeSquareCone.zero_square v.val.2.2] at h
    simpa using h.symm
  have regular : ∀ w∈univ.erase O, Nat.card (Fiber w.val (t:ZMod (p^2)))=p^2 := by
    intro w hw
    exact regular_lifts odd w.property (fun z => (mem_erase.mp hw).1 (Subtype.ext z))
  rw [origin,add_zero,sum_congr rfl regular,sum_const,card_erase_of_mem (mem_univ O),
    card_univ,Fintype.card_coe,nsmul_eq_mul]
  simp [S,low,prime_zero p odd]

private theorem vanishes_once {r s : ℕ} [Fact r.Prime] (cop : r.Coprime s)
    (u : ℤ) (unit : u.natAbs.Coprime (r*s)) :
    (((r:ℤ)*s*u:ℤ):ZMod r)=0 ∧ (((r:ℤ)*s*u:ℤ):ZMod (r^2))≠0 := by
  constructor
  · simp
  · intro zero
    have raw := (ZMod.intCast_zmod_eq_zero_iff_dvd ((r:ℤ)*s*u) (r^2)).mp zero
    have divides : r^2∣r*s*u.natAbs := by
      simpa only [Int.natAbs_natCast,Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr raw
    have reduced := Nat.dvd_of_mul_dvd_mul_left (Fact.out : r.Prime).pos
      (show r*r∣r*(s*u.natAbs) by simpa only [pow_two,mul_assoc] using divides)
    have divu := cop.dvd_mul_left.mp reduced
    exact (Fact.out : r.Prime).not_dvd_one (unit ▸ Nat.dvd_gcd divu (dvd_mul_right ..))

/-- For N=pq and a unit u, the target Nu is first-order at both primes.
The count is independent of which unit was used. -/
theorem first_order (ne : p≠q) (op : p≠2) (oq : q≠2) (u : ℤ)
    (unit : u.natAbs.Coprime (p*q)) :
    (points (ZMod ((p*q)^2)) ((p:ℤ)*q*u:ℤ)).card=(p*q)^2*(p^2-1)*(q^2-1) := by
  have cop := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr ne
  have ⟨pl,ph⟩ := vanishes_once cop u unit
  have ⟨ql,qh⟩ := vanishes_once cop.symm u (by simpa only [Nat.mul_comm q p] using unit)
  rw [Int.mul_comm (q:ℤ) p] at ql qh
  rw [change_modulus (mul_pow p q 2),ConeUnitTarget.total_mul_int ((cop.pow_left 2).pow_right 2),
    prime_first_order op _ pl ph, prime_first_order oq _ ql qh]
  ring

/-- The three target types already have different counts modulo 9. -/
theorem nine : (points (ZMod 9) 0).card=99 ∧ (points (ZMod 9) 3).card=72 ∧
    (points (ZMod 9) 1).card=54 := by
  refine ⟨three,?_,?_⟩ <;> decide +kernel

/-- Local count classified by the first two digits of the target. The unit
branch only depends on the first digit. -/
noncomputable def localCount (r : ℕ) [Fact r.Prime] (t : ℤ) : ℕ :=
  if (t:ZMod (r^2))=0 then (r^2-1)*r^2+r^3
  else if (t:ZMod r)=0 then (r^2-1)*r^2 else r^2*(points (ZMod r) t).card

theorem local_count (odd : p≠2) (t : ℤ) :
    (points (ZMod (p^2)) t).card=localCount p t := by
  unfold localCount
  split_ifs with high low
  · rw [high,prime_square p odd]
  · exact prime_first_order odd t low high
  · exact prime_unit odd t low

/-- Splitting the computation into the two local cases also covers targets
that have different divisibility at the two primes. -/
theorem all_targets (ne : p≠q) (op : p≠2) (oq : q≠2) (t : ℤ) :
    (points (ZMod ((p*q)^2)) t).card=localCount p t*localCount q t := by
  have cop := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr ne
  rw [change_modulus (mul_pow p q 2),ConeUnitTarget.total_mul_int ((cop.pow_left 2).pow_right 2),
    local_count op, local_count oq]

/-- The 225 counts are checked via local fibers at 3 and 5. Target 3
vanishes at just one of these primes. -/
theorem controls_225 : (points (ZMod 225) 0).card=71775 ∧ (points (ZMod 225) 15).card=43200 ∧
    (points (ZMod 225) 1).card=40500 ∧ (points (ZMod 225) 3).card=36000 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have check (t : ℤ) : (points (ZMod 225) t).card=localCount 3 t*localCount 5 t :=
    all_targets (p:=3) (q:=5) (by decide) (by decide) (by decide) t
  change (points (ZMod 225) ((0:ℤ):ZMod 225)).card=_ ∧
    (points (ZMod 225) ((15:ℤ):ZMod 225)).card=_ ∧
    (points (ZMod 225) ((1:ℤ):ZMod 225)).card=_ ∧
    (points (ZMod 225) ((3:ℤ):ZMod 225)).card=_
  simp only [check]
  decide +kernel

end PrimeFactors.ConeTargetLifts
