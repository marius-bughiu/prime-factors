import PrimeFactors.JacobiMomentRecurrence
import Mathlib.Data.Nat.Prime.Factorial

/-! Prime divisibility of the complete positive even Jacobi moment itself. -/
namespace PrimeFactors.JacobiMomentZeros

open Finset JacobiMomentRecurrence ProjectiveWordMoments
open private PrimeFactors.ProjectiveWordMoments.local_signed
  PrimeFactors.ProjectiveWordMoments.signed_moment from PrimeFactors.ProjectiveWordMoments

/-- At a positive multiple of p−1 the zero residue drops out and all nonzero powers are 1. -/
theorem at_multiple {p k : ℕ} [Fact p.Prime] (odd : p ≠ 2) (kp : 0 < k) (dv : p-1 ∣ k) :
    component p k = 1 + ((ZMod.χ₄ p : ℤ) : ZMod p) := by
  classical
  let f := fun t : ZMod p => ((quadraticChar (ZMod p) (t^2-4) : ℤ) : ZMod p)
  have full : (∑ t, f t) = -1 := by
    simp only [f,←Int.cast_sum,PrimeFactors.ProjectiveWordMoments.local_signed odd,Int.cast_neg,Int.cast_one]
  have charOdd : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have two : (2:ZMod p)≠0 := Ring.two_ne_zero charOdd
  have origin : f 0 = ((ZMod.χ₄ p : ℤ) : ZMod p) := by
    simp only [f,show (0:ZMod p)^2-4 = (-1)*2^2 by ring, map_mul,quadraticChar_sq_one' two,
      mul_one,quadraticChar_neg_one charOdd,ZMod.card]
  have term (x : ZMod p) : x^k*f x = f x - (if x=0 then f 0 else 0) := by
    by_cases zero : x=0
    · simp [zero,zero_pow kp.ne']
    obtain ⟨u,ku⟩ := dv
    simp only [if_neg zero,sub_zero,ku,pow_mul,ZMod.pow_card_sub_one_eq_one zero,one_pow,one_mul]
  change -(∑ x, x^k*f x) = _
  simp only [term,sum_sub_distrib]
  simp [full,origin]
  ring

/-- In particular, the exceptional value is 1+(-1)^((p−1)/2). -/
theorem value_at_multiple {p k : ℕ} [Fact p.Prime] (odd : p ≠ 2) (kp : 0 < k) (dv : p-1 ∣ k) :
    component p k = 1 + (-1 : ZMod p)^((p-1)/2) := by
  obtain ⟨u,hu⟩ := (Fact.out : p.Prime).odd_of_ne_two odd
  rw [at_multiple odd kp dv,ZMod.χ₄_eq_neg_one_pow (by omega : p%2=1)]
  push_cast
  rw [show p/2=(p-1)/2 by omega]

/-- Positive nonendpoint degrees reduce to the ordinary central binomial value
at their residue. The positivity assumption keeps the zero-residue term unchanged. -/
theorem at_remainder {p k : ℕ} [Fact p.Prime] (odd : p ≠ 2) (kp : 0 < k)
    (nonmultiple : ¬ p-1 ∣ k) : component p k = (central (k%(p-1)) : ZMod p) := by
  let r := k%(p-1)
  have pp := (Fact.out : p.Prime).one_lt
  have rp : 0 < r := Nat.pos_of_ne_zero (fun zero => nonmultiple (Nat.dvd_of_mod_eq_zero zero))
  have rlt : r < p-1 := Nat.mod_lt _ (by omega)
  have reduce (x : ZMod p) : x^k=x^r := by
    by_cases zero : x=0
    · simp [zero,zero_pow kp.ne',zero_pow rp.ne']
    exact pow_eq_pow_mod k (ZMod.pow_card_sub_one_eq_one zero)
  change -(∑ x : ZMod p, x^k*((quadraticChar (ZMod p) (x^2-4) : ℤ) : ZMod p)) = _
  simp only [reduce,PrimeFactors.ProjectiveWordMoments.signed_moment odd r rlt,neg_neg]
  rfl

private theorem central_ne_zero {p r : ℕ} [Fact p.Prime] (low : r < p) (ev : r%2=0) :
    (central r : ZMod p) ≠ 0 := by
  rw [central,if_pos ev,ne_eq,ZMod.natCast_zmod_eq_zero_iff_dvd]
  intro h
  have dvd : p ∣ r.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial (show r/2≤r from Nat.div_le_self ..)]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
  exact (not_le_of_gt low) ((Fact.out : p.Prime).dvd_factorial.mp dvd)

/-- A prime-field component vanishes exactly on the positive even multiples of
p−1 at primes that are 3 modulo 4. -/
theorem local_zero_iff {p k : ℕ} [Fact p.Prime] (odd : p≠2) (kp : 0 < k) (ev : k%2=0) :
    component p k=0 ↔ p%4=3 ∧ p-1∣k := by
  obtain ⟨u,hu⟩ := (Fact.out : p.Prime).odd_of_ne_two odd
  by_cases dv : p-1∣k
  · rw [at_multiple odd kp dv]
    by_cases three : p%4=3
    · simp [ZMod.χ₄_nat_three_mod_four three,three,dv]
    · have one : p%4=1 := by omega
      have two : (2:ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
      simp [ZMod.χ₄_nat_one_mod_four one,three,one_add_one_eq_two,two]
  · rw [at_remainder odd kp dv]
    have evenPred : 2∣p-1 := ⟨u,by omega⟩
    have par := (Nat.mod_mod_of_dvd k evenPred).trans ev
    have low := Nat.mod_lt k (show 0<p-1 by have := (Fact.out : p.Prime).one_lt; omega)
    simp [dv,central_ne_zero (p:=p) (r:=k%(p-1)) (by omega) par]

/-- The gcd with pq contains each local prime exactly when it is 3 modulo 4
and its predecessor divides the even degree. -/
theorem moment_gcd {p q k : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (oddP : p≠2) (oddQ : q≠2) (kp : 0<k) (ev : k%2=0) :
    (p*q).gcd (moment (p*q) k).val =
      (if p%4=3 ∧ p-1∣k then p else 1)*(if q%4=3 ∧ q-1∣k then q else 1) := by
  let m := moment (p*q) k
  have crt : ZMod.chineseRemainder cop m = (component p k,component q k) := components cop oddP oddQ k
  have proj : ((m.val:ZMod p),(m.val:ZMod q)) = (component p k,component q k) := calc
    _ = ZMod.chineseRemainder cop (m.val:ZMod (p*q)) := by rw [map_natCast]; rfl
    _ = _ := by rw [ZMod.natCast_zmod_val,crt]
  have pdiv : p ∣ m.val ↔ p%4=3 ∧ p-1∣k := by
    rw [←ZMod.natCast_zmod_eq_zero_iff_dvd,show (m.val:ZMod p)=component p k from congrArg Prod.fst proj,
      local_zero_iff oddP kp ev]
  have qdiv : q ∣ m.val ↔ q%4=3 ∧ q-1∣k := by
    rw [←ZMod.natCast_zmod_eq_zero_iff_dvd,show (m.val:ZMod q)=component q k from congrArg Prod.snd proj,
      local_zero_iff oddQ kp ev]
  have prime_gcd (l : ℕ) (prime : l.Prime) : m.val.gcd l = if l∣m.val then l else 1 := by
    split_ifs with h
    · exact Nat.gcd_eq_right h
    · exact (prime.coprime_iff_not_dvd.mpr h).symm.gcd_eq_one
  change (p*q).gcd m.val = _
  rw [Nat.gcd_comm,cop.gcd_mul,prime_gcd p Fact.out,prime_gcd q Fact.out]
  simp only [pdiv,qdiv]

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- At level 15 all positive even degrees give gcd 3, including the endpoint of 5. -/
theorem three_five {k : ℕ} (kp : 0 < k) (ev : k%2=0) : (15:ℕ).gcd (moment 15 k).val=3 := by
  have h := moment_gcd (p:=3) (q:=5) (by decide) (by decide) (by decide) kp ev
  have d : 2∣k := Nat.dvd_of_mod_eq_zero ev
  simpa [d,show 3%4=3 by decide,show 5%4≠3 by decide] using h

end PrimeFactors.JacobiMomentZeros
