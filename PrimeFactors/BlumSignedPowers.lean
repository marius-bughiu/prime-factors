import PrimeFactors.JacobiSeparation
import Mathlib.Tactic

/-! Signed odd powers of a negative-Jacobi seed at two Blum primes. -/
namespace PrimeFactors.BlumSignedPowers

private theorem two_kernel {p : ℕ} [Fact p.Prime] (blum : p%4=3) (x : ZMod p) (k : ℕ) :
    x^(2^(k+1))=1 ↔ x^2=1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ 2 (k+1),pow_mul,sq_eq_one_iff]
    constructor
    · rintro (h|h)
      · exact ih.mp h
      · rw [pow_succ 2 k,pow_mul] at h
        exact (ZMod.mod_four_ne_three_of_sq_eq_neg_one h blum).elim
    · intro h
      exact Or.inl (ih.mpr h)

private theorem sign_fixed {R : Type*} [Ring R] {x : R} (h : x=1 ∨ x= -1)
    {t : ℕ} (o : Odd t) : x^t=x := by
  rcases h with rfl|rfl
  · exact one_pow _
  · exact o.neg_one_pow

/-- An odd power of a unit in a Blum prime field can reach only the
sign given by its original Legendre symbol. -/
theorem sign {p : ℕ} [Fact p.Prime] (blum : p%4=3) (a : ℤ) (unit : (a:ZMod p)≠0)
    {e : ℕ} (odd : Odd e) (hit : (a:ZMod p)^e=1 ∨ (a:ZMod p)^e= -1) :
    (a:ZMod p)^e=(legendreSym p a : ZMod p) := by
  have s : (legendreSym p a : ZMod p)=1 ∨ (legendreSym p a : ZMod p)= -1 := by
    rcases legendreSym.eq_one_or_neg_one p unit with h|h <;> rw [h] <;> simp
  have half : Odd (p/2) := Nat.odd_iff.mpr (by omega)
  calc
    _ = ((a:ZMod p)^e)^(p/2) := (sign_fixed hit half).symm
    _ = ((a:ZMod p)^(p/2))^e := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
    _ = _ := by rw [←legendreSym.eq_pow]; exact sign_fixed s odd

/-- Strip the powers of 2 from the public exponent E. The order of a^E
divides an odd multiplier m exactly when the signed power at the odd
exponent t*m reaches the original local Legendre symbol. -/
theorem local_iff {p E t k m : ℕ} [Fact p.Prime] (blum : p%4=3) (a : ℤ)
    (unit : (a:ZMod p)≠0) (decomp : E=2^(k+1)*t) (ot : Odd t) (om : Odd m) :
    orderOf ((a:ZMod p)^E)∣m ↔ (a:ZMod p)^(t*m)=(legendreSym p a : ZMod p) := by
  have eq : ((a:ZMod p)^E)^m=((a:ZMod p)^(t*m))^(2^(k+1)) := by
    rw [←pow_mul,←pow_mul,decomp]; congr 1; ring
  rw [orderOf_dvd_iff_pow_eq_one,eq,two_kernel blum,sq_eq_one_iff]
  constructor
  · exact sign blum a unit (ot.mul om)
  · intro h
    rw [h]
    rcases legendreSym.eq_one_or_neg_one p unit with h|h <;> rw [h] <;> simp

/-- The doubled orbit at indices j has multiplier 2^j−1. Its local
returns are the multiples of the multiplicative order of 2 modulo r. -/
theorem mersenne (r j : ℕ) : r∣2^j-1 ↔ orderOf (2 : ZMod r)∣j := by
  rw [← Nat.modEq_iff_dvd' (show 1≤2^j from Nat.one_le_pow _ _ (by decide)),orderOf_dvd_iff_pow_eq_one]
  rw [← ZMod.natCast_eq_natCast_iff]
  simp [eq_comm]

/-- On a negative-Jacobi input, the two local signed readouts use
opposite slots; both local orders may return on the same iteration. -/
theorem opposite {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    {a : ℤ} (neg : jacobiSym a (p*q)= -1) :
    (legendreSym p a=1 ∧ legendreSym q a= -1) ∨
    (legendreSym p a= -1 ∧ legendreSym q a=1) := by
  rw [jacobiSym.mul_right' _ hp.out.ne_zero hq.out.ne_zero,
    ←jacobiSym.legendreSym.to_jacobiSym p,←jacobiSym.legendreSym.to_jacobiSym q] at neg
  have up : (a:ZMod p)≠0 := by
    intro zero
    rw [(legendreSym.eq_zero_iff p a).mpr zero,zero_mul] at neg
    contradiction
  have uq : (a:ZMod q)≠0 := by
    intro zero
    rw [(legendreSym.eq_zero_iff q a).mpr zero,mul_zero] at neg
    contradiction
  rcases legendreSym.eq_one_or_neg_one p up with h|h <;>
    rcases legendreSym.eq_one_or_neg_one q uq with h'|h' <;> simp_all

/-- Exactly one field reaches a particular sign. This is the condition
for a proper gcd in the corresponding plus or minus slot. -/
def Separates {p q : ℕ} (x : ZMod p) (y : ZMod q) : Prop :=
  (x=1 ∧ y≠1) ∨ (y=1 ∧ x≠1) ∨ (x= -1 ∧ y≠ -1) ∨ (y= -1 ∧ x≠ -1)

private theorem diff {p : ℕ} [Fact p.Prime] (blum : p%4=3) : (1:ZMod p)≠ -1 := by
  intro eq
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_one (y:=1) (by simpa using eq) blum

/-- Testing both signs returns a proper divisor precisely when at least one
local order divides m, including the case where both divide m. -/
theorem split_iff {p q E t k m : ℕ} [Fact p.Prime] [Fact q.Prime]
    (bp : p%4=3) (bq : q%4=3) {a : ℤ} (neg : jacobiSym a (p*q)= -1)
    (up : (a:ZMod p)≠0) (uq : (a:ZMod q)≠0)
    (decomp : E=2^(k+1)*t) (ot : Odd t) (om : Odd m) :
    Separates ((a:ZMod p)^(t*m)) ((a:ZMod q)^(t*m)) ↔
    orderOf ((a:ZMod p)^E)∣m ∨ orderOf ((a:ZMod q)^E)∣m := by
  rw [local_iff bp a up decomp ot om,local_iff bq a uq decomp ot om]
  have ps := sign bp a up (ot.mul om)
  have qs := sign bq a uq (ot.mul om)
  have no_minus {l : ℕ} [Fact l.Prime] (bl : l%4=3) {x : ZMod l}
      (rule : x=1 ∨ x= -1 → x=1) : x≠ -1 :=
    fun h => diff bl ((rule (Or.inr h)).symm.trans h)
  have no_plus {l : ℕ} [Fact l.Prime] (bl : l%4=3) {x : ZMod l}
      (rule : x=1 ∨ x= -1 → x= -1) : x≠1 :=
    fun h => diff bl (h.symm.trans (rule (Or.inl h)))
  obtain ⟨sp,sq⟩|⟨sp,sq⟩ := opposite neg
  · rw [sp] at ps ⊢
    rw [sq] at qs ⊢
    simp only [Int.cast_one,Int.cast_neg] at ps qs ⊢
    simp [Separates,no_minus bp ps,no_plus bq qs]
  · rw [sp] at ps ⊢
    rw [sq] at qs ⊢
    simp only [Int.cast_one,Int.cast_neg] at ps qs ⊢
    simp [Separates,no_plus bp ps,no_minus bq qs,or_comm]

/-- First-return divisibility criterion in units of actual squarings. -/
theorem iteration {p q E t k j : ℕ} [Fact p.Prime] [Fact q.Prime]
    (bp : p%4=3) (bq : q%4=3) {a : ℤ} (neg : jacobiSym a (p*q)= -1)
    (up : (a:ZMod p)≠0) (uq : (a:ZMod q)≠0)
    (decomp : E=2^(k+1)*t) (ot : Odd t) (jp : 0<j) :
    Separates ((a:ZMod p)^(t*(2^j-1))) ((a:ZMod q)^(t*(2^j-1))) ↔
    orderOf (2 : ZMod (orderOf ((a:ZMod p)^E)))∣j ∨
    orderOf (2 : ZMod (orderOf ((a:ZMod q)^E)))∣j := by
  have parity := Even.pow_of_ne_zero (show Even (2:ℕ) by decide) jp.ne'
  have odd : Odd (2^j-1) := Nat.odd_iff.mpr (by
    have h := Nat.even_iff.mp parity
    have pos := Nat.one_le_pow j 2 (by decide)
    omega)
  rw [split_iff bp bq neg up uq decomp ot odd,mersenne,mersenne]

/-- Every base that survives the square precheck has the same reduced
order at a safe prime when the half exponent is coprime to its odd predecessor. -/
theorem safe_order {p r E e : ℕ} [hp : Fact p.Prime] [Fact r.Prime]
    (shape : p=2*r+1) (ee : E=2*e) (ep : 0<e) (cop : r.Coprime e)
    (a : ZMod p) (unit : a≠0) (live : a^2≠1) : orderOf (a^E)=r := by
  have kill : (a^2)^r=1 := by
    rw [←pow_mul,show 2*r=p-1 by omega]
    exact ZMod.pow_card_sub_one_eq_one unit
  have order : orderOf (a^2)=r := orderOf_eq_prime kill live
  rw [ee,pow_mul,orderOf_pow' _ ep.ne',order,cop.gcd_eq_one,Nat.div_one]

/-- A single public gcd precheck implies the local nontrivial-square
hypothesis simultaneously at both hidden primes. -/
theorem live_of_precheck {p a N : ℕ} [hp : Fact p.Prime] (dv : p∣N)
    (ap : 0<a) (cop : (a^2-1).Coprime N) : (a:ZMod p)^2≠1 := by
  intro h
  have mod : 1 ≡ a^2 [MOD p] := (ZMod.natCast_eq_natCast_iff 1 (a^2) p).mp
    (by simpa only [Nat.cast_one,Nat.cast_pow] using h.symm)
  exact hp.out.coprime_iff_not_dvd.mp (cop.coprime_dvd_right dv).symm
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ ap)).mp mod)

end PrimeFactors.BlumSignedPowers
