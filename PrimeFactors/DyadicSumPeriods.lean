import PrimeFactors.TwoAdicSumSpacing
import PrimeFactors.MinimalPrimeSquarePeriod
import PrimeFactors.MaskedSquareWitness
import Mathlib.Algebra.Ring.Periodic

/-! Least additive periods of factor-sum admissibility at powers of two. -/
namespace PrimeFactors.DyadicSumPeriods

open PrimePowerSumFilter MinimalPrimeSquarePeriod
open private PrimeFactors.TwoAdicSumSpacing.sum8 PrimeFactors.TwoAdicSumSpacing.sum32
  from PrimeFactors.TwoAdicSumSpacing

private theorem period_iff (n m t : ℕ) :
    Period n m t ↔ Function.Periodic (AdmissibleSum (n : ZMod m)) (t : ZMod m) :=
  ⟨fun h x => propext (h x), fun h x => (h x).to_iff⟩

private theorem multiple {n m a b : ℕ} (h : Period n m a) (div : a∣b) : Period n m b := by
  obtain ⟨k,rfl⟩ := div
  simpa only [period_iff,Nat.cast_mul,mul_comm] using ((period_iff ..).mp h).nat_mul k

/-- A period which is a power of two is minimal if its half fails. -/
theorem period_from_half {n m e : ℕ} (works : Period n m (2^(e+1)))
    (fails : ¬Period n m (2^e)) (t : ℕ) : Period n m t ↔ 2^(e+1)∣t := by
  refine ⟨fun h => ?_,multiple works⟩
  let M := 2^(e+1)
  let g := Nat.gcd t M
  have get : Period n m g := by
    apply (period_iff ..).mpr
    have bez := congrArg (fun z : ℤ => (z:ZMod m)) (Nat.gcd_eq_gcd_ab t M)
    push_cast at bez
    change ((Nat.gcd t M : ℕ) : ZMod m) = _ at bez
    change Function.Periodic _ ((Nat.gcd t M : ℕ):ZMod m)
    rw [bez]
    simpa only [mul_comm] using (((period_iff ..).mp h).int_mul (Nat.gcdA t M)).add_period
      (((period_iff ..).mp works).int_mul (Nat.gcdB t M))
  obtain ⟨j,hj,shape⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_right t M)
  if eq : j=e+1 then
    have same : t.gcd M = 2^(e+1) := shape.trans (congrArg (2^·) eq)
    rw [←same]
    exact Nat.gcd_dvd_left t M
  else
    exact False.elim (fails (multiple get (by change t.gcd M ∣ _; rw [shape]; exact pow_dvd_pow _ (by omega))))

private theorem modulus_period (n m : ℕ) : Period n m m := by
  intro x
  simp

private theorem exponent_one {R : Type*} [CommSemiring R] (a : ℕ) :
    (2:R)^(2*a+1) = 2*(2^a)^2 := by
  rw [pow_succ,Nat.mul_comm 2 a,pow_mul]
  ring

private theorem exponent_two {R : Type*} [CommSemiring R] (a : ℕ) :
    (2:R)^(2*a+1+1) = 4*(2^a)^2 := by rw [pow_succ,exponent_one]; ring

/-- At every depth k≥2, top-bit translation takes some square to a nonsquare. -/
theorem square_half (j : ℕ) : ∃ z : ZMod (2^(j+2)),
    IsSquare z ∧ ¬IsSquare (z+(2:ZMod _)^(j+1)) := by
  obtain ⟨a,ha | ha⟩ := Nat.even_or_odd' j
  · subst j
    refine ⟨0,IsSquare.zero,?_⟩
    rw [zero_add]
    have lift := MaskedSquareWitness.at_depth (p:=2) (a:=a) (u:=1) (by decide)
      (by decide) 2 (2:ℤ)
    have reject : ¬IsSquare (2:ZMod 4) := by
      rintro ⟨z,h⟩
      exact (show ∀ x : ZMod 4, 2≠x*x by decide +kernel) z h
    rw [exponent_one]
    simpa only [mul_one,Int.cast_mul,Int.cast_natCast,Int.cast_pow,Nat.cast_pow,Int.cast_ofNat,
      Nat.cast_ofNat] using lift.not.mpr reject
  · subst j
    let R := ZMod (2^(2*a+1+2))
    refine ⟨((2:R)^a)^2,IsSquare.sq _,?_⟩
    have bad := MaskedSquareWitness.dyadic_first_rejection (a:=a) (u:=1) (d:=5) (by decide) (by decide)
    change ¬IsSquare (((2:R)^a)^2+(2:R)^(2*a+1+1))
    rw [exponent_two]
    rw [show ((2:R)^a)^2+4*((2:R)^a)^2 = 5*((2:R)^a)^2 by ring]
    simpa only [mul_one,Int.cast_mul,Int.cast_natCast,Int.cast_pow,Nat.cast_pow,Int.cast_ofNat,
      Nat.cast_ofNat] using bad

private theorem digit_shift (j : ℕ) (y : ZMod (2^(j+2))) :
    digit (y+2^(j+1))=digit y + 2^(j+1) := by
  have vanish : (2:ZMod (2^(j+2))) * 2^(j+1)=0 := by
    rw [←pow_succ']
    exact_mod_cast ZMod.natCast_self (2^(j+2))
  unfold digit
  linear_combination (4*y+2*2^(j+1))*vanish

/-- In the singular branch the top bit changes the admissible set at each
precision of at least six bits. -/
theorem unit_half_fails (j : ℕ) : ¬ Period 1 (2^(j+6)) (2^(j+5)) := by
  intro h
  obtain ⟨z,good,bad⟩ := square_half j
  obtain ⟨y,hy⟩ := (digit_bijective (j+2)).surjective z
  obtain ⟨v,rfl⟩ := ZMod.intCast_surjective y
  have seen := (singular_branch (j+2) v).mpr (hy ▸ good)
  have shifted := (h (((2+16*v:ℤ)):ZMod (2^(j+6)))).mpr (by simpa only [Nat.cast_one] using seen)
  have index : (2+16*(v+(2:ℤ)^(j+1))) = (2+16*v)+2^(j+5) := by
    rw [show j+5=j+1+4 by omega,pow_add (2:ℤ) (j+1) 4]; ring
  have next := (singular_branch (j+2) (v+2^(j+1))).mp (by
    rw [index]
    simpa only [Int.cast_add,Int.cast_pow,Int.cast_ofNat,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using shifted)
  push_cast at next
  rw [digit_shift,hy] at next
  exact bad next

private theorem unit_times_half (e : ℕ) (r : (ZMod (2^(e+1)))ˣ) :
    (r : ZMod (2^(e+1))) * 2^e = 2^e := by
  let R := ZMod (2^(e+1))
  have cop : (r:R).val.Coprime (2^(e+1)) := (ZMod.isUnit_iff_coprime ..).mp (by simpa only [ZMod.natCast_zmod_val] using r.isUnit)
  have odd := Nat.coprime_two_right.mp (cop.coprime_dvd_right (dvd_pow_self 2 (by omega : e+1≠0)))
  obtain ⟨a,ha⟩ := odd
  have vanish : (2:R)*2^e=0 := by
    rw [←pow_succ']; exact_mod_cast ZMod.natCast_self (2^(e+1))
  have val : (r:R) = 2*(a:R)+1 := by
    rw [←ZMod.natCast_zmod_val (r:R),ha]
    push_cast
    ring
  rw [val]
  linear_combination (a:R)*vanish

/-- For an odd product congruent to one modulo eight every level from six
onwards has its entire modulus as least period. -/
theorem square_deep {N : ℕ} (one : N%8=1) (j t : ℕ) :
    Period N (2^(j+6)) t ↔ 2^(j+6)∣t := by
  apply period_from_half (e:=j+5) (modulus_period N (2^(j+6)))
  intro h
  apply unit_half_fails j
  obtain ⟨r,hr⟩ := normalizing_unit one (j+6)
  intro s
  simp only [Nat.cast_one]
  rw [←normalize r,←normalize r,mul_add]
  rw [hr,Nat.cast_pow,Nat.cast_ofNat,unit_times_half (j+5) r]
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h ((r:ZMod _)*s)

private theorem int_period (n m t : ℕ) : Period n m t ↔
    ∀ s : ℤ, AdmissibleSum (n:ZMod m) ((s+(t:ℤ):ℤ):ZMod m) ↔ AdmissibleSum (n:ZMod m) s := by
  constructor
  · intro h s
    simpa only [Int.cast_add,Int.cast_natCast] using h (s:ZMod m)
  · intro h x
    obtain ⟨s,rfl⟩ := ZMod.intCast_surjective x
    simpa only [Int.cast_add,Int.cast_natCast] using h s

/-- When N is 3 modulo 4 the single class modulo eight is permanent. -/
theorem three_stable {N : ℕ} (three : N%4=3) (k t : ℕ) :
    Period N (2^(k+3)) t ↔ 8∣t := by
  have n : (N:ℤ)%4=3 := by exact_mod_cast three
  have form (s : ℤ) := PrimeFactors.TwoAdicSumSpacing.sum8 (s:=s) n k
  simp only [Int.cast_natCast] at form
  rw [int_period]
  constructor
  · intro ok
    have raw := (form ((N:ℤ)+1+t)).mp ((ok ((N:ℤ)+1)).mpr ((form _).mpr rfl))
    omega
  · intro div s
    rw [form,form]
    omega

/-- When N is 5 modulo 8 the two permanent classes together have least period 32. -/
theorem five_stable {N : ℕ} (five : N%8=5) (k t : ℕ) :
    Period N (2^(k+5)) t ↔ 32∣t := by
  have n : (N:ℤ)%8=5 := by exact_mod_cast five
  have form (s : ℤ) := PrimeFactors.TwoAdicSumSpacing.sum32 (s:=s) n k
  simp only [Int.cast_natCast] at form
  apply period_from_half (e:=4)
  · apply (int_period ..).mpr
    intro s
    rw [form,form]
    omega
  · intro ok
    have shifted := ((int_period ..).mp ok ((N:ℤ)+1)).mpr ((form _).mpr (Or.inl rfl))
    have raw := (form _).mp shifted
    omega

private theorem one_factor {m : ℕ} (n s : ZMod m) :
    AdmissibleSum n s ↔ ∃ x : ZMod m, x*(s-x)=n := by
  constructor
  · rintro ⟨x,y,prod,rfl⟩
    exact ⟨x,by simpa using prod⟩
  · rintro ⟨x,eq⟩
    exact ⟨x,s-x,eq,by ring⟩

private noncomputable instance {m : ℕ} [NeZero m] (n s : ZMod m) : Decidable (AdmissibleSum n s) :=
  decidable_of_iff _ (one_factor n s).symm

private theorem shallow {N m q r e : ℕ} [NeZero m] (div : q∣m) (good : N%q=r)
    (table : ∀ n : ZMod m, n.val%q=r →
      (∀ s : ZMod m, AdmissibleSum n (s+(2^(e+1):ℕ)) ↔ AdmissibleSum n s) ∧
      ¬AdmissibleSum n (n+1+(2^e:ℕ))) (t : ℕ) :
    Period N m t ↔ 2^(e+1)∣t := by
  have h := table (N:ZMod m) (by rw [ZMod.val_natCast,Nat.mod_mod_of_dvd _ div,good])
  apply period_from_half h.1
  intro low
  apply h.2
  exact (low ((N:ZMod m)+1)).mpr ⟨N,1,by simp,rfl⟩

/-- The first two levels carry the parity and then the unique class modulo four. -/
theorem one_bit {N : ℕ} (odd : N%2=1) (t : ℕ) : Period N 2 t ↔ 2∣t :=
  shallow (q:=2) (e:=0) (by decide) odd (by decide +kernel) t

theorem two_bits {N : ℕ} (odd : N%2=1) (t : ℕ) : Period N 4 t ↔ 4∣t :=
  shallow (q:=2) (e:=1) (by decide) odd (by decide +kernel) t

/-- For products 1 modulo 4, levels 3 and 4 have least periods 4 and 16. -/
theorem three_bits {N : ℕ} (one : N%4=1) (t : ℕ) : Period N 8 t ↔ 4∣t :=
  shallow (q:=4) (e:=1) (by decide) one (by decide +kernel) t

theorem four_bits {N : ℕ} (one : N%4=1) (t : ℕ) : Period N 16 t ↔ 16∣t :=
  shallow (q:=4) (e:=3) (by decide) one (by decide +kernel) t

/-- In the square unit class the fifth bit adds no information. The sixth bit does. -/
theorem five_bits {N : ℕ} (one : N%8=1) (t : ℕ) : Period N 32 t ↔ 16∣t :=
  shallow (q:=8) (e:=3) (by decide) one (by decide +kernel) t

private theorem low_cast {m M : ℕ} (div : m∣M) (s : ℕ) : ((s%M:ℕ):ZMod m)=(s:ZMod m) :=
  (ZMod.natCast_eq_natCast_iff' ..).mpr (Nat.mod_mod_of_dvd _ div)

/-- In the square unit class, forgetting the fifth bit preserves the entire decision. -/
theorem five_pullback {N : ℕ} (one : N%8=1) (s : ℕ) :
    AdmissibleSum (N:ZMod 32) s ↔ AdmissibleSum (N:ZMod 16) s := by
  have table : ∀ n x : ZMod 32, n.val%8=1 →
      (AdmissibleSum n x ↔ AdmissibleSum (n.val:ZMod 16) (x.val:ZMod 16)) := by decide +kernel
  have valid : (N:ZMod 32).val%8=1 := by rw [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 8∣32),one]
  simpa only [ZMod.val_natCast,low_cast (by decide : 16∣32)] using table (N:ZMod 32) (s:ZMod 32) valid

/-- The least period is two to this exponent; zero bits give the one-element ring. -/
def leastExponent (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => if N%4=3 then 3 else 2
  | 4 => if N%4=3 then 3 else 4
  | 5 => if N%4=3 then 3 else if N%8=5 then 5 else 4
  | j+6 => if N%4=3 then 3 else if N%8=5 then 5 else j+6

/-- Exact classification at every depth for every odd product. -/
theorem period_iff_dvd {N : ℕ} (odd : N%2=1) (e t : ℕ) :
    Period N (2^e) t ↔ 2^(leastExponent N e) ∣ t := by
  match e with
  | 0 =>
    refine ⟨fun _ => one_dvd _,fun _ x => ?_⟩
    change AdmissibleSum (N:ZMod 1) (x+t) ↔ AdmissibleSum (N:ZMod 1) x
    have eq : x+(t:ZMod 1)=x := Subsingleton.elim (α:=ZMod 1) _ _
    rw [eq]
  | 1 => exact one_bit odd t
  | 2 => exact two_bits odd t
  | 3 =>
    by_cases three : N%4=3
    · simpa [leastExponent,three] using three_stable three 0 t
    · simpa [leastExponent,three] using three_bits (N:=N) (by omega) t
  | 4 =>
    by_cases three : N%4=3
    · simpa [leastExponent,three] using three_stable three 1 t
    · simpa [leastExponent,three] using four_bits (N:=N) (by omega) t
  | 5 =>
    by_cases three : N%4=3
    · simpa [leastExponent,three] using three_stable three 2 t
    by_cases five : N%8=5
    · simpa [leastExponent,three,five] using five_stable five 0 t
    · simpa [leastExponent,three,five] using five_bits (N:=N) (by omega) t
  | j+6 =>
    by_cases three : N%4=3
    · simpa [leastExponent,three] using three_stable three (j+3) t
    by_cases five : N%8=5
    · simpa [leastExponent,three,five] using five_stable five (j+1) t
    · simpa [leastExponent,three,five] using square_deep (N:=N) (by omega) j t

end PrimeFactors.DyadicSumPeriods
