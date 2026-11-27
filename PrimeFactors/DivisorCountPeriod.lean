import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.NumberTheory.LSeries.PrimesInAP
import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.ReciprocalFloorPrefixes

/-! How much information is needed to obtain the count of divisors in a fixed finite
window from a single residue of the input? Even the parity on all natural inputs has
least positive period equal to the lcm of the window. -/
namespace PrimeFactors.DivisorCountPeriod

open Finset

/-- The divisors of the input which occur among the trial values. -/
noncomputable def divisorsIn (A : Finset ℕ) (n : ℕ) := A.filter fun d => d∣n

/-- A change in the reciprocal floor sum gives the exact window count at a positive input. -/
theorem jumps (A : Finset ℕ) {n : ℕ} (np : 0<n) :
    ∑ d∈A, ReciprocalFloorPrefixes.jump n d = (divisorsIn A n).card := by
  simp only [ReciprocalFloorPrefixes.jump_eq np,divisorsIn,Finset.card_filter]

/-- A decoder may perform arbitrary operations on the residue of the input modulo T. -/
def Readable (A : Finset ℕ) (m T : ℕ) :=
  ∀ x y : ℕ, 0<x → 0<y → x ≡ y [MOD T] → (divisorsIn A x).card ≡ (divisorsIn A y).card [MOD m]

/-- Lifting a unit from t to t*P supplies the same residue while avoiding every prime of P. -/
private theorem lift_unit {a t P : ℕ} (tp : 0<t) (pp : 0<P) (cop : a.Coprime t) :
    ∃ z : ℕ, z ≡ a [MOD t] ∧ z.Coprime P := by
  letI : NeZero (t*P) := ⟨(Nat.mul_pos tp pp).ne'⟩
  have h : t∣t*P := dvd_mul_right t P
  obtain ⟨u,eq⟩ := ZMod.unitsMap_surjective h (ZMod.unitOfCoprime a cop)
  refine ⟨(u : ZMod (t*P)).val,?_,Nat.Coprime.of_dvd_right (dvd_mul_left P t) (ZMod.val_coe_unit_coprime u)⟩
  exact (ZMod.natCast_eq_natCast_iff ..).mp (by
    simpa only [ZMod.unitsMap_val,ZMod.cast_eq_val,ZMod.coe_unitOfCoprime] using
      congrArg (fun v : (ZMod t)ˣ => (v : ZMod t)) eq)

/-- A class modulo T contains a representative whose divisors from A are exactly
those of gcd(d,T). The reduction needs only the elementary surjectivity of a unit lift. -/
private theorem witness {A : Finset ℕ} (pos : ∀ d∈A, 0<d) {T : ℕ} (tp : 0<T) (d : ℕ) :
    ∃ n : ℕ, 0<n ∧ n ≡ d [MOD T] ∧ divisorsIn A n=divisorsIn A (d.gcd T) := by
  let g := d.gcd T
  have gp : 0<g := Nat.gcd_pos_of_pos_right _ tp
  have gt := Nat.gcd_dvd_right d T
  have gd := Nat.gcd_dvd_left d T
  have qp : 0<T/g := Nat.div_pos (Nat.le_of_dvd tp gt) gp
  have pp : 0<A.prod id := Finset.prod_pos (fun i hi => pos i hi)
  obtain ⟨z,h,cop⟩ := lift_unit qp pp (Nat.coprime_div_gcd_div_gcd gp)
  obtain ⟨z,zp,h,cop⟩ : ∃ u : ℕ, 0<u ∧ u ≡ d/g [MOD T/g] ∧ u.Coprime (A.prod id) := by
    by_cases zero : z=0
    · subst z
      have one : A.prod id=1 := by simpa using cop
      exact ⟨T/g,qp,(by simpa [Nat.ModEq] using h),by rw [one]; exact Nat.coprime_one_right _⟩
    · exact ⟨z,Nat.pos_of_ne_zero zero,h,cop⟩
  refine ⟨g*z,Nat.mul_pos gp zp,?_,?_⟩
  · simpa only [g,Nat.mul_div_cancel' gt,Nat.mul_div_cancel' gd] using h.mul_left' g
  · ext e
    simp only [divisorsIn,mem_filter]
    constructor
    · rintro ⟨ea,div⟩
      have ec := Nat.Coprime.of_dvd_left (dvd_prod_of_mem id ea) cop.symm
      exact ⟨ea,ec.dvd_of_dvd_mul_right div⟩
    · exact fun ⟨ea,div⟩ => ⟨ea,div.trans (dvd_mul_right g z)⟩

/-- What a residue can certify on its own: all positive inputs with this residue
have a window divisor precisely when gcd(input,T) already contains one. -/
theorem forced_hit_iff {A : Finset ℕ} (pos : ∀ d∈A, 0<d) {T : ℕ} (tp : 0<T) (n : ℕ) :
    (∀ x : ℕ, 0<x → x ≡ n [MOD T] → (divisorsIn A x).Nonempty) ↔
      (divisorsIn A (n.gcd T)).Nonempty := by
  constructor
  · intro all
    obtain ⟨x,xp,cong,same⟩ := witness pos tp n
    rw [←same]
    exact all x xp cong
  · rintro ⟨d,hd⟩ x _ cong
    obtain ⟨mem,dvd⟩ := mem_filter.mp hd
    exact ⟨d,mem_filter.mpr ⟨mem,(cong.dvd_iff (dvd.trans (Nat.gcd_dvd_right n T))).mpr
      (dvd.trans (Nat.gcd_dvd_left n T))⟩⟩

/-- A residue rules out a candidate d exactly when gcd(d,T) fails to divide the
input. CRT constructs a positive compatible input whenever this elementary test passes. -/
theorem possible_hit_iff {A : Finset ℕ} (pos : ∀ d∈A, 0<d) {T : ℕ} (tp : 0<T) (n : ℕ) :
    (∃ x : ℕ, 0<x ∧ x ≡ n [MOD T] ∧ (divisorsIn A x).Nonempty) ↔
      ∃ d∈A, d.gcd T ∣ n := by
  constructor
  · rintro ⟨x,_,cong,d,hd⟩
    obtain ⟨mem,dvd⟩ := mem_filter.mp hd
    exact ⟨d,mem,(cong.dvd_iff (Nat.gcd_dvd_right d T)).mp ((Nat.gcd_dvd_left d T).trans dvd)⟩
  · rintro ⟨d,mem,dvd⟩
    obtain ⟨x,xd,xt⟩ := Nat.chineseRemainder' ((Nat.modEq_zero_iff_dvd.mpr dvd).symm)
    have T0 : d*T ≡ 0 [MOD T] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left T d)
    have d0 : d*T ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right d T)
    refine ⟨x+d*T,by have := Nat.mul_pos (pos d mem) tp; omega,by simpa using xt.add T0,?_⟩
    exact ⟨d,mem_filter.mpr ⟨mem,Nat.modEq_zero_iff_dvd.mp (by simpa using xd.add d0)⟩⟩

/-- Exact period classification, valid for every finite positive window, including
composite trial divisors and overlapping divisibility conditions. -/
theorem readable_iff {A : Finset ℕ} (pos : ∀ d∈A, 0<d) {m T : ℕ} (mp : 2≤m) (tp : 0<T) :
    Readable A m T ↔ A.lcm id ∣ T := by
  rw [Finset.lcm_dvd_iff]
  constructor
  · intro reads d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro hd
      change d∣T
      by_contra bad
      obtain ⟨n,np,cong,same⟩ := witness pos tp d
      have collapse : (divisorsIn A d).erase d=divisorsIn A (d.gcd T) := by
        ext e
        simp only [divisorsIn,mem_erase,mem_filter]
        constructor
        · rintro ⟨ne,ea,div⟩
          have lt := lt_of_le_of_ne (Nat.le_of_dvd (pos d hd) div) ne
          exact ⟨ea,Nat.dvd_gcd div (ih e lt ea)⟩
        · rintro ⟨ea,div⟩
          refine ⟨fun eq => bad (eq ▸ div.trans (Nat.gcd_dvd_right d T)),ea,
            div.trans (Nat.gcd_dvd_left d T)⟩
      have dm : d∈divisorsIn A d := mem_filter.mpr ⟨hd,dvd_rfl⟩
      have count := card_erase_add_one dm
      rw [collapse] at count
      have mod := reads d n (pos d hd) np cong.symm
      rw [same,←count] at mod
      have zero : 1 ≡ 0 [MOD m] := Nat.ModEq.add_left_cancel
        (Nat.ModEq.refl (divisorsIn A (d.gcd T)).card) (by simpa using mod)
      exact (by have := Nat.dvd_one.mp (Nat.modEq_zero_iff_dvd.mp zero); omega)
  · intro covers x y _ _ eq
    have same : divisorsIn A x=divisorsIn A y := by
      ext d
      simp only [divisorsIn,mem_filter]
      exact and_congr_right (fun hd => eq.dvd_iff (covers d hd))
    rw [same]

/-- A single bit on products of distinct primes, with the interval fixed before
the product is supplied. The factors occur only in the specification. -/
def PrimeReadable (A : Finset ℕ) (T : ℕ) : Prop :=
  ∀ p q r s : ℕ, p.Prime → q.Prime → r.Prime → s.Prime → p<q → r<s →
    p*q ≡ r*s [MOD T] → ((p∈A ∨ q∈A) ↔ (r∈A ∨ s∈A))

/-- Even on distinct semiprimes, recognizing whether either prime belongs to a
finite prime set requires reading a modulus divisible by every member.
Dirichlet's theorem supplies arbitrarily large comparison primes. The two
products in this statement need not have the same size or balanced factors. -/
theorem prime_readable_iff {A : Finset ℕ} (prime : ∀ p∈A, p.Prime) {T : ℕ} (tp : 0<T) :
    PrimeReadable A T ↔ A.prod id∣T := by
  constructor
  · intro reads
    apply (Finset.prod_dvd_prod_of_subset A T.primeFactors id ?_).trans (Nat.prod_primeFactors_dvd T)
    intro p hp
    apply Nat.mem_primeFactors.mpr
    refine ⟨prime p hp,?_,tp.ne'⟩
    by_contra bad
    letI : NeZero T := ⟨tp.ne'⟩
    have cop := (prime p hp).coprime_iff_not_dvd.mpr bad
    obtain ⟨r,larger,rp,cong⟩ := Nat.forall_exists_prime_gt_and_eq_mod
      ((ZMod.isUnit_iff_coprime p T).mpr cop) (A.sup id)
    obtain ⟨q,rq,qp⟩ := Nat.exists_infinite_primes (r+1)
    have pr : p<r := lt_of_le_of_lt (le_sup (f:=id) hp) larger
    have rs : r ≡ p [MOD T] := (ZMod.natCast_eq_natCast_iff ..).mp cong
    have rhs := (reads p q r q (prime p hp) qp rp qp (by omega) (by omega)
      (rs.symm.mul_right q)).mp (Or.inl hp)
    rcases rhs with hr|hq
    · exact (not_lt_of_ge (le_sup (f:=id) hr)) larger
    · exact (not_lt_of_ge (le_sup (f:=id) hq)) (larger.trans_le (by exact Nat.le_of_succ_le rq))
  · intro covers p q r s pp qp rp sp _ _ eq
    have resolve {a b c : ℕ} (ha : a∈A) (hb : b.Prime) (hc : c.Prime) (dvd : a∣b*c) :
        b∈A ∨ c∈A := by
      rcases (prime a ha).dvd_mul.mp dvd with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq (prime a ha) hb).mp h ▸ ha)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq (prime a ha) hc).mp h ▸ ha)
    have divides {a : ℕ} (ha : a∈A) : a∣T := (dvd_prod_of_mem id ha).trans covers
    constructor
    · rintro (hp|hq)
      · exact resolve hp rp sp ((eq.dvd_iff (divides hp)).mp (dvd_mul_right p q))
      · exact resolve hq rp sp ((eq.dvd_iff (divides hq)).mp (dvd_mul_left q p))
    · rintro (hr|hs)
      · exact resolve hr pp qp ((eq.dvd_iff (divides hr)).mpr (dvd_mul_right r s))
      · exact resolve hs pp qp ((eq.dvd_iff (divides hs)).mpr (dvd_mul_left s r))

set_option exponentiation.threshold 4096 in
/-- A numeric modulus cost for the prime window [283·2^1023/200,2^1024).
The predicate here accepts distinct semiprimes of any size. -/
theorem upper_window_cost {T : ℕ} (tp : 0<T) (reads : PrimeReadable MixedPrefixSample.upperPrimes T) :
    2^(1023*2^1011) ≤ T := by
  let A := MixedPrefixSample.upperPrimes
  have props {p : ℕ} (hp : p∈A) : 2^1023≤p ∧ p.Prime := by
    obtain ⟨pm,_⟩ := mem_filter.mp hp
    obtain ⟨bd,pp⟩ := mem_filter.mp pm
    exact ⟨(mem_Ico.mp bd).1,pp⟩
  have div := (prime_readable_iff (A:=A) (fun _ h => (props h).2) tp).mp reads
  have count := ChebyshevPrimeSample.prime_count
  change 11*2^1023<35500*(A.card-1) at count
  have many : 2^1011 ≤ A.card := by norm_num1 at count ⊢; omega
  calc
    2^(1023*2^1011) = (2^1023)^2^1011 := pow_mul ..
    _ ≤ (2^1023)^A.card := Nat.pow_le_pow_right (by decide) many
    _ = ∏ _∈A, (2^1023:ℕ) := by simp
    _ ≤ A.prod id := prod_le_prod' fun p hp => (props hp).1
    _ ≤ T := Nat.le_of_dvd tp div

open MixedPrefixSample

attribute [local irreducible] primes

private theorem sorted_eligible {v q : ℕ} (vm : v∈upperPrimes) (qm : q∈upperPrimes)
    (lt : v<q) : (v,q)∈eligible := by
  rw [upperPrimes,mem_filter] at vm qm
  obtain ⟨hp,bp⟩ := vm
  obtain ⟨hq,bq⟩ := qm
  have sz : 2*X^2≤v*q := by
    have h := Nat.mul_le_mul bp bq
    nlinarith only [h,Nat.zero_le (X*X)]
  rw [eligible,sample,mem_filter]
  exact ⟨mem_ordered.mpr ⟨hp,hq,lt.ne,sz,trivial⟩,lt⟩

attribute [local irreducible] eligible sample upperPrimes ordered

set_option exponentiation.threshold 4096 in
/-- On genuine 2048-bit products of two 1024-bit primes, any fixed residue up
to this size conflates two different smaller primes even if the larger prime
is held fixed. The prefix ending at p separates the two inputs, so the residue
cannot answer every prefix query. The separating endpoint may depend on T. -/
theorem balanced_collision {T : ℕ} (tp : 0<T) (small : T≤2^1011) :
    ∃ p r q : ℕ, p<r ∧ r<q ∧ (p,q)∈eligible ∧ (r,q)∈eligible ∧ p*q ≡ r*q [MOD T] := by
  classical
  have count := ChebyshevPrimeSample.prime_count
  change 11*2^1023<35500*(upperPrimes.card-1) at count
  have many : 2^1011<upperPrimes.card-1 := by norm_num1 at count ⊢; omega
  have nonempty : upperPrimes.Nonempty := card_pos.mp (by omega)
  let q := upperPrimes.max' nonempty
  have qin : q∈upperPrimes := max'_mem ..
  have space : (range T).card < (upperPrimes.erase q).card := by
    rw [card_range,card_erase_of_mem qin]
    exact small.trans_lt many
  obtain ⟨p,pin,r,rin,ne,cong⟩ := exists_ne_map_eq_of_card_lt_of_maps_to space
    (f:=fun z : ℕ => z%T) (fun z _ => mem_range.mpr (Nat.mod_lt z tp))
  have qualify {v : ℕ} (vin : v∈upperPrimes.erase q) : v<q ∧ (v,q)∈eligible := by
    obtain ⟨ne,vm⟩ := mem_erase.mp vin
    have lt : v<q := lt_of_le_of_ne (upperPrimes.le_max' v vm) ne
    exact ⟨lt,sorted_eligible vm qin lt⟩
  have pm := qualify pin
  have rm := qualify rin
  have eq : p ≡ r [MOD T] := cong
  rcases lt_or_gt_of_ne ne with lt|gt
  · exact ⟨p,r,q,lt,rm.1,pm.2,rm.2,eq.mul_right q⟩
  · exact ⟨r,p,q,gt,pm.1,rm.2,pm.2,eq.symm.mul_right q⟩

/-- Two 18-bit products of nine-bit primes share the same seven low bits.
Only the first has a divisor in the indicated interval. -/
theorem small_collision :
    Nat.Prime 269 ∧ Nat.Prime 397 ∧ Nat.Prime 499 ∧
    134231=269*499 ∧ 198103=397*499 ∧ 134231 ≡ 198103 [MOD 128] ∧
    (divisorsIn (Icc 257 270) 134231).card=1 ∧ (divisorsIn (Icc 257 270) 198103).card=0 := by
  decide +kernel

end PrimeFactors.DivisorCountPeriod
