import PrimeFactors.FixedBaseSignature

/-! An exponent gap between two global power matches factors the product
whenever the two local multiplicative orders differ. The method applies to
any set of candidate labels: the labels between the two matches are immaterial. -/

namespace PrimeFactors.GeometricCollisionGap

/-- The multiplicative order of the given integer base at a unit modulus. -/
noncomputable def ord (n g : ℕ) (unit : g.Coprime n) := orderOf (ZMod.unitOfCoprime g unit)

private theorem criterion {n g e : ℕ} (unit : g.Coprime n) :
    ord n g unit ∣ e ↔ g^e ≡ 1 [MOD n] := by
  rw [ord,orderOf_dvd_iff_pow_eq_one,←ZMod.eq_iff_modEq_nat]
  refine ⟨fun h => ?_,fun h => ?_⟩
  · simpa only [Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,Units.val_one,Nat.cast_pow,
      Nat.cast_one] using congrArg Units.val h
  · apply Units.ext
    simpa only [Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,Units.val_one,Nat.cast_pow,
      Nat.cast_one] using h

private theorem pos {n g : ℕ} (unit : g.Coprime n) : 0<ord n g unit := by
  exact orderOf_pos (ZMod.unitOfCoprime g unit)

/-- The order visible to public power tests is exactly the lcm of the two
local orders. The equality holds for any coprime moduli. -/
theorem global_order {p q g : ℕ} (cop : p.Coprime q) (unit : g.Coprime (p*q)) :
    ord (p*q) g unit =
      (ord p g (unit.of_dvd_right (dvd_mul_right p q))).lcm
      (ord q g (unit.of_dvd_right (dvd_mul_left q p))) := by
  have h (e : ℕ) := (criterion (e:=e) unit).trans (Nat.modEq_and_modEq_iff_modEq_mul cop).symm
  simp_rw [←criterion (unit.of_dvd_right (dvd_mul_right p q)),
    ←criterion (unit.of_dvd_right (dvd_mul_left q p))] at h
  exact Nat.dvd_antisymm ((h _).mpr ⟨Nat.dvd_lcm_left ..,Nat.dvd_lcm_right ..⟩)
    (Nat.lcm_dvd ((h _).mp dvd_rfl).1 ((h _).mp dvd_rfl).2)

/-- Two distinct matched labels provide a positive annihilating exponent,
so the prime factors of the order are among those of their public gap. -/
theorem order_dvd_gap {n g a b E : ℕ} (unit : g.Coprime n) (ordab : a<b)
    (first : g^a ≡ g^E [MOD n]) (second : g^b ≡ g^E [MOD n]) :
    0<b-a ∧ ord n g unit ∣ b-a := by
  let u := ZMod.unitOfCoprime g unit
  have eq : u^a=u^b := by
    apply Units.ext
    simpa only [u,Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,Nat.cast_pow] using
      (ZMod.eq_iff_modEq_nat n).mpr (first.trans second.symm)
  have cancel : u^a*u^(b-a)=u^a := by rw [←pow_add,Nat.add_sub_of_le ordab.le,eq]
  exact ⟨Nat.sub_pos_of_lt ordab,orderOf_dvd_of_pow_eq_one (mul_eq_left.mp cancel)⟩

/-- Division tests on the distinct primes of a candidate divisor certify
that stripping has stopped at the exact order. All tests use the public modulus. -/
theorem stripped {n g d : ℕ} (unit : g.Coprime n) (hd : 0<d)
    (kill : g^d ≡ 1 [MOD n])
    (minimal : ∀ ℓ, ℓ.Prime → ℓ∣d → ¬g^(d/ℓ) ≡ 1 [MOD n]) : ord n g unit=d := by
  apply orderOf_eq_of_pow_and_pow_div_prime hd
  · exact orderOf_dvd_iff_pow_eq_one.mp ((criterion unit).mpr kill)
  · intro ℓ prime div eq
    exact minimal ℓ prime div ((criterion unit).mp (orderOf_dvd_of_pow_eq_one eq))

private theorem prime_removal {a b d : ℕ} (positive : 0<d) (sub : a∣d)
    (proper : a≠d) (join : a.lcm b=d) :
    ∃ ℓ, ℓ.Prime ∧ ℓ∣d ∧ a∣d/ℓ ∧ ¬b∣d/ℓ := by
  obtain ⟨c,hc⟩ := sub
  have cne : c≠1 := by rintro rfl; simp_all
  let ℓ := c.minFac
  have prime : ℓ.Prime := Nat.minFac_prime cne
  obtain ⟨t,ht⟩ := Nat.minFac_dvd c
  have hd : d=ℓ*(a*t) := by rw [hc,ht]; change a*(ℓ*t)=ℓ*(a*t); ring
  have div : ℓ∣d := ⟨a*t,hd⟩
  have reduced : d/ℓ=a*t := by rw [hd,Nat.mul_div_cancel_left _ prime.pos]
  refine ⟨ℓ,prime,div,by rw [reduced];exact dvd_mul_right ..,?_⟩
  intro bdiv
  have dx : d∣d/ℓ := by
    rw [←join] at *
    exact Nat.lcm_dvd (by rw [reduced];exact dvd_mul_right ..) bdiv
  have less := Nat.div_lt_self positive prime.one_lt
  have z := Nat.div_pos (Nat.le_of_dvd positive div) prime.pos
  exact (Nat.not_le_of_lt less) (Nat.le_of_dvd z dx)

/-- One order is a proper divisor of the lcm. Removing a prime from its
complement leaves that order dividing the quotient, but cannot leave both. -/
theorem distinguishing_prime {a b : ℕ} (ha : 0<a) (hb : 0<b) (ne : a≠b) :
    let d := a.lcm b
    ∃ ℓ, ℓ.Prime ∧ ℓ∣d ∧ ((a∣d/ℓ ∧ ¬b∣d/ℓ) ∨ (b∣d/ℓ ∧ ¬a∣d/ℓ)) := by
  let d := a.lcm b
  have positive : 0<d := Nat.lcm_pos ha hb
  by_cases ad : a=d
  · obtain ⟨ℓ,pr,div,bd,na⟩ := prime_removal positive (Nat.dvd_lcm_right a b)
      (show b≠d from fun h => ne (ad.trans h.symm)) (Nat.lcm_comm b a)
    exact ⟨ℓ,pr,div,Or.inr ⟨bd,na⟩⟩
  · obtain ⟨ℓ,pr,div,bd,na⟩ := prime_removal positive (Nat.dvd_lcm_left a b) ad rfl
    exact ⟨ℓ,pr,div,Or.inl ⟨bd,na⟩⟩

/-- Reducing the power difference before taking the gcd keeps its value. -/
noncomputable def gcdProbe (n g e : ℕ) := n.gcd (((g:ZMod n)^e-1).val)

private theorem one_side {p q g e : ℕ} (prime : q.Prime) (gpos : 0<g)
    (yes : g^e ≡ 1 [MOD p]) (no : ¬g^e ≡ 1 [MOD q]) : gcdProbe (p*q) g e=p := by
  have order : 1≤g^e := pow_pos gpos _
  have dp := (Nat.modEq_iff_dvd' order).mp yes.symm
  have dq : ¬q∣g^e-1 := fun div => no ((Nat.modEq_iff_dvd' order).mpr div).symm
  have base := Nat.gcd_mul_of_coprime_of_dvd (prime.coprime_iff_not_dvd.mpr dq) dp
  rw [mul_comm q p] at base
  unfold gcdProbe
  rw [show (g:ZMod (p*q))^e-1=((g^e-1:ℕ):ZMod (p*q)) by rw [Nat.cast_sub order,Nat.cast_pow,Nat.cast_one],
    ZMod.val_natCast]
  simpa only [Nat.gcd_comm ((g^e-1)%(p*q)) (p*q),Nat.gcd_rec (p*q) (g^e-1)] using base

/-- Scanning just the distinct prime divisors of the exact public order gives
a proper factor as soon as the two local orders differ. -/
theorem split {p q g : ℕ} (hp : p.Prime) (hq : q.Prime) (distinct : p≠q)
    (unit : g.Coprime (p*q))
    (ne : ord p g (unit.of_dvd_right (dvd_mul_right p q)) ≠
          ord q g (unit.of_dvd_right (dvd_mul_left q p))) :
    let d := ord (p*q) g unit
    ∃ ℓ, ℓ.Prime ∧ ℓ∣d ∧ (gcdProbe (p*q) g (d/ℓ)=p ∨ gcdProbe (p*q) g (d/ℓ)=q) := by
  let up := unit.of_dvd_right (dvd_mul_right p q)
  let uq := unit.of_dvd_right (dvd_mul_left q p)
  have gp : 0<g := by
    by_contra! h; have zero : g=0 := by omega
    have := (show g.Coprime p from up); rw [zero,Nat.coprime_zero_left] at this
    exact hp.ne_one this
  obtain ⟨ℓ,prime,div,cases⟩ := distinguishing_prime (pos up) (pos uq) ne
  dsimp only
  rw [global_order ((Nat.coprime_primes hp hq).mpr distinct) unit]
  refine ⟨ℓ,prime,div,?_⟩
  rcases cases with ⟨ap,bq⟩|⟨bq,ap⟩
  · exact Or.inl (one_side hq gp ((criterion up).mp ap) (fun h => bq ((criterion uq).mpr h)))
  · apply Or.inr
    simpa only [mul_comm q p] using (one_side hp gp ((criterion uq).mp bq) (fun h => ap ((criterion up).mpr h)))

private theorem ambient {p g : ℕ} (hp : p.Prime) (unit : g.Coprime p) : ord p g unit∣p-1 := by
  letI : Fact p.Prime := ⟨hp⟩
  exact orderOf_dvd_of_pow_eq_one (ZMod.units_pow_card_sub_one_eq_one p _)

/-- Equal orders give a second copy of d in (p−1)(q−1), so the unknown
factor sum is determined modulo d². -/
theorem common_sum {p q g d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (up : g.Coprime p) (uq : g.Coprime q) (op : ord p g up=d) (oq : ord q g uq=d) :
    p+q ≡ p*q+1 [MOD d^2] := by
  have dv := Nat.mul_dvd_mul (op ▸ ambient hp up) (oq ▸ ambient hq uq)
  obtain ⟨a,pa⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  obtain ⟨b,qb⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne_zero
  rw [pa,qb,Nat.succ_sub_one,Nat.succ_sub_one] at dv
  rw [pa,qb,show (a+1)*(b+1)+1=(a+1+(b+1))+a*b by ring,
    Nat.modEq_iff_dvd' (Nat.le_add_right ..),Nat.add_sub_cancel_left,pow_two]
  exact dv

/-- Failure of the public Fermat test rules out equal local orders. -/
theorem fermat_witness_ne_orders {p q g : ℕ} (hp : p.Prime) (hq : q.Prime) (distinct : p≠q)
    (unit : g.Coprime (p*q)) (witness : ¬g^(p*q-1) ≡ 1 [MOD p*q]) :
    ord p g (unit.of_dvd_right (dvd_mul_right p q)) ≠
      ord q g (unit.of_dvd_right (dvd_mul_left q p)) := by
  intro same
  let up := unit.of_dvd_right (dvd_mul_right p q)
  let uq := unit.of_dvd_right (dvd_mul_left q p)
  let d := ord p g up
  have pd : d∣p-1 := ambient hp up
  have qd : d∣q-1 := by change ord p g up∣q-1; rw [same]; exact ambient hq uq
  have p1 : 1 ≡ p [MOD d] := (Nat.modEq_iff_dvd' hp.one_le).mpr pd
  have q1 : 1 ≡ q [MOD d] := (Nat.modEq_iff_dvd' hq.one_le).mpr qd
  have mul : 1 ≡ p*q [MOD d] := by simpa only [one_mul] using p1.mul q1
  have common : d∣p*q-1 := (Nat.modEq_iff_dvd' (Nat.mul_pos hp.pos hq.pos)).mp mul
  apply witness
  apply (criterion unit).mp
  rw [global_order ((Nat.coprime_primes hp hq).mpr distinct) unit,←same,Nat.lcm_self]
  exact common

/-- Scan a supplied prime factorization of an annihilating exponent, with
repetitions. The caller can implement `kill e` by modular exponentiation.
The function makes at most one power test per list entry. -/
def strip (kill : ℕ → Bool) (h : ℕ) : List ℕ → ℕ
  | [] => h
  | ℓ :: rest => strip kill (if ℓ∣h ∧ kill (h/ℓ) then h/ℓ else h) rest

private theorem strip_extra {d : ℕ} (hd : 0<d) (kill : ℕ → Bool)
    (ok : ∀ e, kill e=true ↔ d∣e) (parts : List ℕ) (primes : ∀ ℓ∈parts, ℓ.Prime)
    {c : ℕ} (covers : c∣parts.prod) : strip kill (d*c) parts=d := by
  induction parts generalizing c with
  | nil =>
    have eq : c=1 := Nat.dvd_one.mp covers
    simp [eq,strip]
  | cons ℓ rest ih =>
    have prime := primes ℓ List.mem_cons_self
    have tail (v : ℕ) (hv : v∈rest) := primes v (List.mem_cons_of_mem ℓ hv)
    rw [List.prod_cons] at covers
    rw [strip]
    by_cases extra : ℓ∣c
    · obtain ⟨t,rfl⟩ := extra
      have div : ℓ∣d*(ℓ*t) := dvd_mul_of_dvd_right (dvd_mul_right ℓ t) d
      have quo : d*(ℓ*t)/ℓ=d*t := by
        rw [show d*(ℓ*t)=ℓ*(d*t) by ring,Nat.mul_div_cancel_left _ prime.pos]
      rw [if_pos ⟨div,(ok _).mpr (by rw [quo]; exact dvd_mul_right ..)⟩,quo]
      exact ih tail ((Nat.mul_dvd_mul_iff_left prime.pos).mp covers)
    · have leave : ¬(ℓ∣d*c ∧ kill (d*c/ℓ)=true) := by
        rintro ⟨div,test⟩
        have reduced := (Nat.dvd_div_iff_mul_dvd div).mp ((ok _).mp test)
        rw [mul_comm ℓ d] at reduced
        exact extra ((Nat.mul_dvd_mul_iff_left hd).mp reduced)
      rw [if_neg leave]
      exact ih tail ((prime.coprime_iff_not_dvd.mpr extra).symm.dvd_of_dvd_mul_left covers)

/-- Correctness of stripping from any known, factored annihilator. -/
theorem strip_order {n g h : ℕ} (unit : g.Coprime n) (ann : ord n g unit∣h)
    (parts : List ℕ) (product : parts.prod=h) (primes : ∀ ℓ∈parts,ℓ.Prime)
    (kill : ℕ → Bool) (test : ∀ e,kill e=true ↔ g^e ≡ 1 [MOD n]) :
    strip kill h parts=ord n g unit := by
  obtain ⟨c,hc⟩ := ann
  rw [hc]
  apply strip_extra (pos unit) kill (fun e => (test e).trans (criterion unit).symm) parts primes
  rw [product,hc]
  exact dvd_mul_left ..

/-- After any two agreeing power labels, an ordinary Fermat witness suffices
for an actual factor. The only extra factorization input is the positive label
gap, whose prime list and product can be checked independently. -/
theorem fermat_gap_split {p q g a b E : ℕ} (hp : p.Prime) (hq : q.Prime) (distinct : p≠q)
    (unit : g.Coprime (p*q)) (witness : ¬g^(p*q-1) ≡ 1 [MOD p*q])
    (ab : a<b) (first : g^a ≡ g^E [MOD p*q]) (second : g^b ≡ g^E [MOD p*q])
    (parts : List ℕ) (product : parts.prod=b-a) (primes : ∀ ℓ∈parts,ℓ.Prime)
    (kill : ℕ → Bool) (test : ∀ e,kill e=true ↔ g^e ≡ 1 [MOD p*q]) :
    let d := strip kill (b-a) parts
    ∃ ℓ∈(b-a).primeFactors, ℓ∣d ∧ (gcdProbe (p*q) g (d/ℓ)=p ∨ gcdProbe (p*q) g (d/ℓ)=q) := by
  have gap := order_dvd_gap unit ab first second
  dsimp only
  rw [strip_order unit gap.2 parts product primes kill test]
  obtain ⟨ℓ,prime,div,out⟩ := split hp hq distinct unit (fermat_witness_ne_orders hp hq distinct unit witness)
  exact ⟨ℓ,Nat.mem_primeFactors.mpr ⟨prime,div.trans gap.2,gap.1.ne'⟩,div,out⟩

/-- A previously observed alias has gap 188. Halving the gap gives a proper
factor of the same number. This example uses the unfiltered labels; the
known modulus-three sieve rejects the false sum 6300. -/
theorem alias_8842111 :
    (2:ZMod 8842111)^6112=5844590 ∧ (2:ZMod 8842111)^6300=5844590 ∧
    6300-6112=(188:ℕ) ∧ (2:ZMod 8842111)^(188/2 : ℕ)=5882203 ∧
    Nat.gcd 8842111 (5882203-1)=2351 ∧ 2351*3761=8842111 ∧
    Nat.Prime 2351 ∧ Nat.Prime 3761 := by
  obtain ⟨hp,hq,product,_,_,_,_,hit₁,hit₂⟩ := FixedBaseSignature.base_two_alias
  exact ⟨hit₁,hit₂,rfl,by decide +kernel,by decide +kernel,product,hp,hq⟩

end PrimeFactors.GeometricCollisionGap
