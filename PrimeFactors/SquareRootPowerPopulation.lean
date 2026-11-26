import PrimeFactors.BlockProbePopulation
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-! The population bound for an arbitrary number of repeated squarings of
the public integer square root. -/
namespace PrimeFactors.SquareRootPowerPopulation

open Finset MixedPrefixSample

set_option maxRecDepth 4096
set_option exponentiation.threshold 4096

/-- Exponent of the power of two dividing p−1. -/
noncomputable def exponent (p : ℕ) := (p-1).factorization 2

/-- An uncapped choice of squaring count k. -/
noncomputable def reading (n k : ℕ) : ℤ := (n.sqrt:ℤ)^(2^k)-1

noncomputable def successes : Finset (ℕ×ℕ) := by
  classical exact eligible.filter fun z =>
    ∃ k : ℕ, 1 < Int.gcd (reading (z.1*z.2) k) (z.1*z.2:ℕ) ∧
      Int.gcd (reading (z.1*z.2) k) (z.1*z.2:ℕ) < z.1*z.2

private theorem target : 2<X := by decide +kernel
attribute [local irreducible] X eligible sample ordered primes

/-- The union of all power-of-two root sets is already exhausted at the
two-part of p−1. -/
theorem stabilized {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    (∃ k : ℕ, x^(2^k)=1) ↔ x^(2^(exponent p))=1 := by
  refine ⟨?_, fun hx => ⟨exponent p, hx⟩⟩
  rintro ⟨k,hk⟩
  have nz : x≠0 := by
    rintro rfl
    rw [zero_pow (by positivity : (2:ℕ)^k≠0)] at hk
    exact zero_ne_one hk
  have ord := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j,_,eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ord
  have bound := ZMod.orderOf_dvd_card_sub_one nz
  rw [eq] at bound
  have jf : j≤exponent p := (Nat.prime_two.pow_dvd_iff_le_factorization
    (by have := (Fact.out : p.Prime).two_le; omega)).mp bound
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [eq]
  exact pow_dvd_pow _ jf

private theorem range_dvd {b c : ℕ} (b2 : 2≤b) (S : Finset ℕ)
    (box : ∀ p∈S, b*c≤p ∧ p<2*(b*c) ∧ 1≤p) :
    (S.filter (fun p => b ∣ p-1)).card ≤ c := by
  let f (p : ℕ) := (p-1)/b
  have eq (p : ℕ) (hp : p∈S.filter (fun p => b∣p-1)) : p=f p*b+1 := by
    obtain ⟨sp,dvd⟩ := mem_filter.mp hp
    have core : f p*b=p-1 := Nat.div_mul_cancel dvd
    have lo := (box p sp).2.2
    omega
  have into (p) (hp : p∈S.filter (fun p => b∣p-1)) : f p∈Ico c (2*c) := by
    have bounds := box p (mem_filter.mp hp).1
    have e := eq p hp
    apply mem_Ico.mpr
    constructor
    · by_contra! lo
      have cut := Nat.mul_le_mul_right b (show f p+1≤c by omega)
      nlinarith only [cut,e,bounds.1,b2]
    · by_contra! hi
      have cut := Nat.mul_le_mul_right b hi
      nlinarith only [cut,e,bounds.2.1]
  have card := card_le_card_of_injOn (t:=Ico c (2*c)) f into
    (fun a ha b hb same => by rw [eq a ha, eq b hb, same])
  rw [Nat.card_Ico] at card
  omega

private noncomputable def weight (k p : ℕ) := 2^(min k (exponent p))

private theorem next_weight (k p : ℕ) (pp : 1<p) :
    weight (k+1) p = weight k p + if 2^(k+1)∣p-1 then 2^k else 0 := by
  have iff := Nat.prime_two.pow_dvd_iff_le_factorization (by omega : p-1≠0) (k:=k+1)
  change (2^(k+1)∣p-1 ↔ k+1≤exponent p) at iff
  by_cases h : k+1≤exponent p
  · rw [if_pos (iff.mpr h)]
    simp only [weight, min_eq_left h, min_eq_left (by omega : k≤exponent p), pow_succ]
    omega
  · simp only [weight,min_eq_right (by omega : exponent p≤k+1), min_eq_right (by omega : exponent p≤k),
      if_neg (fun a => h (iff.mp a)),add_zero]

private theorem sum_layer (k : ℕ) (S : Finset ℕ) (pos : ∀ p∈S, 1<p) :
    ∑ p∈S, weight (k+1) p = (∑ p∈S, weight k p) + (S.filter fun p => 2^(k+1)∣p-1).card*2^k := by
  calc
    _ = ∑ p∈S, (weight k p + if 2^(k+1)∣p-1 then 2^k else 0) :=
      sum_congr rfl fun p hp => next_weight k p (pos p hp)
    _ = _ := by rw [sum_add_distrib, ←sum_filter]; simp

/-- An exact period supplies at most one residue class per power of two.
The bound applies even when S contains composite integers. -/
theorem weight_sum (d : ℕ) (S : Finset ℕ)
    (box : ∀ p∈S, 2^d≤p ∧ p<2*(2^d) ∧ 1<p) :
    2*(∑ p∈S, 2^(exponent p)) ≤ 2*S.card+d*2^d := by
  have partial_sum (k : ℕ) (kd : k≤d) :
      2*(∑ p∈S, weight k p) ≤ 2*S.card+k*2^d := by
    induction k with
    | zero => simp [weight]
    | succ k ih =>
      have id : 2^(k+1)*2^(d-(k+1))=(2:ℕ)^d := by
        rw [←pow_add]; congr 1; omega
      have b2 : 2 ≤ (2:ℕ)^(k+1) := by
        rw [pow_succ]
        have z : 0<(2:ℕ)^k := by positivity
        omega
      have cards := range_dvd (c:=2^(d-(k+1))) b2 S (fun p hp => by
        rw [id]
        exact ⟨(box p hp).1,(box p hp).2.1,(box p hp).2.2.le⟩)
      have L := Nat.mul_le_mul_right (2^(k+1)) cards
      rw [Nat.mul_comm (2^(d-(k+1))) _,id] at L
      rw [sum_layer k S (fun p hp => (box p hp).2.2)]
      have prev := ih (by omega)
      let count := (S.filter fun p => 2^(k+1)∣p-1).card
      change count*2^(k+1) ≤ 2^d at L
      change 2*((∑ p∈S,weight k p)+count*2^k) ≤ 2*S.card+(k+1)*2^d
      rw [pow_succ] at L
      nlinarith only [prev,L]
  have ecap (p) (hp : p∈S) : exponent p ≤ d := by
    have dvd : 2^(exponent p)∣p-1 := Nat.ordProj_dvd ..
    have le := Nat.le_of_dvd (by have := (box p hp).2.2; omega : 0<p-1) dvd
    have top := (box p hp).2.1
    apply Nat.le_of_lt_succ
    apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
    rw [pow_succ]
    omega
  have replace_sum : (∑ p∈S, 2^(exponent p)) = ∑ p∈S,weight d p :=
    sum_congr rfl fun p hp => by rw [weight,min_eq_right (ecap p hp)]
  rw [replace_sum]
  exact partial_sum d le_rfl

private theorem prime_data {p : ℕ} (hp : p∈primes) :
    p∈Ico X (2*X) ∧ p%2=1 ∧ p.Prime ∧ 0<exponent p := by
  rw [primes] at hp
  obtain ⟨mem,pp⟩ := mem_filter.mp hp
  have lo := (mem_Ico.mp mem).1
  have u := target
  obtain ⟨r,eq⟩ := pp.odd_of_ne_two (by omega)
  have ep : 1≤exponent p := (Nat.prime_two.pow_dvd_iff_le_factorization
    (by omega : p-1≠0)).mp (by rw [pow_one]; omega)
  exact ⟨mem,by omega,pp,ep⟩

private noncomputable def partners (p : ℕ) : Finset ℕ := by
  classical exact (Ico X (2*X)).filter fun q =>
    q%2=1 ∧ ∃ k, (p:ℤ) ∣ reading (p*q) k

/-- All exponents together permit at most 3·2^(v₂(p−1)−1) odd partners at
one target prime. Squaring the residue uses the evenness of p−1. -/
theorem partner_count {p : ℕ} (hp : p∈primes) :
    (partners p).card ≤ 3*2^(exponent p-1) := by
  classical
  obtain ⟨ip,_,prime,ep⟩ := prime_data hp
  obtain ⟨pl,pu⟩ := mem_Ico.mp ip
  letI : Fact p.Prime := ⟨prime⟩
  let d := 2^(exponent p-1)
  have dp : 0<d := by dsimp [d]; positivity
  have twice : 2*d=2^(exponent p) := by
    dsimp [d]
    rw [←pow_succ',Nat.sub_add_cancel ep]
  let F : Polynomial (ZMod p) := Polynomial.X^d-Polynomial.C 1
  have nz : F≠0 := Polynomial.X_pow_sub_C_ne_zero dp _
  have fits (q : ℕ) (hq : q∈partners p) :
      ((p*q).sqrt : ZMod p)^2 ∈ F.roots.toFinset := by
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots nz).mpr
    obtain ⟨_,_,k,hit⟩ := mem_filter.mp hq
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hit
    simp only [reading, Int.cast_sub, Int.cast_pow, Int.cast_one,Int.cast_natCast,
      sub_eq_zero] at h
    have stable := (stabilized ((p*q).sqrt:ZMod p)).mp ⟨k,h⟩
    simpa only [Polynomial.IsRoot,F,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,
      Polynomial.eval_C,←pow_mul,twice,sub_eq_zero] using stable
  have items := BlockProbePopulation.square_partners pl pu (partners p) F.roots.toFinset
    (fun q hq => by
      obtain ⟨range,odd,_⟩ := mem_filter.mp hq
      exact ⟨(mem_Ico.mp range).1,(mem_Ico.mp range).2,odd⟩) fits
  have count : F.roots.toFinset.card ≤ d := (Multiset.toFinset_card_le _).trans
    (Polynomial.card_roots_X_pow_sub_C dp (1:ZMod p))
  exact items.trans (Nat.mul_le_mul_left 3 count)

private noncomputable def partnerPairs (p : ℕ) := (partners p).image fun q => (min p q,max p q)

private theorem covered : successes ⊆ primes.biUnion partnerPairs := by
  classical
  intro z hz
  obtain ⟨mem,k,nonunit,_⟩ := mem_filter.mp hz
  rw [eligible,sample] at mem
  obtain ⟨ord,lt⟩ := mem_filter.mp mem
  obtain ⟨pm,qm,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp ord
  obtain ⟨pi,po,pp,_⟩ := prime_data pm
  obtain ⟨qi,qo,qp,_⟩ := prime_data qm
  rcases BlockProbePopulation.prime_dvd_reading pp qp _ nonunit with hits|hits
  · exact mem_biUnion.mpr ⟨z.1,pm,mem_image.mpr ⟨z.2,mem_filter.mpr ⟨qi,qo,k,hits⟩,
      by simp [min_eq_left lt.le,max_eq_right lt.le]⟩⟩
  · exact mem_biUnion.mpr ⟨z.2,qm,mem_image.mpr ⟨z.1,mem_filter.mpr
      ⟨pi,po,k,by simpa only [Nat.mul_comm z.2 z.1] using hits⟩,
      by simp [min_eq_right lt.le,max_eq_left lt.le]⟩⟩

private theorem normalize_count {a b s c x : ℕ} (bound : a≤b) (twice : 2*b=3*s)
    (weightBound : 2*s≤2*c+1023*x) (primeCount : c≤x) : 4*a≤3075*x := by omega

private theorem total_hits : successes.card ≤ ∑ p∈primes, 3*2^(exponent p-1) :=
  ((card_le_card covered).trans (card_biUnion_le ..)).trans
    (sum_le_sum fun _ hp => card_image_le.trans (partner_count hp))

private theorem twice_sum (S : Finset ℕ) (f : ℕ→ℕ) (pos : ∀ p∈S,0<f p) :
    2*(∑ p∈S, 3*2^(f p-1)) = 3*(∑ p∈S, 2^(f p)) := by
  rw [mul_sum,mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [show 2*(3*2^(f p-1))=3*(2*2^(f p-1)) by ac_rfl,
    ←pow_succ',Nat.sub_add_cancel (pos p hp)]

private theorem twice_total : 2*(∑ p∈primes, 3*2^(exponent p-1)) =
    3*(∑ p∈primes, 2^(exponent p)) :=
  twice_sum primes exponent (fun _ hp => (prime_data hp).2.2.2)

private theorem target_sum : 2*(∑ p∈primes, 2^(exponent p)) ≤ 2*primes.card+1023*X := by
  rw [X]
  refine weight_sum 1023 primes fun p hp => ?_
  have box := (prime_data hp).1
  have h := mem_Ico.mp box
  have lo := h.1
  have hi := h.2
  have pos := (lt_of_lt_of_le target lo)
  rw [X] at lo hi
  exact ⟨lo,hi,(by omega)⟩

private theorem target_prime_count : primes.card≤X := by
  have h := card_le_card (show primes⊆Ico X (2*X) from fun _ hp => (prime_data hp).1)
  rw [Nat.card_Ico] at h
  exact h.trans_eq (show 2*X-X=X by omega)

/-- A single upper count covers all exponents simultaneously, including an
adaptive procedure choosing k as a function of the product. -/
theorem absolute : 4*successes.card ≤ 3075*X :=
  normalize_count total_hits twice_total target_sum target_prime_count

/-- Unconditional uniform probability on all sorted, distinct 1,024-bit
prime pairs with 2,048-bit product. -/
theorem probability : 2^989*successes.card < eligible.card := by
  have scale : 2^989*21000000*3075 < 4*X := by rw [X]; decide +kernel
  have den : X*X<21000000*eligible.card := by
    rw [X, ←pow_add]
    exact ChebyshevPrimeSample.eligible_count
  have hp := Nat.mul_lt_mul_of_pos_right scale (show 0<X by have := target; omega)
  have c := Nat.mul_le_mul_left (2^989*21000000) absolute
  apply Nat.lt_of_mul_lt_mul_left (a:=4*21000000)
  calc
    _ = (2^989*21000000)*(4*successes.card) := by ac_rfl
    _ ≤ (2^989*21000000)*(3075*X) := c
    _ < 4*(X*X) := by simpa only [Nat.mul_assoc] using hp
    _ < 4*(21000000*eligible.card) := Nat.mul_lt_mul_of_pos_left den (by decide)
    _ = _ := (Nat.mul_assoc ..).symm

private theorem upward {p j k : ℕ} [Fact p.Prime] {x : ZMod p}
    (jk : j≤k) (h : x^(2^j)=1) : x^(2^k)=1 :=
  orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_iff_pow_eq_one.mpr h).trans (pow_dvd_pow _ jk))

/-- The existence of a local hit stabilizes at b−1 for each prime below 2^b. -/
theorem saturated_side {p b k : ℕ} [Fact p.Prime] (limit : p<2^b) (late : b-1≤k) (x : ZMod p) :
    x^(2^k)=1 ↔ x^(2^(b-1))=1 := by
  have dvd : 2^exponent p ∣ p-1 := Nat.ordProj_dvd ..
  have cap : 2^exponent p < 2^b := (Nat.le_of_dvd
    (by have := (Fact.out : p.Prime).two_le; omega : 0<p-1) dvd).trans_lt
    ((Nat.sub_le ..).trans_lt limit)
  have e := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp cap
  exact ⟨fun h => upward (by omega : exponent p≤b-1) ((stabilized x).mp ⟨k,h⟩),upward late⟩

private theorem reading_dvd_iff {p : ℕ} [Fact p.Prime] (n k : ℕ) :
    (p:ℤ)∣reading n k ↔ (n.sqrt:ZMod p)^(2^k)=1 := by
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [reading, Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_one,sub_eq_zero]

private theorem gcd_shape {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q) (a : ℤ) :
    Int.gcd a (p*q:ℕ) = if (p:ℤ)∣a then (if (q:ℤ)∣a then p*q else p)
      else (if (q:ℤ)∣a then q else 1) := by
  have pd : (p:ℤ)∣a ↔ p∣a.natAbs := Int.natAbs_dvd_natAbs.symm
  have qd : (q:ℤ)∣a ↔ q∣a.natAbs := Int.natAbs_dvd_natAbs.symm
  change a.natAbs.gcd (p*q)=_
  rw [Nat.gcd_comm]
  simp only [pd,qd]
  split_ifs with a1 a2 a2
  · exact Nat.gcd_eq_left (((Nat.coprime_primes pp qp).mpr ne).mul_dvd_of_dvd_of_dvd a1 a2)
  · rw [Nat.mul_comm p q]
    exact Nat.gcd_mul_of_coprime_of_dvd (qp.coprime_iff_not_dvd.mpr a2) a1
  · exact Nat.gcd_mul_of_coprime_of_dvd (pp.coprime_iff_not_dvd.mpr a1) a2
  · exact (Nat.coprime_mul_iff_left.mpr
      ⟨pp.coprime_iff_not_dvd.mpr a1,qp.coprime_iff_not_dvd.mpr a2⟩).gcd_eq_one

/-- At and above the common bit cutoff the actual gcd is constant, including
the unit and whole-modulus cases. -/
theorem saturated_gcd {p q b k : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (pl : p<2^b) (ql : q<2^b) (late : b-1≤k) :
    Int.gcd (reading (p*q) k) (p*q:ℕ) = Int.gcd (reading (p*q) (b-1)) (p*q:ℕ) := by
  letI : Fact p.Prime := ⟨pp⟩
  letI : Fact q.Prime := ⟨qp⟩
  have ps : ((p:ℤ)∣reading (p*q) k) ↔ (p:ℤ)∣reading (p*q) (b-1) :=
    (reading_dvd_iff ..).trans ((saturated_side pl late _).trans (reading_dvd_iff ..).symm)
  have qs : ((q:ℤ)∣reading (p*q) k) ↔ (q:ℤ)∣reading (p*q) (b-1) :=
    (reading_dvd_iff ..).trans ((saturated_side ql late _).trans (reading_dvd_iff ..).symm)
  simp only [gcd_shape pp qp ne,ps,qs]

/-- Every gcd ever returned by the infinite family occurs in the first b tests. -/
theorem finite_cutoff {p q b : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (pl : p<2^b) (ql : q<2^b) (k : ℕ) :
    ∃ j≤b-1, Int.gcd (reading (p*q) k) (p*q:ℕ) = Int.gcd (reading (p*q) j) (p*q:ℕ) := by
  rcases le_total k (b-1) with h|h
  · exact ⟨k,h,rfl⟩
  · exact ⟨b-1,le_rfl,saturated_gcd pp qp ne pl ql h⟩

/-- A bounded example where six modular squarings are needed before a nonunit
is found. Each earlier exponent was used as well. -/
theorem six_squarings :
    (∀ k : Fin 6, Int.gcd (reading 33389 k) 33389=1) ∧
    Int.gcd (reading 33389 6) 33389=193 ∧
    Nat.Prime 173 ∧ Nat.Prime 193 ∧ 173*193=(33389:ℕ) := by
  have root : (33389:ℕ).sqrt=182 := Nat.eq_of_le_of_lt_succ
    (Nat.le_sqrt'.mpr (by decide)) (Nat.sqrt_lt'.mpr (by decide))
  simp only [reading,root]
  decide +kernel

end PrimeFactors.SquareRootPowerPopulation
