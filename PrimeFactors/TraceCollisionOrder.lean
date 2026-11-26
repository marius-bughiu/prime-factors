import PrimeFactors.FareyWrap
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.FieldTheory.Finite.Basic

/-! Local periods of stride-24 collisions and a bound on the number of large
primes that can have a short period for a fixed base. No factor of the input is supplied
to the search. The primes are used here only to count possible exceptions. -/

namespace PrimeFactors.TraceCollisionOrder

open Finset

/-- The public and true exponents differ by a multiple of p−1. Signed
differences include a tested label on either side of the true trace. -/
theorem remove_public_term {p : ℕ} (hp : p.Prime) (v : (ZMod p)ˣ)
    {a b q z c : ℤ} (collision : v^(c*(a+b*p*q-z))=1) :
    v^(c*(a*p+b*q-z))=1 := by
  have card : orderOf v ∣ p-1 := by
    letI : NeZero p := ⟨hp.ne_zero⟩
    simpa only [ZMod.card_units_eq_totient, Nat.totient_prime hp] using
      (orderOf_dvd_card (x:=v))
  have cardZ : (orderOf v : ℤ) ∣ (p:ℤ)-1 := by
    have pp := hp.one_le
    exact_mod_cast card
  have corr := dvd_mul_of_dvd_left cardZ (c*(b*q-a))
  have agree := dvd_sub (orderOf_dvd_iff_zpow_eq_one.mpr collision) corr
  apply orderOf_dvd_iff_zpow_eq_one.mp
  convert agree using 1
  ring

/-- In progression coordinates this is stronger than divisibility of the raw
difference: the signed difference divided by the stride is a multiple of the
order. A true trace and a tested label both belong to the same public stride. -/
theorem collision_index {p d : ℕ} (hp : p.Prime) (v : (ZMod p)ˣ) (stride : d∣24)
    {a b q z j : ℤ} (grid : a*p+b*q-z=(d:ℤ)*j)
    (hit : v^(((24/d:ℕ):ℤ)*(a+b*p*q-z))=1) :
    (orderOf (v^24) : ℤ) ∣ j :=
  (FareyWrap.period v stride grid).mp (remove_public_term hp v hit)

/-- Even without a grid witness, every local collision obeys the raw-difference
order restriction. Applies to the fixed unit with residue 2 at each odd prime. -/
theorem collision_difference {p d : ℕ} (hp : p.Prime) (v : (ZMod p)ˣ) (stride : d∣24)
    {a b q z : ℤ} (hit : v^(((24/d:ℕ):ℤ)*(a+b*p*q-z))=1) :
    (orderOf (v^24) : ℤ) ∣ a*p+b*q-z := by
  let T : ℤ := a*p+b*q-z
  have eq : v^(((24/d:ℕ):ℤ)*T)=1 := remove_public_term hp v hit
  have mult : (((24/d:ℕ):ℤ)*(d:ℤ))=24 := by exact_mod_cast Nat.div_mul_cancel stride
  have full : v^((24:ℤ)*T)=1 := by
    have h := congrArg (fun w : (ZMod p)ˣ => w^(d:ℤ)) eq
    dsimp only at h
    rw [← zpow_mul, one_zpow] at h
    rwa [show ((24/d:ℕ):ℤ)*T*d=24*T by rw [←mult]; ring] at h
  exact (FareyWrap.period v (s:=1) (by decide) (T:=T) (t:=0) (j:=T) (by simp)).mp
    (by simpa using full)

/-- Natural-power version of a fixed-base baby/giant coincidence. The
candidate label has already absorbed the public step and the baby index. -/
theorem record_difference_base {base p a b q z d : ℕ} (pp : p.Prime)
    (cop : base.Coprime p) (stride : d∣24)
    (hit : (base:ZMod p)^((24/d)*(a+b*(p*q)))=(base:ZMod p)^((24/d)*z)) :
    (orderOf ((ZMod.unitOfCoprime base cop)^24):ℤ) ∣ (a:ℤ)*p+(b:ℤ)*q-z := by
  let v := ZMod.unitOfCoprime base cop
  have unitHit : v^((24/d)*(a+b*(p*q)))=v^((24/d)*z) := by
    apply Units.ext
    simpa [v, ZMod.coe_unitOfCoprime] using hit
  apply collision_difference pp v stride
  rw [show (((24/d:ℕ):ℤ)*((a:ℤ)+(b:ℤ)*p*q-z)) =
    (((24/d)*(a+b*(p*q)):ℕ):ℤ)-(((24/d)*z:ℕ):ℤ) by push_cast; ring]
  rw [zpow_sub, zpow_natCast, zpow_natCast, unitHit, mul_inv_cancel]

/-- Natural-power version of a fixed-base baby/giant coincidence. The
candidate label has already absorbed the public step and the baby index. -/
theorem record_difference {p a b q z d : ℕ} (pp : p.Prime)
    (cop : (2:ℕ).Coprime p) (stride : d∣24)
    (hit : (2:ZMod p)^((24/d)*(a+b*(p*q)))=(2:ZMod p)^((24/d)*z)) :
    (orderOf ((ZMod.unitOfCoprime 2 cop)^24):ℤ) ∣ (a:ℤ)*p+(b:ℤ)*q-z :=
  record_difference_base pp cop stride hit

private def term (base j : ℕ) := base^(24*j)-1
private def product (base H : ℕ) := ∏ i ∈ range H, term base (i+1)

private theorem divides_product {base p H j : ℕ} (pos : 0<j) (le : j≤H)
    (dvd : p∣term base j) : p∣product base H := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  exact dvd.trans (dvd_prod_of_mem (fun i => term base (i+1)) (mem_range.mpr (by omega : i<H)))

private theorem positive_product {base : ℕ} (min : 2≤base) (H : ℕ) : 0<product base H := by
  apply prod_pos
  intro i _
  unfold term
  exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by positivity) min)

private theorem product_size (base H : ℕ) : product base H ≤ base^(12*H*(H+1)) := by
  induction H with
  | zero => simp [product]
  | succ H ih =>
    change (∏ i ∈ range (H+1), term base (i+1)) ≤ _
    rw [prod_range_succ]
    rw [show 12*(H+1)*(H+1+1)=12*H*(H+1)+24*(H+1) by ring, pow_add]
    exact Nat.mul_le_mul ih (Nat.sub_le _ _)

/-- Each prime divisor of the public setup gcd has a positive return index for
this base. The gcd itself may contain primes with different return indices. -/
theorem setup_factor_base {base p n H : ℕ} (pp : p.Prime)
    (hit : p∣Nat.gcd ((∏ i ∈ range H, (base^(24*(i+1))-1))%n) n) :
    ∃ j, 0<j ∧ j≤H ∧ p∣base^(24*j)-1 := by
  have pn := hit.trans (Nat.gcd_dvd_right ..)
  have hp : p∣product base H := (Nat.dvd_mod_iff pn).mp (hit.trans (Nat.gcd_dvd_left ..))
  obtain ⟨i,hi,dvd⟩ := (pp.prime.dvd_finset_prod_iff (fun i => term base (i+1))).mp hp
  exact ⟨i+1, by omega, mem_range.mp hi, dvd⟩

theorem setup_factor {p n H : ℕ} (pp : p.Prime)
    (hit : p∣Nat.gcd ((∏ i ∈ range H, (2^(24*(i+1))-1:ℕ))%n) n) :
    ∃ j, 0<j ∧ j≤H ∧ p∣2^(24*j)-1 := setup_factor_base pp hit

/-- The single product for a base at most 2^s uses at most s times the original
base-two exponent budget. The distinct primes in S jointly divide this product. -/
theorem base_exception_bits {base s H e : ℕ} {S : Finset ℕ} (min : 2≤base) (max : base≤2^s)
    (small : ∀ p∈S, 2^e≤p ∧ p.Prime ∧ ∃ j, 0<j ∧ j≤H ∧ p∣base^(24*j)-1) :
    e*S.card ≤ s*(12*H*(H+1)) := by
  have d : (∏ p∈S,p) ∣ product base H := by
    apply prod_primes_dvd
    · exact fun p h => (small p h).2.1.prime
    · intro p h
      obtain ⟨j,hj,le,div⟩ := (small p h).2.2
      exact divides_product hj le div
  have lower := prod_le_prod' (f:=fun _ : ℕ => (2:ℕ)^e) (g:=id) (s:=S)
    (fun p h => (small p h).1)
  simp only [prod_const, id_eq] at lower
  apply (Nat.pow_le_pow_iff_right (show 1<(2:ℕ) by decide)).mp
  rw [pow_mul, pow_mul]
  exact ((lower.trans (Nat.le_of_dvd (positive_product min H) d)).trans (product_size base H)).trans
    (Nat.pow_le_pow_left max _)

theorem exception_bits {S : Finset ℕ} {H e : ℕ}
    (small : ∀ p∈S, 2^e≤p ∧ p.Prime ∧ ∃ j, 0<j ∧ j≤H ∧ p∣2^(24*j)-1) :
    e*S.card ≤ 12*H*(H+1) := by
  simpa only [one_mul] using base_exception_bits (base:=2) (s:=1) (by decide) (by decide) small

/-- A target-width prime belongs exactly when some positive index up to H
is a return to one for the designated base. -/
noncomputable def lowFor (base H : ℕ) : Finset ℕ := by
  classical
  exact (Ico (2^1023) (2^1024)).filter fun p =>
    p.Prime ∧ ∃ j, 0<j ∧ j≤H ∧ p∣base^(24*j)-1

theorem mem_lowFor {p base H : ℕ} : p∈lowFor base H ↔
    2^1023≤p ∧ p<2^1024 ∧ p.Prime ∧ ∃ j, 0<j ∧ j≤H ∧ p∣base^(24*j)-1 := by
  classical
  simp only [lowFor, mem_filter, mem_Ico, and_assoc]

noncomputable def lowOrderPrimes (H : ℕ) : Finset ℕ := lowFor 2 H

theorem mem_lowOrderPrimes {p H : ℕ} : p∈lowOrderPrimes H ↔
    2^1023≤p ∧ p<2^1024 ∧ p.Prime ∧ ∃ j, 0<j ∧ j≤H ∧ p∣2^(24*j)-1 := mem_lowFor

theorem lowFor_bits {base s H : ℕ} (min : 2≤base) (max : base≤2^s) :
    1023*(lowFor base H).card ≤ s*(12*H*(H+1)) :=
  base_exception_bits min max (fun _ h => ⟨(mem_lowFor.mp h).1, (mem_lowFor.mp h).2.2⟩)

theorem lowFor_card {base : ℕ} (min : 2≤base) (max : base≤2^22) :
    (lowFor base (2^475)).card < 2^949 := by
  have numeric : 22*(12*(2:ℕ)^475*(2^475+1))<1023*2^949 := by decide +kernel
  exact Nat.lt_of_mul_lt_mul_left ((lowFor_bits min max).trans_lt numeric)

theorem lowOrderPrimes_card : (lowOrderPrimes (2^475)).card < 2^944 := by
  have bound := exception_bits (H:=2^475) (e:=1023) (S:=lowOrderPrimes (2^475))
    (fun p h => ⟨(mem_lowOrderPrimes.mp h).1, (mem_lowOrderPrimes.mp h).2.2⟩)
  have numeric : 12*(2:ℕ)^475*(2^475+1)<1023*2^944 := by decide +kernel
  exact Nat.lt_of_mul_lt_mul_left (bound.trans_lt numeric)

theorem target_base_coprime {base p : ℕ} (min : 2≤base) (max : base≤2^22)
    (lo : 2^1023≤p) (pp : p.Prime) : base.Coprime p := by
  have less : base<p := lt_of_le_of_lt max ((by decide +kernel : (2:ℕ)^22<2^1023).trans_le lo)
  exact (pp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) less)).symm

theorem mem_of_order_le_base {base p H : ℕ} (lo : 2^1023≤p) (hi : p<2^1024) (pp : p.Prime)
    (cop : base.Coprime p) (short : orderOf ((ZMod.unitOfCoprime base cop)^24)≤H) :
    p∈lowFor base H := by
  letI : NeZero p := ⟨pp.ne_zero⟩
  let v := ZMod.unitOfCoprime base cop
  let j := orderOf (v^24)
  refine mem_lowFor.mpr ⟨lo,hi,pp,j,orderOf_pos _,short,?_⟩
  have val := congrArg (fun w : (ZMod p)ˣ => (w : ZMod p)) (pow_orderOf_eq_one (v^24))
  have eq : (1:ZMod p)=(base:ZMod p)^(24*j) := by
    rw [pow_mul]
    simpa [j, v, ZMod.coe_unitOfCoprime] using val.symm
  have pos : 0<base := by
    by_contra! h
    have zero : base=0 := by omega
    exact pp.ne_one (by simpa [zero] using cop)
  apply (Nat.modEq_iff_dvd' (Nat.one_le_pow (24*j) base pos)).mp
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  push_cast
  exact eq

theorem mem_of_order_le {p H : ℕ} (lo : 2^1023≤p) (hi : p<2^1024) (pp : p.Prime)
    (cop : (2:ℕ).Coprime p) (short : orderOf ((ZMod.unitOfCoprime 2 cop)^24)≤H) :
    p∈lowOrderPrimes H := mem_of_order_le_base lo hi pp cop short

/-- Normalization of one emitted giant and one tested baby. The signed
giant exponent and the block recursion are represented by the left side. -/
theorem giant_baby_record {G : Type*} [Group G] (v : G)
    {A z d r m i : ℕ} (step : d∣24) :
    v^(((24/d:ℕ):ℤ)*((A:ℤ)-((z+d*(r*m):ℕ):ℤ)))=(v^ (24:ℕ))^i ↔
    v^((24/d)*A)=v^((24/d)*(z+d*(r*m+i))) := by
  have period : (((24/d:ℕ):ℤ)*(d:ℤ))=24 := by exact_mod_cast Nat.div_mul_cancel step
  let a : ℤ := ((24/d:ℕ):ℤ)*A
  let b : ℤ := ((24/d:ℕ):ℤ)*(z+d*(r*m):ℕ)
  let c : ℤ := 24*i
  have ab : ((24/d:ℕ):ℤ)*((A:ℤ)-((z+d*(r*m):ℕ):ℤ))=a-b := by dsimp [a,b]; ring
  have bc : (((24/d)*(z+d*(r*m+i)):ℕ):ℤ)=c+b := by
    dsimp only [b,c]; simp only [Nat.cast_add,Nat.cast_mul]
    linear_combination (i:ℤ)*period
  have leftPower : (v^(24:ℕ))^i=v^c := by
    rw [←pow_mul]
    have eq : c=((24*i:ℕ):ℤ) := by simp only [c,Nat.cast_mul,Nat.cast_ofNat]
    rw [eq,zpow_natCast]
  have rightPower : v^((24/d)*(z+d*(r*m+i)))=v^(c+b) := by rw [←bc,zpow_natCast]
  have publicPower : v^((24/d)*A)=v^a := by dsimp only [a]; rw [←Nat.cast_mul, zpow_natCast]
  rw [ab,leftPower,rightPower,publicPower,zpow_sub,zpow_add]
  exact mul_inv_eq_iff_eq_mul

end PrimeFactors.TraceCollisionOrder
