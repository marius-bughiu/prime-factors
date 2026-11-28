import PrimeFactors.PersistentLocalSurvivors
import PrimeFactors.FactorSumCRT
import Mathlib.Data.Nat.Factorization.Induction

/-! A uniform survivor bound for a sum modulus chosen after seeing the product. -/

namespace PrimeFactors.LocalSumMenu

open Finset PersistentLocalSurvivors

set_option exponentiation.threshold 2048

noncomputable def count (n m : ℕ) := Nat.card {s : ZMod m // AdmissibleSum (n : ZMod m) s}

private theorem count_pos (n m : ℕ) (pos : 0<m) : 0<count n m := by
  letI : NeZero m := ⟨pos.ne'⟩
  haveI : Nonempty {s : ZMod m // AdmissibleSum (n : ZMod m) s} :=
    ⟨⟨1+n,1,n,one_mul _,rfl⟩⟩
  exact Nat.card_pos

/-- At depth seven the traces of the explicit units 1, 3 and 5 cannot all coincide. -/
private theorem dyadic_seven (n : ℕ) : 2≤count n 128 := by
  classical
  let N : ZMod 128 := n
  have a : AdmissibleSum N (1+N) := ⟨1,N,one_mul _,rfl⟩
  have b : AdmissibleSum N (3+43*N) := ⟨3,43*N,by rw [←mul_assoc,show (3*43 : ZMod 128)=1 by decide,one_mul],rfl⟩
  have c : AdmissibleSum N (5+77*N) := ⟨5,77*N,by rw [←mul_assoc,show (5*77 : ZMod 128)=1 by decide,one_mul],rfl⟩
  have h : (1+N≠3+43*N) ∨ (1+N≠5+77*N) :=
    (show ∀ t : ZMod 128, 1+t≠3+43*t ∨ 1+t≠5+77*t by decide +kernel) N
  letI : Nontrivial {s : ZMod 128 // AdmissibleSum N s} := by
    cases h with
    | inl ne => exact ⟨⟨⟨_,a⟩,⟨_,b⟩,fun h => ne (congrArg Subtype.val h)⟩⟩
    | inr ne => exact ⟨⟨⟨_,a⟩,⟨_,c⟩,fun h => ne (congrArg Subtype.val h)⟩⟩
  change 1<Nat.card {s : ZMod 128 // AdmissibleSum N s}
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- Four permanent 2-adic midpoint classes modulo 128 give at least 1/64 of
all sum residues at every precision. This bound includes odd products in all four classes mod 8. -/
theorem dyadic_density {n : ℕ} (odd : ¬2∣n) (e : ℕ) : 2^e ≤ 64*count n (2^e) := by
  by_cases small : e≤6
  · exact (Nat.pow_le_pow_right (by decide : 0<2) small).trans
      (show 64≤64*count n (2^e) by have := count_pos n (2^e) (by positivity); omega)
  by_cases seven : e=7
  · subst e; have := dyadic_seven n; change 128≤64*count n 128; omega
  obtain ⟨k,rfl⟩ : ∃ k, e=k+8 := ⟨e-8,by omega⟩
  let w := 2^(k+7)
  let m := 2^(k+8)
  letI : NeZero m := ⟨by dsimp [m]; positivity⟩
  have eqm : m=2*w := by dsimp only [m,w]; rw [pow_succ, Nat.mul_comm]
  have two : smallPrimes 2={2} := by decide +kernel
  have low := persistent_interval 2 0 w n (by simp only [two,mem_singleton]; rintro _ rfl; exact odd)
  let S := {i : Fin w // ∀ p∈smallPrimes 2, ∀ e : ℕ, IsSquare ((((0+i.val : ℕ):ℤ)^2-n:ℤ) : ZMod (p^e))}
  let f (i : S) : {s : ZMod m // AdmissibleSum (n : ZMod m) s} :=
    ⟨((2*i.val.val : ℕ) : ZMod m),by
      have h := i.property 2 (by simp [two]) (k+8)
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using (LocalMidpointLanes.midpoint_iff (n : ZMod m) i.val.val).mpr
        (by simpa [m] using h)⟩
  have val_lt (i : S) : 2*i.val.val<m := by rw [eqm]; exact Nat.mul_lt_mul_of_pos_left i.val.isLt (by decide)
  have inject : Function.Injective f := by
    intro i j h
    have h' := congrArg (fun a : {s : ZMod m // AdmissibleSum (n : ZMod m) s} => a.val.val) h
    change (((2*i.val.val:ℕ):ZMod m).val) = (((2*j.val.val:ℕ):ZMod m).val) at h'
    rw [ZMod.val_natCast_of_lt (val_lt _),ZMod.val_natCast_of_lt (val_lt _)] at h'
    exact Subtype.ext (Fin.ext (by omega))
  have co : w/128*4≤count n m := by
    exact (show w/period 2*minPerPeriod 2 ≤ Nat.card S from low).trans
      (Nat.card_le_card_of_injective f inject)
  have ww : w=2^k*128 := pow_add 2 k 7
  rw [ww,Nat.mul_div_cancel _ (by decide)] at co
  change m ≤ 64*count n m
  calc
    m = 2*(2^k*128) := eqm.trans (congrArg (2*·) ww)
    _ ≤ _ := by omega

/-- A finite integer correction for the inequality measuring density loss against modulus size. -/
def charge (p : ℕ) : ℕ :=
  if 283≤p then 1 else if p=2 then 64^8/2 else if p=3 then 12^8/3 else
    max ((2*p)^8 / (p*(p-1)^8) + 1) ((2*p)^8 / (p^2*(p-3)^8) + 1)

private theorem charge_pos (p : ℕ) : 1≤charge p := by
  unfold charge; split_ifs <;> first | decide | exact (Nat.le_add_left 1 _).trans (le_max_left ..)

private theorem large_prime_cost {p : ℕ} (large : 283≤p) : (2*p)^8 ≤ p*(p-3)^8 := by
  have x : (2*p)*45≤91*(p-3) := by omega
  apply (Nat.mul_le_mul_right_iff (by decide : 0<(45:ℕ)^8)).mp
  calc
    (2*p)^8*45^8=((2*p)*45)^8 := (mul_pow ..).symm
    _ ≤ (91*(p-3))^8 := Nat.pow_le_pow_left x _
    _ = 91^8*(p-3)^8 := mul_pow ..
    _ ≤ (p*45^8)*(p-3)^8 := Nat.mul_le_mul_right _ ((by decide : 91^8≤283*45^8).trans (Nat.mul_le_mul_right _ large))
    _ = _ := by ac_rfl

private theorem digit_cost {p : ℕ} (big : 5≤p) :
    (2*p)^8 ≤ p*charge p*(p-1)^8 ∧ (2*p)^8 ≤ p^2*charge p*(p-3)^8 := by
  by_cases large : 283≤p
  · have h := large_prime_cost large
    have eq : charge p=1 := if_pos large
    simp only [eq,mul_one]
    exact ⟨h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)),
      h.trans (Nat.mul_le_mul_right _ (by rw [pow_two]; exact Nat.le_mul_of_pos_right p (by omega)))⟩
  · exact (show ∀ i : Fin 283, (5 ≤ i.val) → ((2*i.val)^8 ≤ i.val*charge i.val*(i.val-1)^8 ∧
      (2*i.val)^8 ≤ i.val^2*charge i.val*(i.val-3)^8) by decide +kernel) ⟨p,by omega⟩ big

private lemma pay {m h p u v g : ℕ} (vo : 0<v) (loc : m*v≤u*h) (bits : u^8≤p*g*v^8)
    (scale : p≤m) : m^8 ≤ m*g*h^8 := by
  apply (Nat.mul_le_mul_right_iff (pow_pos vo 8)).mp
  calc
    m^8*v^8 ≤ u^8*h^8 := by simpa only [mul_pow] using Nat.pow_le_pow_left loc 8
    _ ≤ (p*g*v^8)*h^8 := Nat.mul_le_mul_right _ bits
    _ ≤ (m*g*v^8)*h^8 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ scale))
    _ = _ := by ac_rfl

private lemma regular_cost (p k : ℕ) (prime : p.Prime) (big : 5≤p) (sq : Bool) :
    (p^(k+1))^8 ≤ p^(k+1)*charge p*(primePowerSumCount p sq (k+1))^8 := by
  have odd := prime.odd_of_ne_two (by omega)
  obtain ⟨t,ht⟩ := odd
  rcases k with _|k
  · apply pay (p:=p) (v:=p-1) (u:=2*p) (by omega) _ (digit_cost big).1 (by simp)
    have h : p-1 ≤ 2*primePowerSumCount p sq 1 := by
      cases sq <;> simp [primePowerSumCount,collidingDigitCount] <;> omega
    simpa only [Nat.zero_add,pow_one,←Nat.mul_assoc,Nat.mul_comm p 2] using Nat.mul_le_mul_left p h
  · apply pay (p:=p^2) (v:=p-3) (u:=2*p) (by omega) _ (digit_cost big).2
        (Nat.pow_le_pow_right (by omega) (by omega))
    have lower : (p-3)/2 * p^(k+1) ≤ primePowerSumCount p sq (k+1+1) := by
      cases sq <;> simp only [primePowerSumCount,Bool.true_eq,if_true,if_false]
      · exact Nat.mul_le_mul_right _ (by omega)
      · omega
    calc
      p^(k+1+1)*(p-3) = 2*p*((p-3)/2*p^(k+1)) := by
        calc
          _ = p^(k+1+1)*(2*((p-3)/2)) := congrArg (p^(k+1+1)*·) (by omega)
          _ = _ := by rw [pow_succ]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ lower

private lemma one_prime {p n : ℕ} (prime : p.Prime) (k : ℕ) (cop : p.Coprime n) :
    (p^(k+1))^8 ≤ p^(k+1)*charge p*(count n (p^(k+1)))^8 := by
  classical
  letI : Fact p.Prime := ⟨prime⟩
  have scale : p≤p^(k+1) := by simpa only [pow_one] using Nat.pow_le_pow_right prime.pos (show 1≤k+1 by omega)
  have unit := prime.coprime_iff_not_dvd.mp cop
  by_cases two : p=2
  · subst p
    apply pay (p:=2) (u:=64) (v:=1) (by decide) _ (by decide +kernel) scale
    simpa using dyadic_density unit (k+1)
  have eq : count n (p^(k+1)) = primePowerSumCount p (decide (IsSquare (n : ZMod p))) (k+1) := by
    classical
    simpa only [map_natCast] using card_primePower_admissibleSum two k (n : ZMod (p^(k+1)))
      (by rw [map_natCast]; exact (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp.mt unit)
  rw [eq]
  by_cases three : p=3
  · subst p
    apply pay (p:=3) (u:=12) (v:=1) (by decide) _ (by decide +kernel) scale
    simpa using primePowerSumCount_density two k (decide (IsSquare (n : ZMod 3)))
  have big : 5≤p := by have h := prime.two_le; rcases prime.odd_of_ne_two two with ⟨x,hx⟩; omega
  exact regular_cost p k prime big _

/-- This product bound applies to an arbitrary modulus, including one chosen from N. -/
theorem density_budget (n m : ℕ) : 0<m → m.Coprime n →
    m^8 ≤ m*(∏ p∈m.primeFactors,charge p)*(count n m)^8 := by
  induction m using Nat.recOnPrimeCoprime with
  | h0 => omega
  | hp p e hp =>
    intro pos cop
    cases e with
    | zero =>
      have h := count_pos n 1 (by decide)
      simp only [pow_zero,Nat.primeFactors_one,prod_empty,one_mul,one_pow]
      exact Nat.one_le_iff_ne_zero.mpr (pow_pos h 8).ne'
    | succ k =>
      rw [Nat.primeFactors_prime_pow (Nat.succ_ne_zero _) hp,prod_singleton]
      exact one_prime hp k (cop.of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero _)))
  | h a b ha hb cop ih jh =>
    intro _ units
    have prod : count n (a*b)=count n a*count n b := card_admissibleSum_crt cop n
    obtain ⟨left,right⟩ := Nat.coprime_mul_iff_left.mp units
    rw [Nat.primeFactors_mul (by omega) (by omega),prod_union cop.disjoint_primeFactors,prod,mul_pow,mul_pow]
    calc
      _ ≤ _ := Nat.mul_le_mul (ih (by omega) left) (jh (by omega) right)
      _ = _ := by ac_rfl

private theorem charge_le_table (m : ℕ) :
    (∏ p∈m.primeFactors,charge p) ≤ ∏ p∈(range 283).filter Nat.Prime,charge p := by
  classical
  let s := m.primeFactors.filter (·<283)
  have small : s ⊆ (range 283).filter Nat.Prime := by
    intro p hp
    obtain ⟨f,lt⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr lt,Nat.prime_of_mem_primeFactors f⟩
  have eq : (∏ p∈s, charge p)=∏ p∈m.primeFactors,charge p := by
    apply prod_subset (filter_subset ..)
    intro p mem miss
    exact if_pos (show 283≤p by by_contra! h; exact miss (mem_filter.mpr ⟨mem,h⟩))
  rw [←eq]
  exact prod_le_prod_of_subset_of_one_le' small (fun i _ _ => charge_pos i)

private theorem charge_bound (m : ℕ) : (∏ p∈m.primeFactors,charge p) < 2^197 :=
  (charge_le_table m).trans_lt
    (by decide +kernel : (∏ p∈(range 283).filter Nat.Prime, charge p) < 2^197)

/-- Squaring retains the half-bit of precision lost by rounding the total
charge to a power of two. The same table bounds every positive modulus. -/
theorem charge_bound_squared (m : ℕ) : (∏ p∈m.primeFactors,charge p)^2 < 2^393 :=
  (Nat.pow_le_pow_left (charge_le_table m) 2).trans_lt
    (by decide +kernel : (∏ p∈(range 283).filter Nat.Prime, charge p)^2 < 2^393)

/-- Fewer than 75 bits of density loss for any unit product and any modulus of at most 2^401. -/
theorem fraction_floor {n m : ℕ} (pos : 0<m) (cap : m≤2^401) (cop : m.Coprime n) :
    m < 2^75 * count n m := by
  let h := count n m
  have hpos : 0<h := count_pos n m pos
  have low : m^8 < (2^75*h)^8 := by
    calc
      _ ≤ _ := density_budget n m pos cop
      _ < (m*2^197)*h^8 := Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left (charge_bound m) pos) (pow_pos hpos 8)
      _ ≤ (2^401*2^197)*h^8 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ cap)
      _ ≤ _ := by rw [mul_pow,←pow_mul,←pow_add]; exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by decide))
  exact (Nat.pow_lt_pow_iff_left (by decide : 8≠0)).mp low

/-- Every translate of 2^401 consecutive sums contains over 2^325 locally
admissible values for any product-dependent modulus no larger than the interval. -/
theorem surviving_sums {n m : ℕ} (pos : 0<m) (cap : m≤2^401) (cop : m.Coprime n) (start : ℕ) :
    2^325 < Nat.card {k : Fin (2^401) // AdmissibleSum (n : ZMod m) ((start+k.val : ℕ) : ZMod m)} := by
  let W : ℕ := 2^401
  let q := W/m
  have qpos : 0<q := Nat.div_pos cap pos
  have L : W < (2*m)*q := calc
    W < m*(q+1) := Nat.lt_mul_div_succ W pos
    _ ≤ m*(2*q) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ac_rfl
  have lt : 2^76*2^325<2^76*(q*count n m) := calc
    _ = W := by rw [←pow_add]
    _ < (2*m)*q := L
    _ < (2*(2^75*count n m))*q := Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_left (fraction_floor pos cap cop) (by decide)) qpos
    _ = _ := by rw [show (2:ℕ)^76 = 2*2^75 by decide]; ac_rfl
  exact (Nat.lt_of_mul_lt_mul_left lt).trans_le
    (periodic_interval_lower_bound pos (AdmissibleSum (n : ZMod m)) start W)

/-- A pair realizing a sum modulo the joint modulus supplies a pair for every divisor. -/
theorem reduce {n m d s : ℕ} (div : d∣m) (ok : AdmissibleSum (n : ZMod m) s) :
    AdmissibleSum (n : ZMod d) s := by
  let f := ZMod.castHom div (ZMod d)
  obtain ⟨x,y,prod,sum⟩ := ok
  exact ⟨f x,f y,by simpa only [map_mul,map_natCast] using congrArg f prod,
    by simpa only [map_add,map_natCast] using congrArg f sum⟩

/-- All survivors are even when the joint modulus includes the parity check for an odd product. -/
theorem even_sum {n m s : ℕ} (odd : ¬2∣n) (two : 2∣m) (ok : AdmissibleSum (n : ZMod m) s) :
    Even s := by
  obtain ⟨x,y,prod,sum⟩ := reduce two ok
  have nz : (n : ZMod 2) ≠ 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp.mt odd
  have zero := (show ∀ x y : ZMod 2, x*y≠0 → x+y=0 by decide) x y (prod ▸ nz)
  exact even_iff_two_dvd.mpr ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp (sum.symm.trans zero))

/-- Simultaneously imposing arbitrary moduli dividing m retains the same lower bound. -/
theorem surviving_family {n m : ℕ} (pos : 0<m) (cap : m≤2^401) (cop : m.Coprime n)
    (S : Finset ℕ) (mods : ∀ d∈S, d∣m) (start : ℕ) :
    2^325 < Nat.card {k : Fin (2^401) // ∀ d∈S, AdmissibleSum (n : ZMod d) ((start+k.val : ℕ) : ZMod d)} := by
  apply (surviving_sums pos cap cop start).trans_le
  apply Nat.card_le_card_of_injective (fun k => ⟨k.val,fun d mem => reduce (mods d mem) k.property⟩)
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : {i : Fin (2^401) // ∀ d∈S, AdmissibleSum (n : ZMod d) ((start+i.val : ℕ) : ZMod d)} => z.val) h

end PrimeFactors.LocalSumMenu
