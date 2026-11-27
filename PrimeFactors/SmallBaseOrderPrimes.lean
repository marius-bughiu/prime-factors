import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic

/-! Count large primes at which one fixed small integer has small multiplicative order.
The proof uses only a product of integers and requires no information about the base's
factorization. The product is a counting device and need not be computed. -/
namespace PrimeFactors.SmallBaseOrderPrimes
open Finset
set_option exponentiation.threshold 2050

/-- Every positive exponent below T occurs as an index. The zero index contributes one. -/
private def multiple (a T : ℕ) := ∏ i ∈ range T, max 1 (a^i-1)

/-- Distinct primes of size at least 2^b, each dividing some a^i−1 for 0<i<T,
have product at least 2^(b·count) and at most a^(T choose 2). -/
theorem powers_bound {a A b T : ℕ} (base : 1<a) (size : a≤2^A) (P : Finset ℕ)
    (prime : ∀ p ∈ P, p.Prime) (lower : ∀ p ∈ P, 2^b≤p)
    (hit : ∀ p ∈ P, ∃ i : ℕ, 0 < i ∧ i < T ∧ p ∣ a^i-1) :
    b*P.card ≤ A*(T.choose 2) := by
  have pos : 0 < multiple a T := prod_pos (fun i _ => lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  have sub : P ⊆ (multiple a T).primeFactors := by
    intro p hp
    obtain ⟨i,ipos,small,dvd⟩ := hit p hp
    have one : 1≤a^i-1 := by have := Nat.one_lt_pow ipos.ne' base; omega
    apply Nat.mem_primeFactors.mpr ⟨prime p hp,_,pos.ne'⟩
    have d := dvd_prod_of_mem (fun j => max 1 (a^j-1)) (mem_range.mpr small)
    exact dvd.trans (by simpa only [max_eq_right one] using d)
  have divides := (prod_dvd_prod_of_subset P _ id sub).trans (Nat.prod_primeFactors_dvd (multiple a T))
  have low : (2^b)^P.card ≤ ∏ p ∈ P, p := by simpa using prod_le_prod' lower
  have top : multiple a T ≤ a^(T.choose 2) := by
    calc
      _ ≤ ∏ i ∈ range T, a^i := prod_le_prod' (fun i _ => max_le
        (Nat.one_le_pow i a (by omega)) (Nat.sub_le _ _))
      _ = _ := by rw [prod_pow_eq_pow_sum,sum_range_id,Nat.choose_two_right]
  apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
  rw [pow_mul,pow_mul]
  exact ((low.trans (Nat.le_of_dvd pos divides)).trans top).trans (Nat.pow_le_pow_left size _)

/-- The CRT family is not needed to define the local count. The upper bound U is exclusive. -/
noncomputable def primes (a b T U : ℕ) : Finset ℕ := by
  classical exact (Ico (2^b) U).filter fun p => p.Prime ∧ a.Coprime p ∧ orderOf (a : ZMod p) < T

theorem mem_primes {a b T U p : ℕ} : p ∈ primes a b T U ↔
    (2^b≤p ∧ p<U) ∧ p.Prime ∧ a.Coprime p ∧ orderOf (a : ZMod p) < T := by
  classical simp [primes]

/-- The group order of the public base itself supplies the exponent in `powers_bound`. -/
theorem order_bound {a A b T U : ℕ} (base : 1<a) (size : a≤2^A) :
    b*(primes a b T U).card ≤ A*(T.choose 2) := by
  classical
  apply powers_bound base size
  · exact fun p hp => (mem_filter.mp hp).2.1
  · exact fun p hp => (mem_Ico.mp (mem_filter.mp hp).1).1
  · intro p hp
    obtain ⟨prime,cop,small⟩ := (mem_filter.mp hp).2
    letI : Fact p.Prime := ⟨prime⟩
    let m := orderOf (a : ZMod p)
    have pos : 0<m := by
      change 0<orderOf (a : ZMod p)
      rw [←ZMod.coe_unitOfCoprime a cop,orderOf_units]
      exact orderOf_pos _
    refine ⟨m,pos,small,?_⟩
    apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Nat.cast_sub (Nat.one_le_pow m a (by omega)),Nat.cast_pow,Nat.cast_one,sub_eq_zero]
    exact pow_orderOf_eq_one _

/-- For all integer bases in [2,2^32], fewer than 2^885 candidate 1024-bit primes
have order below 2^445. U can be any upper cutoff. -/
theorem small_445 {a U : ℕ} (base : 1<a) (size : a≤2^32) :
    (primes a 1023 (2^445) U).card < 2^885 := by
  have h := order_bound (b:=1023) (T:=2^445) (U:=U) base size
  have cap : 32*((2^445).choose 2) < 1023*2^885 := by rw [Nat.choose_two_right]; norm_num
  omega

/-- For the single base 2 the same cutoff gives fewer than 2^880 primes. -/
theorem two_445 (U : ℕ) : (primes 2 1023 (2^445) U).card < 2^880 := by
  have h := order_bound (a:=2) (A:=1) (b:=1023) (T:=2^445) (U:=U) (by decide) (by decide)
  have cap : 1*((2^445).choose 2) < 1023*2^880 := by rw [Nat.choose_two_right]; norm_num
  omega

/-- Primes that have small order for at least one of the public bases 2 through 2^A. -/
noncomputable def basePrefix (A b T U : ℕ) : Finset ℕ :=
  (Icc 2 (2^A)).biUnion fun a => primes a b T U

theorem mem_basePrefix {A b T U p : ℕ} : p ∈ basePrefix A b T U ↔
    ∃ a ∈ Icc 2 (2^A), p ∈ primes a b T U := by classical simp [basePrefix]

theorem mem_basePrefix_of_order {a A b T U p : ℕ} (alo : 2≤a) (ahi : a≤2^A) (ap : a<p)
    (lo : 2^b≤p) (hi : p<U) (prime : p.Prime) (small : orderOf (a : ZMod p)<T) :
    p ∈ basePrefix A b T U :=
  mem_basePrefix.mpr ⟨a,mem_Icc.mpr ⟨alo,ahi⟩,mem_primes.mpr
    ⟨⟨lo,hi⟩,prime,(prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) ap)).symm,small⟩⟩

/-- Overlapping base events require no independence assumption. -/
theorem prefix_bound (A b T U : ℕ) :
    b*(basePrefix A b T U).card ≤ (2^A)*(A*T.choose 2) := by
  classical
  let I := Icc 2 (2^A)
  have bound : (basePrefix A b T U).card ≤ ∑ a ∈ I, (primes a b T U).card := card_biUnion_le
  have size : I.card ≤ 2^A := by simp [I,Nat.card_Icc]
  calc
    _ ≤ b*(∑ a ∈ I, (primes a b T U).card) := Nat.mul_le_mul_left b bound
    _ = ∑ a ∈ I, b*(primes a b T U).card := mul_sum ..
    _ ≤ ∑ _a ∈ I, A*T.choose 2 := sum_le_sum fun a ha =>
      order_bound (show 1 < a from (mem_Icc.mp ha).1) (mem_Icc.mp ha).2
    _ = I.card*(A*T.choose 2) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ size

/-- The entire prefix of 2^21−1 bases and order cutoff 2^438. -/
theorem prefix_438 (U : ℕ) : (basePrefix 21 1023 (2^438) U).card < 2^891 := by
  have h := prefix_bound 21 1023 (2^438) U
  have cap : 2^21*(21*((2^438).choose 2)) < 1023*2^891 := by rw [Nat.choose_two_right]; norm_num
  omega

/-- The shorter order cutoff used with the tilted smooth-divisor estimate. -/
theorem prefix_403 (U : ℕ) : (basePrefix 21 1023 (2^403) U).card < 2^821 := by
  have h := prefix_bound 21 1023 (2^403) U
  have cap : 2^21*(21*((2^403).choose 2)) < 1023*2^821 := by rw [Nat.choose_two_right]; norm_num
  omega

end PrimeFactors.SmallBaseOrderPrimes
