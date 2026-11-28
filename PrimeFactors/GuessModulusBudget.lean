import PrimeFactors.PrimeSquareUniformFloor
import PrimeFactors.QuotientBudget

/-! A finite bound for the uniform component on local tables at distinct
odd prime squares. The product of the prime squares is bounded by 2^2048.
The extremum uses the first 129 primes from 5 through 739. -/

namespace PrimeFactors.GuessModulusBudget

open Finset PrimeSquareExpectedRank PrimeSquareUniformFloor
open private PrimeFactors.budgetPrimes_trial from PrimeFactors.QuotientBudget

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

noncomputable def primes (k : ℕ) := (quotientBudgetPrimes k).filter (5 ≤ ·)
noncomputable def ratio (p : ℕ) : ℝ := (numerator p : ℝ) / pairs p
noncomputable def penalty (p : ℕ) : ℝ := (pairs p : ℝ) / numerator p
noncomputable def budget (T : Finset ℕ) := ∏ p∈T, p^2
noncomputable def pairProduct (T : Finset ℕ) := ∏ p∈T, pairs p
noncomputable def numeratorProduct (T : Finset ℕ) := ∏ p∈T, numerator p

private theorem mem_primes {p k : ℕ} : p∈primes k ↔ p.Prime ∧ 5 ≤ p ∧ p ≤ k := by
  simp only [primes,quotientBudgetPrimes,mem_filter,mem_range,Nat.lt_succ_iff]
  tauto

private def receipt (s t : Finset ℕ) : Prop :=
  s.card=129 ∧ t.card=130 ∧
  2^2031≤budget s ∧ budget s<2^2032 ∧
  2^2050≤budget t ∧ budget t<2^2051 ∧
  7581413*pairProduct s<100000000*numeratorProduct s ∧
    100000000*numeratorProduct s<7581415*pairProduct s ∧
  13225704*numeratorProduct t<1000000*pairProduct t ∧
    1000000*pairProduct t<13225705*numeratorProduct t

private noncomputable instance (s t : Finset ℕ) : Decidable (receipt s t) := by unfold receipt; infer_instance

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
private theorem checked : receipt (primes 739) (primes 743) := by
  unfold primes
  rw [PrimeFactors.budgetPrimes_trial 739 (by decide),PrimeFactors.budgetPrimes_trial 743 (by decide)]
  decide +kernel

theorem cutoff_facts :
    (primes 739).card=129 ∧ (primes 743).card=130 ∧
    2^2031 ≤ budget (primes 739) ∧ budget (primes 739) < 2^2032 ∧
    2^2050 ≤ budget (primes 743) ∧ budget (primes 743) < 2^2051 :=
  ⟨checked.1,checked.2.1,checked.2.2.1,checked.2.2.2.1,checked.2.2.2.2.1,checked.2.2.2.2.2.1⟩

private theorem num_formula {p : ℕ} (hp : p.Prime) (large : 5≤p) :
    (numerator p : ℝ) = (p:ℝ)^2-3*p+4 := by
  obtain ⟨k,hk⟩ := hp.odd_of_ne_two (by omega)
  have h : 2*((p-3)/2)+3=p := by omega
  have hr : 2*(((p-3)/2:ℕ):ℝ)+3=p := by exact_mod_cast h
  simp only [numerator,if_neg (show p≠3 by omega),classes,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
  nlinarith only [congrArg (fun x : ℝ => x*p) hr]

private theorem den_formula {p : ℕ} (hp : 1≤p) : (pairs p : ℝ) = p*((p:ℝ)-1) := by
  simp only [pairs,Nat.cast_mul,Nat.cast_sub hp,Nat.cast_one]

private theorem polynomial_pos {x : ℝ} (h : 5≤x) : 0 < x^2-3*x+4 := by
  nlinarith only [sq_nonneg (x-3),h]

private theorem penalty_ge_one {p : ℕ} (hp : p.Prime) (large : 5≤p) : 1≤penalty p := by
  have hv : 5≤(p:ℝ) := by exact_mod_cast large
  rw [penalty,num_formula hp large,den_formula (by omega),le_div_iff₀ (polynomial_pos hv)]
  nlinarith only [hv]

private theorem penalty_anti {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (large : 5≤p)
    (pq : p≤q) : penalty q ≤ penalty p := by
  have a : 5≤(p:ℝ) := by exact_mod_cast large
  have b : (p:ℝ)≤q := by exact_mod_cast pq
  rw [penalty,penalty,num_formula hp large,num_formula hq (large.trans pq),
    den_formula (p:=p) (by omega),den_formula (p:=q) (by omega),
    div_le_div_iff₀ (polynomial_pos (a.trans b)) (polynomial_pos a)]
  have cross : 0≤(p:ℝ)*q-2*p-2*q+2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr a) (sub_nonneg.mpr (a.trans b)),a,b]
  nlinarith only [mul_nonneg (sub_nonneg.mpr b) cross]

/-- There are at most 129 distinct factors at least 5 in the budget, as any
130 such prime squares have a product of at least 2^2050. -/
theorem count_under_budget (S : Finset ℕ) (hs : ∀p∈S, p.Prime ∧ 5≤p)
    (limit : budget S≤2^2048) : S.card≤129 := by
  by_contra! many
  have order := quotientBudget_product_exchange (s:=primes 743) (t:=S)
    (fun p => p^2) (cut:=743^2) (by decide) (by have := checked.2.1; omega)
    (by simp) (fun p h => Nat.pow_le_pow_left (mem_primes.mp (mem_sdiff.mp h).1).2.2 2)
    (by
      intro p h
      obtain ⟨ins,missing⟩ := mem_sdiff.mp h
      obtain ⟨prime,big⟩ := hs p ins
      exact Nat.pow_le_pow_left (le_of_not_gt (fun low => missing (mem_primes.mpr ⟨prime,big,low.le⟩))) 2)
  change budget (primes 743) ≤ budget S at order
  have low := cutoff_facts.2.2.2.2.1
  have tooBig : (2:ℕ)^2048<2^2050 := by decide +kernel
  omega

private theorem largest_penalty (S : Finset ℕ) (hs : ∀p∈S, p.Prime ∧ 5≤p)
    (limit : budget S≤2^2048) : (∏ p∈S, penalty p) ≤ ∏ p∈primes 739, penalty p := by
  have prime : Nat.Prime 739 := by norm_num
  apply quotientBudget_product_exchange (cut:=penalty 739) _
    (penalty_ge_one prime (by decide)) ((count_under_budget S hs limit).trans_eq checked.1.symm)
    (fun p hp => by unfold penalty; positivity)
  · intro p h
    obtain ⟨ins,missing⟩ := mem_sdiff.mp h
    obtain ⟨pp,big⟩ := hs p ins
    exact penalty_anti prime pp (by decide)
      (le_of_not_gt (fun small => missing (mem_primes.mpr ⟨pp,big,small.le⟩)))
  · intro p h
    obtain ⟨pp,big,low⟩ := mem_primes.mp (mem_sdiff.mp h).1
    exact penalty_anti pp prime big low

private theorem ratio_eq (T : Finset ℕ) :
    (∏ p∈T,ratio p) = ((numeratorProduct T:ℕ):ℝ)/((pairProduct T:ℕ):ℝ) := by
  simp only [ratio,numeratorProduct,pairProduct,Nat.cast_prod,prod_div_distrib]

/-- The finite minimum is achieved by the first 129 useful primes. The
prime 3 may be present without changing any local component fraction. -/
theorem minimum (S : Finset ℕ) (hs : ∀p∈S, p.Prime ∧ p≠2) (limit : budget S ≤ 2^2048) :
    (∏ p∈primes 739,ratio p) ≤ ∏ p∈S,ratio p := by
  let T := S.erase 3
  have members (p) (h : p∈T) : p.Prime ∧ 5≤p := by
    obtain ⟨ne,ins⟩ := mem_erase.mp h
    obtain ⟨pp,odd⟩ := hs p ins
    have := pp.two_le
    have h4 : p≠4 := by intro eq; subst eq; exact (by decide : ¬Nat.Prime 4) pp
    exact ⟨pp,by omega⟩
  have bound : budget T ≤ budget S := by
    by_cases h : 3∈S
    · have split := mul_prod_erase S (fun p : ℕ => p^2) h
      change 3^2*budget T=budget S at split
      omega
    · exact (congrArg budget (erase_eq_of_not_mem h)).le
  have same : (∏p∈T,ratio p) = ∏p∈S,ratio p := by
    by_cases h : 3∈S
    · simpa only [show ratio 3=1 by norm_num [ratio,numerator,pairs],one_mul,T]
        using mul_prod_erase S ratio h
    · rw [show T=S from erase_eq_of_not_mem h]
  rw [←same]
  have positive : 0<∏p∈T,penalty p := prod_pos fun p h =>
    zero_lt_one.trans_le (penalty_ge_one (members p h).1 (members p h).2)
  have recip (U : Finset ℕ) : (∏p∈U,penalty p)⁻¹ = ∏p∈U,ratio p := by
    simp only [←prod_inv_distrib,penalty,inv_div,ratio]
  rw [←recip,←recip]
  exact inv_anti₀ positive (largest_penalty T members (bound.trans limit))

/-- Exact integer arithmetic places the attained minimum just above 7.58%. -/
theorem minimum_value :
    (7581413:ℝ)/100000000 < ∏ p∈primes 739,ratio p ∧
    (∏ p∈primes 739,ratio p) < (7581415:ℝ)/100000000 := by
  rw [ratio_eq]
  have pos : 0 < (pairProduct (primes 739):ℝ) := by
    apply Nat.cast_pos.mpr
    exact prod_pos (fun p h => Nat.mul_pos (mem_primes.mp h).1.pos
      (by have := (mem_primes.mp h).2.1; omega))
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) pos]
    simpa only [mul_comm] using (by exact_mod_cast checked.2.2.2.2.2.2.1 :
      (7581413:ℝ)*(pairProduct (primes 739):ℝ)<100000000*(numeratorProduct (primes 739):ℝ))
  · rw [div_lt_div_iff₀ pos (by norm_num)]
    simpa only [mul_comm] using (by exact_mod_cast checked.2.2.2.2.2.2.2.1 :
      (100000000:ℝ)*(numeratorProduct (primes 739):ℝ)<7581415*(pairProduct (primes 739):ℝ))

theorem uniform_floor (S : Finset ℕ) (hs : ∀p∈S, p.Prime ∧ p≠2) (limit : budget S ≤ 2^2048) :
    (1:ℝ)/14 < ∏ p∈S, ((numerator p:ℝ)/pairs p) :=
  (show (1:ℝ)/14<7581413/100000000 by norm_num).trans_le
    (minimum_value.1.le.trans (minimum S hs limit))

end PrimeFactors.GuessModulusBudget
