import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic

/-! The sharp constant for the number of divisor orientations in a common
weighted Fermat trace test, scaled by the fourth root of the multiplier. -/

namespace PrimeFactors.MultiplierDivisorReach
open Finset

private def peak : ℕ → ℕ
  | 2 => 5
  | 3 => 3
  | 5 => 2
  | 7 | 11 | 13 => 1
  | _ => 0

private def exceptional : Finset ℕ := {2,3,5,7,11,13}

private theorem peak_zero {p : ℕ} (h : p ∉ exceptional) : peak p = 0 := by
  simp [exceptional] at h
  unfold peak
  split <;> simp_all

private theorem local_bound {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (e+1)^4 * p^(peak p) ≤ p^e * (peak p+1)^4 := by
  by_cases small : p<16
  · have base : ∀ j : Fin 16, ∀ i : Fin 7, j.val.Prime →
        (i.val+1)^4 * j.val^(peak j.val) ≤ j.val^i.val * (peak j.val+1)^4 := by
      decide +kernel
    induction e with
    | zero => exact base ⟨p,small⟩ 0 hp
    | succ e ih =>
      by_cases short : e+1<7
      · exact base ⟨p,small⟩ ⟨e+1,short⟩ hp
      · obtain ⟨d,hd⟩ : ∃ d, e=6+d := ⟨e-6,by omega⟩
        have step : (e+1+1)^4 ≤ 2*(e+1)^4 := by rw [hd]; nlinarith only [Nat.zero_le d, Nat.zero_le (d^2), Nat.zero_le (d^3), Nat.zero_le (d^4)]
        calc
          _ ≤ (2*(e+1)^4)*p^(peak p) := Nat.mul_le_mul_right _ step
          _ ≤ p*(p^e*(peak p+1)^4) := by
            rw [Nat.mul_assoc]
            exact Nat.mul_le_mul hp.two_le ih
          _ = _ := by rw [pow_succ]; ring
  · have zero : peak p=0 := peak_zero (by intro h; simp [exceptional] at h; omega)
    simp only [zero,pow_zero, mul_one, zero_add,one_pow]
    have exp : e+1≤2^e := by
      induction e with
      | zero => decide
      | succ e ih => rw [pow_succ]; omega
    calc
      _ ≤ (2^e)^4 := Nat.pow_le_pow_left exp _
      _ = 16^e := by rw [←pow_mul,Nat.mul_comm,pow_mul]; rfl
      _ ≤ p^e := Nat.pow_le_pow_left (by omega) _

/-- The best possible fourth-power bound. Equality is attained at 21,621,600. -/
theorem sharp_bound {n : ℕ} (hn : n≠0) :
    n.divisors.card^4 * 21621600 ≤ n*576^4 := by
  let s := n.primeFactors ∪ exceptional
  have extend (f : ℕ → ℕ) (orig : Finset ℕ) (sub : orig ⊆ s)
      (outside : ∀ p ∈ s, p ∉ orig → f p = 1) :
      ∏ p ∈ s, f p = ∏ p ∈ orig, f p := (prod_subset sub outside).symm
  have zero {p : ℕ} (h : p ∉ n.primeFactors) : n.factorization p = 0 :=
    Finsupp.not_mem_support_iff.mp h
  have fac : ∏ p ∈ s, p^(n.factorization p)=n := by
    rw [extend _ n.primeFactors subset_union_left (fun p _ h => by simp [zero h])]
    exact Nat.factorization_prod_pow_eq_self hn
  have tau : ∏ p ∈ s, (n.factorization p+1)^4 = n.divisors.card^4 := by
    rw [extend _ n.primeFactors subset_union_left (fun p _ h => by simp [zero h]),
      prod_pow, ← Nat.card_divisors hn]
  have weight : ∏ p ∈ s, p^(peak p) = 21621600 := by
    rw [extend _ exceptional subset_union_right (fun p _ h => by simp [peak_zero h])]
    decide +kernel
  have count : ∏ p ∈ s, (peak p+1)^4 = 576^4 := by
    rw [extend _ exceptional subset_union_right (fun p _ h => by simp [peak_zero h])]
    decide +kernel
  have prod := Finset.prod_le_prod' (s:=s) (fun p hp => local_bound (p:=p)
    (by
      rcases mem_union.mp hp with h|h
      · exact Nat.prime_of_mem_primeFactors h
      · simp [exceptional] at h
        rcases h with h|h|h|h|h|h <;> subst p <;> decide) (n.factorization p))
  simpa only [prod_mul_distrib,tau,fac,weight,count] using prod

theorem peak_attained : (21621600:ℕ).divisors.card = 576 := by
  rw [show (21621600:ℕ)=2^5*3^3*5^2*7*11*13 by decide]
  repeat
    rw [(show Nat.Coprime _ _ from by decide +kernel).card_divisors_mul]
  decide +kernel

theorem fourth_power_bound {n : ℕ} (hn : n≠0) : n.divisors.card^4 < 9^4*n := by
  have h := sharp_bound hn
  have strict := Nat.mul_lt_mul_of_pos_right (by decide : 576^4 < 9^4*21621600) (Nat.pos_of_ne_zero hn)
  exact Nat.lt_of_mul_lt_mul_right (by nlinarith only [h,strict] : n.divisors.card^4*21621600 < 9^4*n*21621600)

end PrimeFactors.MultiplierDivisorReach
