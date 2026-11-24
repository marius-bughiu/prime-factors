import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace PrimeFactors

private theorem dyadic_quotients (C K : ℕ) :
    (∑ j ∈ Finset.range K, C / 2^(j+1)) + C / 2^K ≤ C := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ 2 k, ← Nat.div_div_eq_div_mul]
    omega

private theorem dyadic_powers (K : ℕ) :
    (∑ j ∈ Finset.range K, 2^(j+1)) + 2 = 2*2^K := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,pow_succ 2 k]
    omega

private theorem dyadic_level_term (C j : ℕ) :
    2^j * (4*(C/4^j+1)) ≤ 4*(C/2^j) + 4*2^j := by
  have quotient : 2^j*(C/4^j) ≤ C/2^j := by
    apply (Nat.le_div_iff_mul_le (pow_pos (by decide : 0 < 2) j)).mpr
    calc 2^j*(C/4^j)*2^j = (C/4^j)*(2*2)^j := by rw [mul_pow]; ring
      _ ≤ C := Nat.div_mul_le_self _ _
  nlinarith only [quotient]

/-- Aggregate the divisibility levels of a dyadic square-root bound.
The zeroth level contributes one per candidate. The higher levels include
the rounding cost from the possible incomplete congruence periods. -/
theorem dyadic_level_sum_bound (s : Finset ℕ) (a : ℕ → ℕ) (C K : ℕ)
    (card : s.card ≤ C)
    (levels : ∀ j, 1 ≤ j → j ≤ K → (s.filter (fun x => 4^j ∣ a x)).card ≤ 4*(C/4^j+1)) :
    (∑ x ∈ s, ∑ j ∈ Finset.range (K+1), if 4^j ∣ a x then 2^j else 0) ≤ 5*C+8*2^K := by
  rw [Finset.sum_comm,Finset.sum_range_succ']
  have per (j : ℕ) (hj : j ∈ Finset.range K) :
      (∑ x ∈ s, if 4^(j+1) ∣ a x then 2^(j+1) else 0) ≤ 4*(C/2^(j+1)) + 4*2^(j+1) := by
    calc
      _ = 2^(j+1)*(s.filter (fun x => 4^(j+1) ∣ a x)).card := by
        rw [← Finset.sum_filter]; simp [Nat.mul_comm]
      _ ≤ 2^(j+1)*(4*(C/4^(j+1)+1)) :=
        Nat.mul_le_mul_left _ (levels (j+1) (by omega) (Finset.mem_range.mp hj))
      _ ≤ _ := dyadic_level_term C (j+1)
  have bound := Finset.sum_le_sum per
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum] at bound
  have quo : (∑ j ∈ Finset.range K, C / 2^(j+1)) ≤ C :=
    (Nat.le_add_right _ _).trans (dyadic_quotients C K)
  have pw := dyadic_powers K
  simp only [pow_zero,one_dvd,if_true,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_one]
  omega

end PrimeFactors
