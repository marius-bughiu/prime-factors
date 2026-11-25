import PrimeFactors.ClassNumberWindow
import PrimeFactors.Certificate
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors.SharedClassOrders

/-- Consecutive hits in any positive-exponent search reveal the order,
without factoring the exponent of either hit. -/
theorem consecutive_hits {G : Type*} [Group G] [Fintype G] (x : G) {a b : ℕ}
    (ab : a < b) (left : x^a=1) (right : x^b=1)
    (gap : ∀ k, a<k → k<b → x^k ≠ 1) : orderOf x = b-a := by
  have le : orderOf x ≤ b-a := Nat.le_of_dvd (by omega)
    (Nat.dvd_sub (orderOf_dvd_of_pow_eq_one right) (orderOf_dvd_of_pow_eq_one left))
  by_contra ne
  have pos := orderOf_pos x
  exact gap (a+orderOf x) (by omega) (by omega) (by rw [pow_add, left, one_mul, pow_orderOf_eq_one])

/-- A certified divisor of the class number grows by the order of the
powered seed. The new divisor kills the original seed. -/
theorem enlarge {G : Type*} [Group G] (x : G) {D H : ℕ} (div : D ∣ H)
    (kills : x^H = 1) : D * orderOf (x^D) ∣ H ∧ x^(D*orderOf (x^D)) = 1 := by
  obtain ⟨k,rfl⟩ := div
  rw [pow_mul] at kills
  exact ⟨Nat.mul_dvd_mul_left D (orderOf_dvd_of_pow_eq_one kills), by rw [pow_mul,pow_orderOf_eq_one]⟩

/-- One hit in a certified quotient window gives the entire group-size
target, even if the seed itself has much smaller order. -/
theorem unique_hit {G : Type*} [Group G] (x : G) {D H lo hi e : ℕ} (div : D ∣ H)
    (kills : x^H=1) (bounds : lo ≤ H/D ∧ H/D ≤ hi)
    (unique : ∀ k, lo≤k → k≤hi → (x^D)^k=1 → k=e) : H=D*e := by
  have h := Nat.mul_div_cancel' div
  have hit : (x^D)^(H/D)=1 := by rw [← pow_mul,h,kills]
  exact h.symm.trans (congrArg (D*·) (unique _ bounds.1 bounds.2 hit))

/-- For a pivot with maximal 2-power order, every seed outside its cyclic
subgroup supplies a second involution. Only this one pivot is needed. -/
theorem pivot {G : Type*} [CommGroup G] (x : G) (a : ℕ) (ann : x^(2^(a+1))=1)
    (b : ℕ) (bound : b≤a) (z : G) (outside : z ∉ Subgroup.zpowers x)
    (killed : z^(2^(b+1))=1) :
    ∃ v : G, v≠1 ∧ v^2=1 ∧ v≠x^(2^a) := by
  induction b generalizing z with
  | zero =>
    refine ⟨z, ?_, by simpa using killed, ?_⟩
    · rintro rfl; exact outside (Subgroup.one_mem _)
    · rintro rfl; exact outside ((Subgroup.zpowers x).pow_mem (Subgroup.mem_zpowers x) _)
  | succ b ih =>
    by_cases trivial : z^(2^(b+1))=1
    · exact ih (by omega) z outside trivial
    by_cases same : z^(2^(b+1)) = x^(2^a)
    · have idx : b+1+(a-(b+1))=a := by omega
      have step := cancel_shared_involution x z (b+1) (a-(b+1))
        (by simpa only [idx] using same) (by simpa only [idx] using ann) outside
      exact ih (by omega) _ step.2 step.1
    · exact ⟨_,trivial,by simpa only [←pow_mul, ←pow_succ] using killed,same⟩

/-- Multiplying the two ideal-lattice generators (w-t),(w-u) in the
quadratic order with w²=s*w-k gives the coordinates used in composition. -/
theorem ideal_generator {R : Type*} [CommRing R] (w s k t u : R) (rel : w^2=s*w-k) :
    (w-t)*(w-u)=(t*u-k)+(s-t-u)*w := by linear_combination rel

theorem example_24511 : ExactFactorization 24511 [127,193] := by norm_num [ExactFactorization]

end PrimeFactors.SharedClassOrders
