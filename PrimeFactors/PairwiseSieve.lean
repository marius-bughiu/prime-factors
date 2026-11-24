import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- The centered second moment of a Bernoulli reading. The indicator
may be expressed algebraically by its pointwise idempotence. -/
theorem sieve_indicator_variance {α : Type*} (population : Finset α) (w f : α → ℝ)
    (p : ℝ) (mass : ∑ x ∈ population, w x = 1) (mean : ∑ x ∈ population, w x * f x = p)
    (binary : ∀ x ∈ population, f x ^ 2 = f x) :
    ∑ x ∈ population, w x * (f x - p)^2 = p - p^2 := by
  calc
    _ = ∑ x ∈ population, ((w x * f x) * (1-2*p) + w x * p^2) := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        _ = w x * (f x^2 - 2*p*f x + p^2) := by ring
        _ = _ := by rw [binary x hx]; ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, mean, mass]; ring

/-- A weighted population and finitely many rejection tests. Pairwise
uncorrelated tests already bound the weight with no rejections. -/
theorem pairwise_sieve_miss {α ι : Type*} (population : Finset α) (tests : Finset ι)
    (w : α → ℝ) (score : ι → α → ℝ) (rate : ι → ℝ)
    (wpos : ∀ x ∈ population, 0 ≤ w x)
    (variance : ∀ i ∈ tests, ∑ x ∈ population, w x * (score i x - rate i)^2 ≤ rate i)
    (independent : ∀ i ∈ tests, ∀ j ∈ tests, i ≠ j →
      ∑ x ∈ population, w x * (score i x - rate i) * (score j x - rate j) = 0)
    (miss : Finset α) (sub : miss ⊆ population)
    (zero : ∀ x ∈ miss, ∀ i ∈ tests, score i x = 0) :
    (∑ x ∈ miss, w x) * (∑ i ∈ tests, rate i)^2 ≤ ∑ i ∈ tests, rate i := by
  classical
  let f := fun i x => score i x - rate i
  have bound (i) (hi : i ∈ tests) :
      (∑ j ∈ tests, ∑ x ∈ population, w x * f i x * f j x) ≤ rate i := by
    rw [Finset.sum_eq_single i]
    · simpa only [f, pow_two, mul_assoc] using variance i hi
    · intro j hj hji
      exact independent i hi j hj (Ne.symm hji)
    · exact fun h => (h hi).elim
  have expand (x) : w x * (∑ i ∈ tests, f i x)^2 =
      ∑ i ∈ tests, ∑ j ∈ tests, w x * f i x * f j x := by
    simp only [pow_two, ← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
  have all : (∑ x ∈ population, w x * (∑ i ∈ tests, f i x)^2) ≤ ∑ i ∈ tests, rate i := by
    simp_rw [expand]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.sum_comm]
    exact bound i hi
  calc
    _ = ∑ x ∈ miss, w x * (∑ i ∈ tests, f i x)^2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have off : (∑ i ∈ tests, f i x) = -(∑ i ∈ tests, rate i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i hi => by simp [f, zero x hx i hi]
      rw [off, neg_sq]
    _ ≤ _ := (Finset.sum_le_sum_of_subset_of_nonneg sub fun x hx _ =>
      mul_nonneg (wpos x hx) (sq_nonneg _)).trans all

end PrimeFactors
