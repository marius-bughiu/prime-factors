import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PrimeFactors.QuarticPrimeCover

open Finset

/-- Union bound over tuples in a common finite group. Tests for different
levels may be arbitrarily correlated inside any one group element. -/
theorem exists_cover {A G : Type*} [Fintype G] [Nonempty G] (levels : Finset A)
    (pass : A → Finset G) (k : ℕ)
    (density : ∀ a ∈ levels, 4*(pass a).card ≤ 3*Fintype.card G)
    (budget : levels.card*3^k < 4^k) :
    ∃ tests : Fin k → G, ∀ a ∈ levels, ∃ i, tests i ∉ pass a := by
  classical
  let bad (a : A) := Fintype.piFinset (fun _ : Fin k => pass a)
  have localBound {a : A} (ha : a ∈ levels) :
      4^k * (bad a).card ≤ 3^k * (Fintype.card G)^k := by
    rw [show (bad a).card=(pass a).card^k from Fintype.card_piFinset_const ..,
      ← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (density a ha) k
  have bound : 4^k * (levels.biUnion bad).card ≤
      levels.card * 3^k * (Fintype.card G)^k := calc
    _ ≤ 4^k * ∑ a ∈ levels, (bad a).card := Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ a ∈ levels, 4^k*(bad a).card := Finset.mul_sum ..
    _ ≤ ∑ _ ∈ levels, 3^k * (Fintype.card G)^k := sum_le_sum fun _ ha => localBound ha
    _ = _ := by simp [mul_assoc]
  have strict := bound.trans_lt (Nat.mul_lt_mul_of_pos_right budget
    (pow_pos Fintype.card_pos k))
  have small : (levels.biUnion bad).card < (univ : Finset (Fin k → G)).card := by
    simp only [card_univ, Fintype.card_fun, Fintype.card_fin]
    exact Nat.lt_of_mul_lt_mul_left strict
  obtain ⟨tests,_,missing⟩ := exists_mem_not_mem_of_card_lt_card small
  refine ⟨tests, fun a ha => ?_⟩
  by_contra! every
  exact missing (mem_biUnion.mpr ⟨a,ha,Fintype.mem_piFinset.mpr every⟩)

theorem fresh_budgets :
    25487*3^36 < (4:ℕ)^36 ∧ 23967979*3^60 < (4:ℕ)^60 := by decide +kernel

/-- Every prescribed finite prime list can miss a rational-root-free quartic.
All divisors of M see the residue 1, while M⁴+1 is strictly between fourth powers. -/
theorem fixed_list {M : ℕ} (positive : 0<M) :
    (∀ p : ℕ, p ∣ M → p ∣ M^4) ∧ ¬∃ r : ℕ, r^4=M^4+1 := by
  refine ⟨fun _ divides => divides.trans (dvd_pow_self _ (by decide : 4≠0)), ?_⟩
  rintro ⟨r, root⟩
  have greater : M < r := by
    by_contra! small
    have h := Nat.pow_le_pow_left small 4
    omega
  have bound := Nat.pow_le_pow_left (Nat.succ_le_of_lt greater) 4
  have hp : 0 < M^2 := pow_pos positive 2
  nlinarith only [root,bound,hp,pow_nonneg (Nat.zero_le M) 3,positive]

end PrimeFactors.QuarticPrimeCover
