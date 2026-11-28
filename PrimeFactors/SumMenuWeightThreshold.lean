import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Exact optimal coverage when a budget reaches an entire group of high
weights and can be completed from the next group of equal weights. -/
namespace PrimeFactors.SumMenuWeightThreshold

open Finset
open scoped Classical

/-- Inner labels carry at least the marginal weight, all other labels
carry at most that weight, and the outer shell supplies enough ties. -/
theorem optimal {α : Type*} [DecidableEq α] (weight : α→ℕ) (inner outer : Finset α)
    (B w : ℕ) (inside : inner⊆outer) (lower : inner.card≤B) (upper : B≤outer.card)
    (heavy : ∀ s∈inner, w≤weight s) (cap : ∀ s∉inner, weight s≤w)
    (ties : ∀ s∈outer\inner, weight s=w) :
    IsGreatest {n : ℕ | ∃ S : Finset α, S.card≤B ∧ n=∑ s∈S,weight s}
      ((∑ s∈inner,weight s)+(B-inner.card)*w) := by
  let excess := fun s => weight s-w
  have split : ∑ s∈inner,weight s=inner.card*w+∑ s∈inner,excess s := by
    calc
      _ = ∑ s∈inner,(w+excess s) := sum_congr rfl fun s hs => by
        have le := heavy s hs; dsimp only [excess]; omega
      _ = _ := by simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id]
  constructor
  · have size : B-inner.card≤(outer\inner).card := by
      rw [Finset.card_sdiff inside]; omega
    obtain ⟨T,sub,count⟩ := exists_subset_card_eq size
    have dis : Disjoint inner T := by
      apply disjoint_left.mpr
      intro x xi xt
      exact (mem_sdiff.mp (sub xt)).2 xi
    refine ⟨inner∪T,?_,?_⟩
    · rw [card_union_of_disjoint dis,count]; omega
    · rw [sum_union dis]
      have eq : ∑ x∈T,weight x=T.card*w := by
        calc
          _ = ∑ _x∈T,w := sum_congr rfl fun x hx => ties x (sub hx)
          _ = _ := by simp only [sum_const,nsmul_eq_mul,Nat.cast_id]
      rw [eq,count]
  · rintro _ ⟨S,limit,rfl⟩
    have each : ∀ s, weight s≤w+(if s∈inner then excess s else 0) := by
      intro s
      split_ifs with mem
      · dsimp [excess]; omega
      · simpa using cap s mem
    have clipped : (∑ s∈S,if s∈inner then excess s else 0) ≤ ∑ s∈inner,excess s := by
      rw [←sum_filter]
      exact sum_le_sum_of_subset (fun x hx => (mem_filter.mp hx).2)
    calc
      _ ≤ ∑ s∈S,(w+if s∈inner then excess s else 0) := sum_le_sum fun s _ => each s
      _ ≤ B*w+∑ s∈inner,excess s := by
        rw [sum_add_distrib,sum_const,nsmul_eq_mul]
        exact Nat.add_le_add (Nat.mul_le_mul_right _ limit) clipped
      _ = _ := by have le := Nat.mul_le_mul_right w lower; rw [split,Nat.sub_mul]; omega

end PrimeFactors.SumMenuWeightThreshold
