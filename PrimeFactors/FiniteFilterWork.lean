import Mathlib.Data.List.Count
import Lean.Elab.Tactic.Omega

/-! Scalar work in a sequence of yes-or-no tests. A test is evaluated once
on every position which has survived its predecessors. -/
namespace PrimeFactors.FiniteFilterWork

variable {α : Type*}

def work (xs : List α) : List (α → Bool) → ℕ
  | [] => 0
  | f::fs => xs.length + work (xs.filter f) fs

private theorem commute (xs : List α) (f g : α → Bool) :
    (xs.filter f).filter g = (xs.filter g).filter f := by
  simp only [List.filter_filter]
  simp [Bool.and_comm]

/-- In a fixed window, swapping neighbors preserves all later work.
The preferable first test is the one passing fewer current candidates. -/
theorem swap_iff (xs : List α) (f g : α → Bool) (rest : List (α → Bool)) :
    work xs (f::g::rest) ≤ work xs (g::f::rest) ↔
      (xs.filter f).length ≤ (xs.filter g).length := by
  simp only [work,commute xs f g]
  omega

/-- Exact comparison, including when both tests pass the same number. -/
theorem swap_cost (xs : List α) (f g : α → Bool) (rest : List (α → Bool)) :
    work xs (f::g::rest) + (xs.filter g).length =
      work xs (g::f::rest) + (xs.filter f).length := by
  simp only [work,commute xs f g]
  omega

end PrimeFactors.FiniteFilterWork
