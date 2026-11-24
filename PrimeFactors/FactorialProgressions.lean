import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

namespace PrimeFactors.FactorialProgressions

variable {M : Type*} [CommMonoid M]

/-- One cycle of a translated wheel, with an arbitrary finite set of offsets. -/
noncomputable def cycle (f : ℕ → M) (base wheel : ℕ) (offsets : Finset ℕ) (i : ℕ) : M :=
  ∏ r ∈ offsets, f (base + wheel*i + r)

/-- Index j of the progression of products, each covering h complete cycles. -/
noncomputable def block (f : ℕ → M) (base wheel : ℕ) (offsets : Finset ℕ) (h j : ℕ) : M :=
  ∏ s ∈ Finset.range h, cycle f base wheel offsets (h*j+s)

/-- Doubling the block length multiplies the two neighboring old block values. -/
theorem block_double (f : ℕ → M) (base wheel : ℕ) (offsets : Finset ℕ) (h j : ℕ) :
    block f base wheel offsets (2*h) j =
      block f base wheel offsets h (2*j) * block f base wheel offsets h (2*j+1) := by
  unfold block
  rw [show 2*h = h+h by omega, Finset.prod_range_add]
  congr 1 <;> apply Finset.prod_congr rfl <;> intro k _ <;> congr 1 <;> ring

/-- The product of s full blocks covers precisely h*s consecutive cycles. -/
theorem full_blocks (f : ℕ → M) (base wheel : ℕ) (offsets : Finset ℕ) (h s : ℕ) :
    (∏ j ∈ Finset.range s, block f base wheel offsets h j) =
      ∏ i ∈ Finset.range (h*s), cycle f base wheel offsets i := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.prod_range_succ, ih, Nat.mul_succ, Finset.prod_range_add]
    rfl

/-- The full blocks and the direct tail cover all c cycles exactly. -/
theorem blocks_with_tail (f : ℕ → M) (base wheel : ℕ) (offsets : Finset ℕ) (h c : ℕ) :
    (∏ j ∈ Finset.range (c/h), block f base wheel offsets h j) *
        (∏ s ∈ Finset.range (c%h), cycle f base wheel offsets (h*(c/h)+s)) =
      ∏ i ∈ Finset.range c, cycle f base wheel offsets i := by
  rw [full_blocks, ← Finset.prod_range_add, Nat.div_add_mod]

end PrimeFactors.FactorialProgressions
