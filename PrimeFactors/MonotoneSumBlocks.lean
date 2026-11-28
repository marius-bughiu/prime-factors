import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! Counting possible block indices and sum values for a monotone predictor. -/

namespace PrimeFactors.MonotoneSumBlocks

open Finset

/-- Use both ends of each input block to enclose its possible nonnegative
sum values. Block indices distinguish cells even when the intervals overlap. -/
noncomputable def cells (g : ℕ → ℕ) (B W E : ℕ) : Finset (ℕ×ℕ) :=
  (range B).biUnion fun b => {b} ×ˢ Icc (g (b*W)-E) (g ((b+1)*W)+E)

theorem mem_cells (g : ℕ → ℕ) (B W E b S : ℕ) :
    (b,S)∈cells g B W E ↔ b<B ∧ g (b*W)-E≤S ∧ S≤g ((b+1)*W)+E := by
  simp only [cells,mem_biUnion,mem_range,mem_product,mem_singleton,mem_Icc]
  constructor
  · rintro ⟨i,hi,rfl,lo,up⟩
    exact ⟨hi,lo,up⟩
  · rintro ⟨hb,lo,up⟩
    exact ⟨b,hb,rfl,lo,up⟩

theorem mem_of_estimate {g : ℕ → ℕ} (mono : Monotone g) {B W E b N S : ℕ}
    (block : b<B) (left : b*W≤N) (right : N≤(b+1)*W)
    (low : g N-E≤S) (high : S≤g N+E) : (b,S)∈cells g B W E :=
  (mem_cells ..).mpr ⟨block,(Nat.sub_le_sub_right (mono left) E).trans low,
    high.trans (Nat.add_le_add_right (mono right) E)⟩

theorem mem_quotient {g : ℕ → ℕ} (mono : Monotone g) {B W E N S : ℕ}
    (width : 0<W) (size : N<B*W) (low : g N-E≤S) (high : S≤g N+E) :
    (N/W,S)∈cells g B W E := by
  apply mem_of_estimate mono ((Nat.div_lt_iff_lt_mul width).mpr size) (Nat.div_mul_le_self ..)
    _ low high
  simpa only [Nat.succ_mul] using (Nat.lt_div_mul_add (a:=N) width).le

theorem card_eq_sum (g : ℕ → ℕ) (B W E : ℕ) :
    (cells g B W E).card=∑ b∈range B,(Icc (g (b*W)-E) (g ((b+1)*W)+E)).card := by
  unfold cells
  rw [card_biUnion]
  · simp only [card_product,card_singleton,one_mul]
  · intro i _ j _ ne
    apply disjoint_left.mpr
    intro x hx hy
    exact ne ((mem_singleton.mp (mem_product.mp hx).1).symm.trans
      (mem_singleton.mp (mem_product.mp hy).1))

/-- Natural-number subtraction clips a block at zero exactly when its
left endpoint lies below E. Adding back those clipped lengths gives the
full telescoping count. -/
theorem card_accounting (g : ℕ → ℕ) (mono : Monotone g) (B W E : ℕ) :
    (cells g B W E).card + ∑ b∈range B,(E-g (b*W)) =
      g (B*W)-g 0+(2*E+1)*B := by
  rw [card_eq_sum]
  induction B with
  | zero => simp
  | succ B ih =>
    rw [sum_range_succ,sum_range_succ,Nat.card_Icc,Nat.mul_succ (2*E+1)]
    have start : g 0≤g (B*W) := mono (Nat.zero_le _)
    have stop : g (B*W)≤g ((B+1)*W) := mono (Nat.mul_le_mul_right W (Nat.le_succ B))
    omega

theorem card_le (g : ℕ → ℕ) (mono : Monotone g) (B W E : ℕ) :
    (cells g B W E).card≤g (B*W)-g 0+(2*E+1)*B :=
  (Nat.le_add_right ..).trans_eq (card_accounting g mono B W E)

end PrimeFactors.MonotoneSumBlocks
