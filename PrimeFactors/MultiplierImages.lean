import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- Scaling an honest collision and translating its exponent preserves the
match. Injectivity of raising arbitrary group elements to w is not assumed. -/
theorem multiplierImage_collision {G : Type*} [Monoid G] (α v : G) {i : ℕ}
    (w c : ℕ) (hit : α^i = v) : α^(c+w*i) = α^c*v^w := by
  rw [Nat.mul_comm w i, pow_add, pow_mul, hit]

/-- The public local multiplier bσ makes the leading coefficient b/σ square. -/
theorem multiplierImage_align {R : Type*} [CommRing R] (b : R) (σ : Rˣ) :
    (b*(σ : R))*(b*(↑σ⁻¹ : R)) = b^2 := by
  calc
    _ = b^2*((σ : R)*(↑σ⁻¹ : R)) := by ring
    _ = _ := by rw [σ.mul_inv, mul_one]

/-- Stationarity identifies the leading class with b/σ and the weighted
product with (bσ)². Flipping a CRT square root preserves stationarity. -/
theorem multiplierImage_stationary {R : Type*} [CommRing R] (a b n : R) (σ : Rˣ)
    (stat : b*(σ : R)^2 = a*n) :
    a*n*(↑σ⁻¹ : R)^3 = b*(↑σ⁻¹ : R) ∧ a*b*n = (b*(σ : R))^2 ∧
      b*(-(σ : R))^2 = a*n := by
  constructor
  · calc
      _ = b*((σ : R)*(↑σ⁻¹ : R))^2*(↑σ⁻¹ : R) := by rw [← stat]; ring
      _ = _ := by simp
  constructor
  · calc
      _ = b*(a*n) := by ring
      _ = _ := by rw [← stat]; ring
  · simpa using stat

/-- Count labels in an interval satisfying two simultaneous progression
constraints. Their common spacing includes the full lcm of the multipliers. -/
theorem multiplierImage_train_count (points : Finset ℕ) (lo H M u v a b : ℕ)
    (range : ∀ x ∈ points, lo ≤ x ∧ x ≤ lo+H*min u v)
    (left : ∀ x ∈ points, x ≡ a [MOD M*u])
    (right : ∀ x ∈ points, x ≡ b [MOD M*v]) :
    points.card ≤ H*min u v / (M*Nat.lcm u v)+1 := by
  let step := M*Nat.lcm u v
  let key (x : ℕ) := (x-lo)/step
  let indices := Finset.range (H*min u v/step+1)
  have into : ∀ x ∈ points, key x ∈ indices := by
    intro x hx
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (show x-lo ≤ H*min u v by
      have := (range x hx).2
      omega))
  have inj : Set.InjOn key (points : Set ℕ) := by
    intro x hx y hy same
    have mod := Nat.mod_lcm ((left x hx).trans (left y hy).symm)
      ((right x hx).trans (right y hy).symm)
    rw [Nat.lcm_mul_left] at mod
    have small : x-lo ≡ y-lo [MOD step] := by
      apply Nat.ModEq.add_left_cancel (Nat.ModEq.refl lo)
      simpa only [Nat.add_sub_of_le (range x hx).1, Nat.add_sub_of_le (range y hy).1] using mod
    change (x-lo) % step = (y-lo) % step at small
    change (x-lo)/step = (y-lo)/step at same
    have decomposition := Nat.mod_add_div (x-lo) step
    rw [small,same,Nat.mod_add_div] at decomposition
    have := (range x hx).1
    have := (range y hy).1
    omega
  simpa [indices,step] using Finset.card_le_card_of_injOn key into inj

/-- Finite second-moment bound for the union of arbitrary translated
progressions. Applying it after fixing the CRT residue permits a different
multiplier and a different clipped interval in every row. -/
theorem multiplierImage_union_moment {ι β : Type*} [DecidableEq β] (rows : Finset ι)
    (F : ι → Finset β) :
    (∑ j ∈ rows, (F j).card)^2 ≤ (rows.biUnion F).card *
      ∑ j ∈ rows, ∑ k ∈ rows, (F j ∩ F k).card := by
  classical
  let B := rows.biUnion F
  let I (x : β) (j : ι) : ℕ := if x ∈ F j then 1 else 0
  let hits (x : β) := ∑ j ∈ rows, I x j
  have count (C : Finset β) (hC : C ⊆ B) :
      (∑ x ∈ B, if x ∈ C then 1 else 0) = C.card := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hC, ← Finset.card_eq_sum_ones]
  have total : ∑ x ∈ B, hits x = ∑ j ∈ rows, (F j).card := by
    dsimp [hits,I]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j hj => count _ (Finset.subset_biUnion_of_mem F hj)
  have second : ∑ x ∈ B, (hits x)^2 = ∑ j ∈ rows, ∑ k ∈ rows, (F j ∩ F k).card := by
    simp only [hits,pow_two,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    convert count (F j ∩ F k) (Finset.inter_subset_left.trans (Finset.subset_biUnion_of_mem F hj)) using 1
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : x ∈ F j <;> by_cases t : x ∈ F k <;> simp [I,h,t]
  rw [← total, ← second]
  simpa [B] using Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) B (fun _ => 1) hits

private def multiplierExampleSquare (p x : ℕ) : Bool :=
  (List.range p).any fun z => x%p == z^2%p

private def multiplierExampleBabies : Finset ℕ :=
  (Finset.range (6*77)).filter fun e =>
    multiplierExampleSquare 7 e && multiplierExampleSquare 11 e &&
      [1,2,3,6].any (fun w => e%w == 0 && decide (e < w*77))

/-- The four multipliers attain all four sign signatures at 7 and 11. Their
output table takes 60 entries even when the individual spans and exact
divisibility are both used. The ordinary translated table takes 40. -/
theorem multiplierImage_example :
    ([1,2,3,6].map fun w => (multiplierExampleSquare 7 w,multiplierExampleSquare 11 w)) =
      [(true,true),(true,false),(false,true),(false,false)] ∧
    multiplierExampleBabies.card = 60 ∧
    ((Finset.range 77).filter fun i =>
      (multiplierExampleSquare 7 i || multiplierExampleSquare 7 (8-i%7)) &&
      (multiplierExampleSquare 11 i || multiplierExampleSquare 11 (12-i%11))).card = 40 := by
  decide +kernel

end PrimeFactors
