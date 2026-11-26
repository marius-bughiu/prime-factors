import PrimeFactors.ShortPascalRow
import Mathlib.Tactic

/-! Smaller-prime windows in a public bin of products. The per-cell estimates
in `population` are supplied by prime counting on intervals. The summation,
rounding and candidate-interval geometry are independent of those estimates. -/

namespace PrimeFactors.LowerHalfPrimeBins

open Finset

private def scale : ℕ := 10^12

/-- Fixed-point reciprocal weights. Upper weights round strictly upwards. -/
private def weight (upper : Bool) (j : ℕ) : ℕ :=
  scale / j + if upper then 1 else 0

private def accumulated (upper : Bool) (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => accumulated upper start i + weight upper (start+i)

private theorem accumulated_eq (upper : Bool) (start n : ℕ) :
    accumulated upper start n = ∑ i ∈ range n, weight upper (start+i) := by
  induction n with
  | zero => simp [accumulated]
  | succ n ih => rw [accumulated, ih, sum_range_succ]

set_option maxRecDepth 4096 in
private theorem weights_checked :
    accumulated false 1026 211 = 187104496989 ∧
    accumulated true 1236 213 = 159052784456 := by decide +kernel

private theorem lower_weight {cost price d : ℕ} (hit : cost ≤ d*price) :
    weight false d * cost ≤ scale*price := by
  have bound : weight false d * d ≤ scale := by
    simpa [weight] using Nat.div_mul_le_self scale d
  calc
    _ ≤ weight false d * (d*price) := Nat.mul_le_mul_left _ hit
    _ = (weight false d*d)*price := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ bound

private theorem upper_weight {cost price d : ℕ} (pos : 0<d) (hit : d*price ≤ cost) :
    scale*price ≤ weight true d * cost := by
  have bound : scale ≤ weight true d * d := by
    have := Nat.lt_mul_div_succ scale pos
    simpa [weight, Nat.mul_comm] using this.le
  calc
    _ ≤ (weight true d*d)*price := Nat.mul_le_mul_right _ bound
    _ = weight true d*(d*price) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hit

/-- Convert the prime-count discrepancy and the smooth mass bounds to the
two rates used for both coordinates of every cell. -/
theorem interval_rates {length smooth count error : ℝ}
    (lo : length/710 ≤ smooth) (hi : smooth ≤ length/709)
    (discrepancy : |count-smooth| ≤ error) (wide : 710000*error ≤ length) :
    999*length/710000 ≤ count ∧ count ≤ 1001*length/709000 := by
  obtain ⟨left,right⟩ := abs_le.mp discrepancy
  constructor <;> linarith

/-- At B=2^1023 the squared RH discrepancy fits even at the minimum
partner width 2^538. The unconditional discrepancy fits at width 2^1002.
The analytic estimates for the discrepancies themselves are external. -/
theorem discrepancy_constants :
    (710000*100)^2*2^1023 < (2^538 : ℕ)^2 ∧
    710000*4*2^1023 < (10^13 : ℕ)*2^1002 := by decide +kernel

/-- Given the lower and upper prime-pair counts per cell, the full lower side
has over 53.8824% of the population. The lower cells may omit pairs and the
upper cells may overcount. All endpoints are indexed in units of B/1024. -/
theorem population {H low high : ℕ} (hH : 0<H) (left right : ℕ → ℕ)
    (lowerCells : ∀ i<211, 999^2*H ≤ (1026+i)*(710000^2*left i))
    (upperCells : ∀ i<213, (1236+i)*(709000^2*right i) ≤ 1001^2*H)
    (below : ∑ i ∈ range 211, left i ≤ low)
    (above : high ≤ ∑ i ∈ range 213, right i) :
    538824*(low+high) < 1000000*low := by
  have a : (∑ i ∈ range 211, weight false (1026+i))*(999^2*H) ≤
      scale*(710000^2*low) := calc
    _ = ∑ i ∈ range 211, weight false (1026+i)*(999^2*H) := sum_mul ..
    _ ≤ ∑ i ∈ range 211, scale*(710000^2*left i) :=
      sum_le_sum fun i hi => lower_weight (lowerCells i (mem_range.mp hi))
    _ = scale*(710000^2*∑ i ∈ range 211, left i) := by simp only [mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ below)
  have b : scale*(709000^2*high) ≤
      (∑ i ∈ range 213, weight true (1236+i))*(1001^2*H) := calc
    _ ≤ scale*(709000^2*∑ i ∈ range 213, right i) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ above)
    _ = ∑ i ∈ range 213, scale*(709000^2*right i) := by simp only [mul_sum]
    _ ≤ ∑ i ∈ range 213, weight true (1236+i)*(1001^2*H) :=
      sum_le_sum fun i hi => upper_weight (by omega) (upperCells i (mem_range.mp hi))
    _ = _ := (sum_mul ..).symm
  rw [← accumulated_eq,weights_checked.1] at a
  rw [← accumulated_eq,weights_checked.2] at b
  unfold scale at a b
  linarith only [a,b,hH]

/-- The two disjoint equal-width windows give odds above four to three. -/
theorem separated_windows {H low high : ℕ} (hH : 0<H)
    (lo : 999^2*H ≤ 66*(710000^2*low))
    (hi : 89*(709000^2*high) ≤ 1001^2*H) : 4*high < 3*low := by
  linarith only [hH,lo,hi]

/-- Reflection around the cutoff gives an injection into the other half of
the same feasible interval. For odd candidates the reflection is about T,
and for all integers it is about T+1/2. -/
theorem position_counts {L T U : ℕ} (room : 2*T+1 ≤ L+U) (even : T%2=0) :
    ((Icc L U).filter (fun i => i≤T)).card ≤
      ((Icc L U).filter (fun i => T < i)).card ∧
    ((Icc L U).filter (fun i => i≤T ∧ i%2=1)).card ≤
      ((Icc L U).filter (fun i => T < i ∧ i%2=1)).card := by
  constructor
  · apply card_le_card_of_injOn (fun x : ℕ => 2*T+1-x)
    · intro x hx
      simp only [mem_coe, mem_filter, mem_Icc] at hx ⊢
      omega
    · intro x hx y hy eq
      simp only [mem_coe, mem_filter, mem_Icc] at hx hy
      dsimp at eq
      omega
  · apply card_le_card_of_injOn (fun x : ℕ => 2*T-x)
    · intro x hx
      simp only [mem_coe, mem_filter, mem_Icc] at hx ⊢
      omega
    · intro x hx y hy eq
      simp only [mem_coe, mem_filter, mem_Icc] at hx hy
      dsimp at eq
      omega

/-- For actual 2048-bit-sized products above the public threshold, the cutoff
309*2^1015 takes at most half of the feasible integer or odd positions. -/
theorem target_positions {n : ℕ} (full : 2*(2^1023)^2 ≤ n) :
    let L := ShortPascalRow.lower n (2^1023)
    let T := 309*2^1015
    let U := n.sqrt
    ((Icc L U).filter (fun i => i≤T)).card ≤
      ((Icc L U).filter (fun i => T < i)).card ∧
    ((Icc L U).filter (fun i => i≤T ∧ i%2=1)).card ≤
      ((Icc L U).filter (fun i => T < i ∧ i%2=1)).card := by
  have bottom : 2^1023 ≤ ShortPascalRow.lower n (2^1023) := le_max_left ..
  have top : 362*2^1015+1 ≤ n.sqrt := Nat.le_sqrt'.mpr
    (le_trans (by decide +kernel : (362*2^1015+1)^2 ≤ 2*(2^1023)^2) full)
  exact position_counts (by omega) (by decide +kernel)

/-- The average one-based position of a distinguished candidate in a
uniformly shuffled block. Empty blocks receive the value zero. -/
noncomputable def shuffleRank (w : ℕ) : ℚ :=
  (∑ i ∈ range w, ((i:ℚ)+1)) / w

theorem shuffle_rank {w : ℕ} (pos : 0<w) : shuffleRank w = ((w:ℚ)+1)/2 := by
  have ranks (k : ℕ) : 2*(∑ i ∈ range k, ((i:ℚ)+1)) = (k:ℚ)*((k:ℚ)+1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ]
      push_cast
      linear_combination ih
  unfold shuffleRank
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt pos)]
  linarith only [ranks w]

/-- Expected individual candidate tests saved when prioritizing the lower
block, divided by this input's total number of candidates. Both orders stop
after testing the true divisor. Each randomized block is shuffled uniformly. -/
noncomputable def normalizedSaving (lower upper : ℕ) (inLower : Bool) : ℚ :=
  (shuffleRank (lower+upper) -
    (if inLower then shuffleRank lower else (lower:ℚ)+shuffleRank upper)) / (lower+upper)

theorem saving_identity (lower upper : ℕ) (inLower : Bool)
    (occupied : 0 < if inLower then lower else upper) :
    normalizedSaving lower upper inLower =
      ((if inLower then (1:ℚ) else 0) - (lower:ℚ)/(lower+upper))/2 := by
  have pos : 0 < lower + upper := by cases inLower <;> simp at occupied <;> omega
  have nz : (lower:ℚ)+(upper:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt pos)
  cases inLower <;> simp only [Bool.false_eq_true, ↓reduceIte] at occupied ⊢ <;>
    unfold normalizedSaving <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    rw [shuffle_rank (by omega),shuffle_rank occupied] <;> push_cast <;>
    field_simp [nz] <;> first | ring1 | left; ring

/-- For a uniform finite population, the mean of the savings normalized
separately for each input exceeds 1.9412% of its full candidate interval.
The hit and position inequalities are those supplied by `population` and
`target_positions`. This weights every input equally regardless of width. -/
theorem mean_saving {α : Type*} (S : Finset α) (nonempty : S.Nonempty)
    (lo hi : α → ℕ) (hit : α → Bool)
    (occupied : ∀ x ∈ S, 0 < if hit x then lo x else hi x)
    (half : ∀ x ∈ S, lo x ≤ hi x)
    (odds : 538824*S.card < 1000000*(S.filter (fun x => hit x)).card) :
    (19412:ℚ)/1000000 < (∑ x ∈ S, normalizedSaving (lo x) (hi x) (hit x))/S.card := by
  have per (x : α) (hx : x ∈ S) :
      (if hit x then (1:ℚ) else 0)/2 - 1/4 ≤ normalizedSaving (lo x) (hi x) (hit x) := by
    rw [saving_identity _ _ _ (occupied x hx)]
    have occ := occupied x hx
    have pos : 0 < lo x + hi x := by cases ht : hit x <;> simp [ht] at occ <;> omega
    have qp : 0 < (lo x:ℚ) + hi x := by exact_mod_cast pos
    have le : (lo x:ℚ) ≤ hi x := by exact_mod_cast half x hx
    have width : (lo x:ℚ)/(lo x + hi x) ≤ 1/2 := (div_le_iff₀ qp).mpr (by linarith)
    linarith
  have total := sum_le_sum per
  have hits : (∑ x ∈ S, if hit x then (1:ℚ) else 0) =
      ((S.filter (fun x => hit x)).card:ℚ) := by simp [sum_ite]
  rw [sum_sub_distrib, ←sum_div, hits, sum_const, nsmul_eq_mul] at total
  have ratio : 538824*(S.card:ℚ) < 1000000*((S.filter (fun x => hit x)).card:ℚ) := by
    exact_mod_cast odds
  apply (lt_div_iff₀ (Nat.cast_pos.mpr nonempty.card_pos)).mpr
  linarith only [total,ratio]

end PrimeFactors.LowerHalfPrimeBins
