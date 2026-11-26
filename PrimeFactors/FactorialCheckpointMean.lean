import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Average convolution-input savings when a checkpoint ends the search early.
The fraction of the population in the early set and the price of its omitted
convolution are explicit hypotheses. Each input receives equal weight. -/

namespace PrimeFactors.FactorialCheckpointMean

open Finset

/-- Lean's rational division assigns zero savings to a zero baseline cost. -/
noncomputable def saving (old spent : ℕ) : ℚ := ((old : ℚ) - spent) / old

@[simp] theorem saving_zero (spent : ℕ) : saving 0 spent = 0 := by simp [saving]

noncomputable def mean {ι : Type*} (sample : Finset ι) (old spent : ι → ℕ) : ℚ :=
  (∑ x ∈ sample, saving (old x) (spent x)) / sample.card

/-- On the early inputs, a specified convolution is unspent. Everywhere else
the revised search needs at most the baseline number of convolution inputs. -/
theorem mean_of_skipped {ι : Type*} {sample early : Finset ι}
    {old spent last : ι → ℕ} {frequency share : ℚ}
    (nonempty : sample.Nonempty) (sub : early ⊆ sample)
    (prevalence : frequency * sample.card < early.card) (positive : 0 < share)
    (noMore : ∀ x ∈ sample, spent x ≤ old x)
    (charged : ∀ x ∈ early, 0 < old x)
    (skipped : ∀ x ∈ early, spent x + last x ≤ old x)
    (price : ∀ x ∈ early, share * old x ≤ last x) :
    frequency * share < mean sample old spent := by
  have onEarly (x) (hx : x ∈ early) : share ≤ saving (old x) (spent x) := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr (charged x hx) : (0 : ℚ) < old x)).2
    have budget : (spent x : ℚ) + last x ≤ old x := by exact_mod_cast skipped x hx
    linarith only [budget, price x hx]
  have onSample (x) (hx : x ∈ sample) : 0 ≤ saving (old x) (spent x) :=
    div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr (noMore x hx))) (Nat.cast_nonneg _)
  have lower : (early.card : ℚ) * share ≤ ∑ x ∈ sample, saving (old x) (spent x) := by
    calc
      _ = ∑ _x ∈ early, share := by simp
      _ ≤ ∑ x ∈ early, saving (old x) (spent x) := sum_le_sum onEarly
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub fun x hx _ => onSample x hx
  apply (lt_div_iff₀ (Nat.cast_pos.mpr nonempty.card_pos : (0 : ℚ) < sample.card)).2
  calc
    _ = (frequency * sample.card) * share := by ring
    _ < early.card * share := mul_lt_mul_of_pos_right prevalence positive
    _ ≤ _ := lower

/-- More than 9.97% early, saving at least 37% each, yields mean savings
strictly above 3.6889% of each input's original convolution count. -/
theorem forward_mean {ι : Type*} {sample early : Finset ι} {old spent last : ι → ℕ}
    (nonempty : sample.Nonempty) (sub : early ⊆ sample)
    (occupancy : 997 * sample.card < 10000 * early.card)
    (noMore : ∀ x ∈ sample, spent x ≤ old x)
    (charged : ∀ x ∈ early, 0 < old x)
    (skipped : ∀ x ∈ early, spent x + last x ≤ old x)
    (price : ∀ x ∈ early, 37 * old x ≤ 100 * last x) :
    (36889 : ℚ) / 1000000 < mean sample old spent := by
  have rate : (997 / 10000 : ℚ) * sample.card < early.card := by
    have h : 997 * (sample.card : ℚ) < 10000 * early.card := by exact_mod_cast occupancy
    linarith only [h]
  have lower := mean_of_skipped nonempty sub rate (show (0 : ℚ) < 37 / 100 by norm_num)
    noMore charged skipped (fun x hx => by
      have h : 37 * (old x : ℚ) ≤ 100 * last x := by exact_mod_cast price x hx
      linarith only [h])
  norm_num at lower ⊢
  exact lower

/-- More than 3.90% early, saving at least 49% each, yields mean savings
strictly above 1.911% of each input's original convolution count. -/
theorem centered_mean {ι : Type*} {sample early : Finset ι} {old spent last : ι → ℕ}
    (nonempty : sample.Nonempty) (sub : early ⊆ sample)
    (occupancy : 39 * sample.card < 1000 * early.card)
    (noMore : ∀ x ∈ sample, spent x ≤ old x)
    (charged : ∀ x ∈ early, 0 < old x)
    (skipped : ∀ x ∈ early, spent x + last x ≤ old x)
    (price : ∀ x ∈ early, 49 * old x ≤ 100 * last x) :
    (1911 : ℚ) / 100000 < mean sample old spent := by
  have rate : (39 / 1000 : ℚ) * sample.card < early.card := by
    have h : 39 * (sample.card : ℚ) < 1000 * early.card := by exact_mod_cast occupancy
    linarith only [h]
  have lower := mean_of_skipped nonempty sub rate (show (0 : ℚ) < 49 / 100 by norm_num)
    noMore charged skipped (fun x hx => by
      have h : 49 * (old x : ℚ) ≤ 100 * last x := by exact_mod_cast price x hx
      linarith only [h])
  norm_num at lower ⊢
  exact lower

/-- Counts for the wheel of period 210. At most 2^1023 integer positions
separate the endpoints of the equal-width smaller-factor interval. -/
theorem target_cycles {span : ℕ} (width : span ≤ 2^1023) : span / 210 ≤ 2^1016 :=
  (Nat.div_le_div_right width).trans (by decide +kernel)

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 4096 in
/-- The terminal grid chooses the first dyadic width with cycles ≤ 96·width².
For width > 1 its preceding width gave 48·width² < 2·cycles.
With 48 reduced residues, 2·floor(cycles/width)+48·width+3 majorizes the
index of every factorial denominator, for both the ordinary and paired grids. -/
theorem target_table {cycles width : ℕ} (size : cycles ≤ 2^1016)
    (stop : cycles ≤ 96 * width^2)
    (previous : width = 1 ∨ 48 * width^2 ≤ 2 * cycles) :
    2 * (cycles / width) + 48 * width + 3 < 2^518 := by
  have width_small : width < 2^508 := by
    rcases previous with rfl | prev
    · decide +kernel
    apply lt_of_not_ge
    intro big
    have bad := (Nat.mul_le_mul_left 48 (Nat.pow_le_pow_left big 2)).trans
      (prev.trans (Nat.mul_le_mul_left 2 size))
    exact (by decide +kernel : ¬ 48 * ((2:ℕ)^508)^2 ≤ 2 * 2^1016) bad
  have blocks : cycles / width ≤ 96 * width := Nat.div_le_of_le_mul' (by
    calc
      cycles ≤ 96 * width^2 := stop
      _ = width * (96 * width) := by ring)
  calc
    _ ≤ 240 * width + 3 := by omega
    _ ≤ 240 * 2^508 + 3 := Nat.add_le_add_right (Nat.mul_le_mul_left _ width_small.le) _
    _ < _ := by decide +kernel

end PrimeFactors.FactorialCheckpointMean
