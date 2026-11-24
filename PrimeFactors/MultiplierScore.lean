import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace PrimeFactors

open Finset Real

/-- Enumerating both signs at each independent prime factors the exponential
moment. Mathlib's cosh bound gives a bound uniform in the signs of the weights. -/
theorem multiplierScore_moment {I : Type*} [Fintype I] [DecidableEq I] (w : I → ℝ) :
    (∑ s : I → Bool, exp (∑ i, if s i then w i else -w i)) ≤
      2^(Fintype.card I) * exp (∑ i, (w i)^2/2) := by
  classical
  simp_rw [Real.exp_sum]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) => exp (if b then w i else -w i))]
  calc
    _ = ∏ i, (2 * cosh (w i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [Fintype.sum_bool, Real.cosh_eq]
      ring
    _ ≤ ∏ i, (2 * exp ((w i)^2/2)) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact mul_le_mul_of_nonneg_left (cosh_le_exp_half_sq _) (by norm_num)
    _ = _ := by simp [Finset.prod_mul_distrib]

/-- A multiplier may be selected after all signs have been read. Bounding its
moment by the sum over candidates charges each multiplier's offset separately. -/
theorem multiplierScore_adaptive {I M : Type*} [Fintype I] [DecidableEq I] [Fintype M]
    (choose : (I → Bool) → M) (w : M → I → ℝ) (offset : M → ℝ) :
    (∑ s : I → Bool, exp (offset (choose s) +
        ∑ i, if s i then w (choose s) i else -w (choose s) i)) ≤
      2^(Fintype.card I) * ∑ m, exp (offset m + ∑ i, (w m i)^2/2) := by
  classical
  let val (s : I → Bool) (m : M) := exp (offset m +
    ∑ i, if s i then w m i else -w m i)
  have selectBound (s : I → Bool) : val s (choose s) ≤ ∑ m, val s m :=
    Finset.single_le_sum (f := val s) (fun m _ => (exp_pos _).le) (Finset.mem_univ (choose s))
  change ∑ s, val s (choose s) ≤ _
  calc
    _ ≤ ∑ s, ∑ m, val s m := Finset.sum_le_sum (fun s _ => selectBound s)
    _ = ∑ m, ∑ s, val s m := Finset.sum_comm
    _ ≤ ∑ m, exp (offset m) * (2^(Fintype.card I) * exp (∑ i, (w m i)^2/2)) := by
      apply Finset.sum_le_sum
      intro m hm
      simp only [val, Real.exp_add, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (multiplierScore_moment (w m)) (exp_pos _).le
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Real.exp_add]
      ring

/-- Enforcing all the local signs allows at most one word per candidate, even
when the selected candidate depends on the observed word. -/
theorem multiplierScore_all_split {I M : Type*} [Fintype I] [DecidableEq I]
    (menu : Finset M) (signs : M → I → Bool) :
    (menu.image signs).card ≤ menu.card := Finset.card_image_le

end PrimeFactors
