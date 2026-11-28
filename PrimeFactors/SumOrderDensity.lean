import Mathlib.Algebra.Order.Rearrangement
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! Order of tests in a smooth fixed-product model. A candidate receives its
local multiplicity times the density of the sum coordinate. Results concern
modeled probability and one equal-cost test per candidate. -/

namespace PrimeFactors.SumOrderDensity

open Finset MeasureTheory Real

/-- Modeled probability per unit candidate length. The discriminant must be
positive for use as a density. The single endpoint at zero has zero area. -/
noncomputable def density (n w s : ℝ) := w / sqrt (s^2 - 4*n)

/-- The derivative of the normalized sum with respect to logarithmic gap is
the square root of its discriminant on the increasing half of the curve. -/
theorem sum_derivative {n a : ℝ} (hn : 0 ≤ n) (ha : 0 ≤ a) :
    HasDerivAt (fun t => 2 * sqrt n * cosh t)
      (sqrt ((2 * sqrt n * cosh a)^2 - 4*n)) a := by
  have eq : (2 * sqrt n * cosh a)^2 - 4*n = (2 * sqrt n * sinh a)^2 := by
    rw [mul_pow (2 * sqrt n), mul_pow (2 * sqrt n), mul_pow 2, sq_sqrt hn]
    nlinarith only [congrArg (fun t : ℝ => n*t) (cosh_sq_sub_sinh_sq a)]
  rw [eq, Real.sqrt_sq (mul_nonneg (by positivity) (sinh_nonneg_iff.mpr ha))]
  exact (hasDerivAt_cosh a).const_mul _

/-- A smaller discriminant per squared multiplicity is exactly a larger
density, including ties. -/
theorem density_order {n s t u v : ℝ} (ds : 0 < s^2-4*n) (dt : 0 < t^2-4*n)
    (hu : 0 < u) (hv : 0 < v) :
    density n v t ≤ density n u s ↔ v^2*(s^2-4*n) ≤ u^2*(t^2-4*n) := by
  unfold density
  rw [div_le_div_iff₀ (sqrt_pos.2 dt) (sqrt_pos.2 ds),
    ←sq_le_sq₀ (mul_nonneg hv.le (sqrt_nonneg _)) (mul_nonneg hu.le (sqrt_nonneg _)),
    mul_pow, mul_pow, sq_sqrt ds.le, sq_sqrt dt.le]

/-- With two weight-five classes and five weight-two classes, each
comparison between the two increasing lists has this threshold. -/
theorem merge_two_groups {n sf so : ℝ} (df : 0 < sf^2-4*n) (dOrd : 0 < so^2-4*n) :
    density n 2 so ≤ density n 5 sf ↔ 4*(sf^2-4*n) ≤ 25*(so^2-4*n) := by
  convert density_order (u:=5) (v:=2) df dOrd (by norm_num) (by norm_num) using 2 <;> ring

theorem within_group {n s t w : ℝ} (hw : 0 < w) (hs : 0 ≤ s) (st : s ≤ t)
    (ds : 0 < s^2-4*n) : density n w t ≤ density n w s := by
  have sq := sq_le_sq₀ hs (hs.trans st) |>.mpr st
  have discs : s^2-4*n ≤ t^2-4*n := by linarith only [sq]
  exact (density_order ds (ds.trans_le discs) hw hw).mpr
    (mul_le_mul_of_nonneg_left discs (sq_nonneg w))

/-- Within the normalized product slice n=3/4, the descending density order
puts the favored position 1.746 between the ordinary positions 1.733 and
1.740. Both ascending order and exhausting the favored group reverse a
strict priority on this three-position table. -/
theorem three_positions :
    sqrt 3 < (1733:ℝ)/1000 ∧ (1746:ℝ)/1000 < 1+3/4 ∧
    density (3/4) 2 (1740/1000) < density (3/4) 5 (1746/1000) ∧
    density (3/4) 5 (1746/1000) < density (3/4) 2 (1733/1000) := by
  refine ⟨(sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num), by norm_num, ?_, ?_⟩
  · apply lt_of_not_ge
    intro h
    have impossible := (density_order (n:=(3:ℝ)/4) (s:=1740/1000) (t:=1746/1000)
      (u:=2) (v:=5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp h
    norm_num at impossible
  · apply lt_of_not_ge
    intro h
    have impossible := (density_order (n:=(3:ℝ)/4) (s:=1746/1000) (t:=1733/1000)
      (u:=5) (v:=2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp h
    norm_num at impossible

/-- On a finite table ordered by nondecreasing discriminant divided by
squared weight, the modeled expected inclusive rank is minimal over all
permutations. Dividing both sides by total modeled mass normalizes them. -/
theorem optimal_ranks {k : ℕ} (n : ℝ) (w s : Fin k → ℝ)
    (weights : ∀ i, 0 < w i) (discs : ∀ i, 0 < (s i)^2-4*n)
    (ordered : Monotone (fun i => ((s i)^2-4*n)/(w i)^2)) (perm : Equiv.Perm (Fin k)) :
    ∑ i, density n (w i) (s i) * ((i.val:ℝ)+1) ≤
    ∑ i, density n (w i) (s i) * (((perm i).val:ℝ)+1) := by
  have anti : Antitone (fun i => density n (w i) (s i)) := by
    intro i j hij
    apply (density_order (discs i) (discs j) (weights i) (weights j)).mpr
    have key := (div_le_div_iff₀ (sq_pos_of_pos (weights i)) (sq_pos_of_pos (weights j))).mp
      (ordered hij)
    simpa only [mul_comm] using key
  have inc : Monotone (fun i : Fin k => (i.val:ℝ)+1) := by
    intro i j hij
    exact add_le_add_right (by exact_mod_cast hij : (i.val:ℝ) ≤ j.val) _
  exact (anti.antivary inc).sum_mul_le_sum_mul_comp_perm

/-- At every modeled cost with a superlevel-set realization, that set
collects the largest possible probability. The test-volume measure may
include different class multiplicities. The competing set may be arbitrary.
The likelihood is measured per unit of this test volume. -/
theorem superlevel_optimal {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : StronglyMeasurable f) (fi : Integrable f μ) (c : ℝ)
    {s : Set α} (hs : MeasurableSet s) (same : μ s = μ {x | c ≤ f x}) :
    (∫ x in s, f x ∂μ) ≤ ∫ x in {y | c ≤ f y}, f x ∂μ := by
  have cmp := setIntegral_le_nonneg (μ:=μ) hs (hf.sub stronglyMeasurable_const)
    (fi.sub (integrable_const c))
  change (∫ x in s, f x - c ∂μ) ≤ ∫ x in {y | 0 ≤ f y-c}, f x - c ∂μ at cmp
  simp only [sub_nonneg] at cmp
  rw [integral_sub fi.integrableOn (integrable_const c),
    integral_sub fi.integrableOn (integrable_const c), setIntegral_const, setIntegral_const] at cmp
  simpa only [Measure.real, same, sub_le_sub_iff_right] using cmp

end PrimeFactors.SumOrderDensity
