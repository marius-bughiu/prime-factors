import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace PrimeFactors.FoldedFactorial

open Polynomial
open scoped Polynomial

variable {R ι : Type*} [CommRing R]

/-- A polynomial for the product of two blocks at equal distances from a boundary.
Each index names one offset, including equal values at different indices. -/
noncomputable def folded (a b : R) (s : Finset ι) (offset : ι → R) : R[X] :=
  ∏ i ∈ s, (C (-(b^2)) * X + C ((a+offset i)*(a+offset i-b)))

/-- The quadratic coordinate represents both translated blocks with one factor per offset. -/
theorem folded_eval (a b j : R) (s : Finset ι) (offset : ι → R) :
    (folded a b s offset).eval (j*(j+1)) =
    (∏ i ∈ s, (a+offset i+b*j)) * (∏ i ∈ s, (a+offset i-b*(j+1))) := by
  rw [folded, eval_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [eval_add, eval_mul, eval_C, eval_X]
  ring

/-- This degree bound also holds modulo composite integers. -/
theorem folded_natDegree_le (a b : R) (s : Finset ι) (offset : ι → R) :
    (folded a b s offset).natDegree ≤ s.card := by
  unfold folded
  refine (natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum fun _i _ ↦ by
      rw [natDegree_add_C]
      exact (natDegree_C_mul_le _ _).trans natDegree_X_le
    _ = _ := by simp

/-- Over a domain with nonzero stride every offset contributes exactly one degree. -/
theorem folded_natDegree [IsDomain R] (a b : R) (hb : b ≠ 0)
    (s : Finset ι) (offset : ι → R) : (folded a b s offset).natDegree = s.card := by
  have h (i : ι) : (C (-(b^2))*X + C ((a+offset i)*(a+offset i-b))).natDegree = 1 := by
    rw [natDegree_add_C, natDegree_C_mul_X _ (neg_ne_zero.mpr (pow_ne_zero _ hb))]
  unfold folded
  have hn (i : ι) : C (-(b^2))*X + C ((a+offset i)*(a+offset i-b)) ≠ 0 := by
    intro hz
    have hd := h i
    rw [hz, natDegree_zero] at hd
    omega
  rw [natDegree_prod _ _ (fun i _ ↦ hn i)]
  simp only [h, Finset.sum_const, smul_eq_mul, mul_one]

/-- A unit stride gives the exact degree even when the coefficient ring has zero divisors. -/
theorem folded_natDegree_of_isUnit [Nontrivial R] (a b : R) (hb : IsUnit b)
    (s : Finset ι) (offset : ι → R) : (folded a b s offset).natDegree = s.card := by
  have hu : IsUnit (-(b^2)) := (hb.pow 2).neg
  let linear (i : ι) := C (-(b^2))*X + C ((a+offset i)*(a+offset i-b))
  have hd (i : ι) : (linear i).natDegree = 1 := by
    dsimp only [linear]
    rw [natDegree_add_C, natDegree_C_mul_X _ hu.ne_zero]
  have lc (i : ι) : (linear i).leadingCoeff = -(b^2) := by
    rw [leadingCoeff, hd]
    simp only [linear, coeff_add, coeff_C_mul_X, if_true, coeff_C_succ, add_zero]
  change (∏ i ∈ s, linear i).natDegree = s.card
  rw [natDegree_prod' _ _ (by simpa only [lc, Finset.prod_const] using (hu.pow s.card).ne_zero)]
  simp only [hd, Finset.sum_const, smul_eq_mul, mul_one]

/-- A block of length h at an integer index relative to the central boundary. -/
noncomputable def segment {M : Type*} [CommMonoid M] (f : ℤ → M) (h : ℕ) (j : ℤ) : M :=
  ∏ k ∈ Finset.range h, f (h*j+k)

theorem segment_double {M : Type*} [CommMonoid M] (f : ℤ → M) (h : ℕ) (j : ℤ) :
    segment f (2*h) j = segment f h (2*j) * segment f h (2*j+1) := by
  unfold segment
  rw [show 2*h = h+h by omega, Finset.prod_range_add]
  push_cast
  congr 1 <;> apply Finset.prod_congr rfl <;> intro k _ <;> congr 1 <;> ring

/-- Two equal segments, counted outward from their common boundary. -/
noncomputable def paired {M : Type*} [CommMonoid M] (f : ℤ → M) (h : ℕ) (j : ℤ) : M :=
  segment f h j * segment f h (-(j+1))

theorem paired_double {M : Type*} [CommMonoid M] (f : ℤ → M) (h : ℕ) (j : ℤ) :
    paired f (2*h) j = paired f h (2*j) * paired f h (2*j+1) := by
  simp only [paired, segment_double]
  rw [show 2 * -(j+1) = -(2*j+1+1) by ring, show -(2*j+1+1)+1 = -(2*j+1) by ring]
  ac_rfl

theorem segments_forward {M : Type*} [CommMonoid M] (f : ℤ → M) (h g : ℕ) :
    (∏ j ∈ Finset.range g, segment f h j) = ∏ i ∈ Finset.range (h*g), f i := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [Finset.prod_range_succ, ih, Nat.mul_succ, Finset.prod_range_add]
    unfold segment
    push_cast
    rfl

theorem segment_reflect {M : Type*} [CommMonoid M] (f : ℤ → M) (h j : ℕ) :
    segment f h (-(j+1 : ℤ)) = segment (fun i ↦ f (-(i+1))) h j := by
  unfold segment
  rw [← Finset.prod_range_reflect (fun k : ℕ ↦ f (h*(-(j+1 : ℤ))+k)) h]
  apply Finset.prod_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  congr 1
  rw [Nat.cast_sub (by omega : k ≤ h-1), Nat.cast_sub (by omega : 1 ≤ h)]
  push_cast
  ring

/-- The complete paired blocks cover every index between -hg and hg-1 exactly once. -/
theorem paired_coverage {M : Type*} [CommMonoid M] (f : ℤ → M) (h g : ℕ) :
    (∏ j ∈ Finset.range g, paired f h j) =
    (∏ i ∈ Finset.range (h*g), f i) * (∏ i ∈ Finset.range (h*g), f (-(i+1 : ℤ))) := by
  simp only [paired, segment_reflect, Finset.prod_mul_distrib, segments_forward]

/-- The node difference gives two ordinary reciprocal kernels. -/
theorem grid_difference (t i : R) : t*(t+1)-i*(i+1) = (t-i)*(t+i+1) := by ring

theorem reciprocal_difference {K : Type*} [Field K] (t i : K)
    (h₁ : t-i ≠ 0) (h₂ : t+i+1 ≠ 0) :
    (2*i+1) / ((t-i)*(t+i+1)) = 1/(t-i) - 1/(t+i+1) := by
  field_simp
  ring

/-- Convolution input lengths summed over ordinary doubled blocks of width 4·2^k. -/
noncomputable def ordinaryInputs (ρ g k : ℕ) : ℕ :=
  (∑ i ∈ Finset.range (k+1), (5*ρ*2^i+2)) + ρ*2^(k+1) + 2*g

/-- Convolution input lengths at the same width using the quadratic coordinate. -/
noncomputable def foldedInputs (ρ g k : ℕ) : ℕ :=
  (∑ i ∈ Finset.range k, (7*ρ*2^i+4)) + 3*ρ*2^k + 2*g + 2

theorem input_saving_exact (ρ g k : ℕ) :
    ordinaryInputs ρ g k + 2*k = foldedInputs ρ g k + (2*2^k+2)*ρ := by
  unfold ordinaryInputs foldedInputs
  induction k with
  | zero => simp; ring
  | succ k ih =>
    rw [Finset.sum_range_succ (fun i ↦ 5*ρ*2^i+2) (k+1),
      Finset.sum_range_succ (fun i ↦ 7*ρ*2^i+4) k]
    simp only [pow_succ] at *
    linarith only [ih]

theorem foldedInputs_lt (ρ g k : ℕ) (hρ : 0 < ρ) :
    foldedInputs ρ g k < ordinaryInputs ρ g k := by
  have h := input_saving_exact ρ g k
  have hbound : 2*2^k+2 ≤ (2*2^k+2)*ρ := Nat.le_mul_of_pos_right _ hρ
  have hpow := k.lt_two_pow_self
  omega

end PrimeFactors.FoldedFactorial
