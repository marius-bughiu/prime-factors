import Mathlib.Data.Int.Interval
import PrimeFactors.FractionalBalancedLifts

/-! Counting the representatives that pass both public windows reduces exactly to
counting suitable divisors of signed lifts of the product. Each pair belongs to
one lift. Different lifts can still contribute the same ordinary sum. -/

namespace PrimeFactors.FractionalMatchedDivisors

open Finset FractionalBalancedLifts

/-- Signed displacement from the observed product in multiples of the modulus. -/
def liftProduct (n m : ℕ) (j : ℤ) : ℤ := n + j * m

/-- Both endpoints are inclusive. The divisions are integer floors. -/
def InIndexRange (n m : ℕ) (j : ℤ) : Prop :=
  -(((n : ℤ) - 1) / (9 * m)) ≤ j ∧ j ≤ ((n : ℤ) - 1) / (8 * m)

/-- The asymmetric endpoints are the exact integer rounding of the two strict
product inequalities. Other requirements on a representative pair still apply. -/
theorem index_range_iff {n m : ℕ} (hm : 0 < m) (j : ℤ) :
    InIndexRange n m j ↔ 8 * (n : ℤ) < 9 * liftProduct n m j ∧
      8 * liftProduct n m j < 9 * n := by
  have mp : 0 < (m : ℤ) := by exact_mod_cast hm
  unfold InIndexRange liftProduct
  rw [neg_le, Int.le_ediv_iff_mul_le (by positivity),
    Int.le_ediv_iff_mul_le (by positivity)]
  constructor <;> rintro ⟨h, k⟩ <;> constructor <;> linarith

/-- A retained pair determines exactly one product lift. -/
theorem unique_lift {n m x y : ℕ} (hm : 0 < m) (pair : (x,y) ∈ pairs n m) :
    ∃! j : ℤ, InIndexRange n m j ∧ liftProduct n m j = (x*y : ℕ) := by
  obtain ⟨_,_,order,bal,window,congruent⟩ := mem_filter.mp pair
  obtain ⟨j, hj⟩ := Nat.modEq_iff_dvd.mp congruent.symm
  have prod : liftProduct n m j = (x*y : ℕ) := by
    unfold liftProduct
    linarith
  obtain ⟨lo,hi⟩ := product_bounds order bal window
  refine ⟨j, ⟨(index_range_iff hm j).2 ?_, prod⟩, ?_⟩
  · rw [prod]
    exact_mod_cast And.intro lo hi
  · rintro k ⟨_, hk⟩
    have mp : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    exact mul_right_cancel₀ mp (add_left_cancel (hk.trans prod.symm))

/-- A divisor x of the lifted product is retained exactly when x and its
complement meet the public representative, ratio and sum conditions. -/
def RetainedDivisor (n m s : ℕ) (j : ℤ) (x : ℕ) : Prop :=
  let t := (liftProduct n m j).toNat
  let y := t / x
  x ∣ t ∧ 1 < x ∧ x ≤ y ∧ y < m ∧ y < 2*x ∧ x+y=s ∧ InWindow n s

private theorem retained_of_pair {n m x y : ℕ} {j : ℤ} (pair : (x,y) ∈ pairs n m)
    (prod : liftProduct n m j = (x*y : ℕ)) : RetainedDivisor n m (x+y) j x := by
  obtain ⟨box, hx, hxy, bal, win, _⟩ := mem_filter.mp pair
  have xp : 0 < x := by omega
  unfold RetainedDivisor
  simp only [prod, Int.toNat_natCast, Nat.mul_div_cancel_left _ xp]
  exact ⟨dvd_mul_right _ _, hx, hxy, mem_range.mp (mem_product.mp box).2, bal, trivial, win⟩

private theorem pair_of_retained {n m s x : ℕ} {j : ℤ} (hm : 0 < m)
    (bound : InIndexRange n m j) (retained : RetainedDivisor n m s j x) :
    let y := (liftProduct n m j).toNat / x
    (x,y) ∈ pairs n m ∧ x+y=s ∧ liftProduct n m j = (x*y : ℕ) := by
  obtain ⟨dv, hx, hxy, ym, bal, sum, win⟩ := retained
  let t := (liftProduct n m j).toNat
  let y := t / x
  have prod : x*y=t := Nat.mul_div_cancel' dv
  have nonneg : 0 ≤ liftProduct n m j := by
    have := ((index_range_iff hm j).1 bound).1
    have : 0 ≤ (n : ℤ) := by positivity
    omega
  have eqn : ((x*y : ℕ) : ℤ) = liftProduct n m j := by
    rw [prod]; exact Int.toNat_of_nonneg nonneg
  have congruent : x*y ≡ n [MOD m] := by
    apply Nat.ModEq.symm
    exact Nat.modEq_iff_dvd.mpr ⟨j, by rw [eqn]; unfold liftProduct; ring⟩
  exact ⟨mem_filter.mpr
    ⟨mem_product.mpr ⟨mem_range.mpr (hxy.trans_lt ym), mem_range.mpr ym⟩,
      hx, hxy, bal, sum ▸ win, congruent⟩, sum, eqn.symm⟩

/-- The sums in the image are precisely those with a retained divisor on some lift. -/
theorem sum_iff_retained_divisor {n m s : ℕ} (hm : 0 < m) :
    s ∈ (pairs n m).image (fun z => z.1 + z.2) ↔
      ∃ j : ℤ, InIndexRange n m j ∧ ∃ x, RetainedDivisor n m s j x := by
  constructor
  · rintro hs
    obtain ⟨⟨x,y⟩, pair, rfl⟩ := mem_image.mp hs
    obtain ⟨j, ⟨bound, prod⟩, _⟩ := unique_lift hm pair
    exact ⟨j, bound, x, retained_of_pair pair prod⟩
  · rintro ⟨j, bound, x, retained⟩
    obtain ⟨pair, sum, _⟩ := pair_of_retained hm bound retained
    exact mem_image.mpr ⟨_, pair, sum⟩

/-- Actual divisors of one lift that contribute to the proposed sum. -/
noncomputable def divisorFiber (n m s : ℕ) (j : ℤ) : Finset ℕ := by
  classical
  exact (liftProduct n m j).toNat.divisors.filter (RetainedDivisor n m s j)

/-- Multiplicity of a single ordinary sum equals the sum of its divisor counts
over the signed index interval. Distinct smaller divisors specify distinct pairs. -/
theorem multiplicity_eq {n m s : ℕ} (hm : 0 < m) :
    ((pairs n m).filter fun z => z.1+z.2=s).card =
      ∑ j ∈ Icc (-(((n : ℤ)-1)/(9*m))) (((n : ℤ)-1)/(8*m)), (divisorFiber n m s j).card := by
  classical
  rw [← card_sigma]
  symm
  apply card_bij (fun z _ => (z.2, (liftProduct n m z.1).toNat / z.2))
  · rintro ⟨j,x⟩ hz
    obtain ⟨bound, keep⟩ := mem_sigma.mp hz
    obtain ⟨pair, sum, _⟩ := pair_of_retained hm (mem_Icc.mp bound) (mem_filter.mp keep).2
    exact mem_filter.mpr ⟨pair, sum⟩
  · rintro ⟨j,x⟩ ha ⟨k,y⟩ hb h
    obtain ⟨rfl, same⟩ := Prod.mk.inj h
    obtain ⟨ja, ra⟩ := mem_sigma.mp ha
    obtain ⟨kb, rb⟩ := mem_sigma.mp hb
    obtain ⟨_, _, p⟩ := pair_of_retained hm (mem_Icc.mp ja) (mem_filter.mp ra).2
    obtain ⟨_, _, q⟩ := pair_of_retained hm (mem_Icc.mp kb) (mem_filter.mp rb).2
    rw [same] at p
    have mp : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    have eqn : j=k := mul_right_cancel₀ mp (add_left_cancel (p.trans q.symm))
    cases eqn
    rfl
  · rintro ⟨x,y⟩ hb
    obtain ⟨pair, rfl⟩ := mem_filter.mp hb
    obtain ⟨j, ⟨bound, prod⟩, _⟩ := unique_lift hm pair
    have retained := retained_of_pair pair prod
    have hx : 0 < x := by have := retained.2.1; omega
    have hy : 0 < y := by have := (mem_filter.mp pair).2.2.1; omega
    refine ⟨⟨j,x⟩, mem_sigma.mpr ⟨mem_Icc.mpr bound, mem_filter.mpr ⟨?_, retained⟩⟩, ?_⟩
    · rw [prod, Int.toNat_natCast]
      exact Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, (Nat.mul_pos hx hy).ne'⟩
    · simp only [prod, Int.toNat_natCast, Nat.mul_div_cancel_left _ hx]

/-- One lift contributes two distinct sums, and two different lifts contribute
sum 60. This rules out counting a lift as a single pair or a distinct sum. -/
theorem example_851 :
    (23,37) ∈ pairs 851 49 ∧ (30,30) ∈ pairs 851 49 ∧ (25,36) ∈ pairs 851 49 ∧
    liftProduct 851 49 0 = 23*37 ∧ liftProduct 851 49 1 = 30*30 ∧
    liftProduct 851 49 1 = 25*36 ∧ 23+37=60 ∧ 30+30=60 ∧ 25+36=61 := by
  simp only [pairs, mem_filter, mem_product, mem_range, InWindow, liftProduct]
  decide +kernel

end PrimeFactors.FractionalMatchedDivisors
