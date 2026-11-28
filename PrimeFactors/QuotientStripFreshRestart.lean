import PrimeFactors.QuotientStripSurvivingBlocks
import PrimeFactors.OffsetWinnerExamples

/-!
# Surviving blocks after the equal-width restart on the fresh control

Keep the half of the primitive grid with first coordinate at most its second.
Its directions have u/v ≤ 9/7, placing the stationary bands far enough right
to survive the tighter public restart even on the independently generated input.
-/

namespace PrimeFactors.QuotientStripFreshRestart

open Finset CircleMarkRationalFrequency QuotientStripScheduleCost QuotientStripSlopePopulation
open QuotientStripSurvivingBlocks QuotientStripWideSlopeGeometry QuotientStripSlopeRestart

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

private noncomputable def halfGrid (B : ℕ) : Finset (ℕ×ℕ) :=
  (primitive B B).filter fun z => z.1 ≤ z.2

private noncomputable def halfDirections (B : ℕ) : Finset (ℕ×ℕ) :=
  (halfGrid B).image direction

private theorem swapped {B : ℕ} {z : ℕ×ℕ} (hz : z∈primitive B B) :
    z.swap∈primitive B B := by
  obtain ⟨hr,hc⟩ := mem_filter.mp hz
  change z ∈ Icc 1 B ×ˢ Icc 1 B at hr
  rw [mem_product] at hr
  exact mem_filter.mpr ⟨mem_product.mpr ⟨hr.2,hr.1⟩,Nat.Coprime.symm hc⟩

private theorem half_card (B : ℕ) : (directions B).card ≤ 2*(halfDirections B).card := by
  classical
  have cover : primitive B B ⊆ halfGrid B ∪ (halfGrid B).image Prod.swap := by
    intro z hz
    rcases le_total z.1 z.2 with sorted | reversed
    · exact mem_union_left _ (mem_filter.mpr ⟨hz,sorted⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨z.swap,mem_filter.mpr ⟨swapped hz,reversed⟩,
        Prod.swap_swap z⟩)
  have bound := (card_le_card cover).trans (card_union_le _ _)
  have image : ((halfGrid B).image Prod.swap).card ≤ (halfGrid B).card := card_image_le
  simp only [directions,halfDirections,card_image_of_injective _ direction_injective]
  omega

private theorem in_upper_half {B : ℕ} {d : ℕ×ℕ} (hd : d∈halfDirections B) :
    d∈directions B ∧ 7*d.1 ≤ 9*d.2 := by
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hd
  obtain ⟨inside,order⟩ := mem_filter.mp hz
  exact ⟨mem_image.mpr ⟨z,inside,rfl⟩,by simp only [direction]; omega⟩

attribute [local irreducible] directions halfGrid halfDirections

/-- For this half of the grid, the entire stationary band lies above
0.8809 times the square root of the product. -/
private theorem fits {s r u v t L : ℝ} (G : Band s r u v t L)
    (ratio : 7*u≤9*v) (rlarge : 1000000 ≤ r) : 8809*s/10000 ≤ t-L := by
  obtain ⟨rp,_,_,up,sp⟩ := G.basic
  have sq : 7*s^2 ≤ 9*t^2 := by
    apply le_of_mul_le_mul_left _ up
    nlinarith only [mul_le_mul_of_nonneg_right ratio (sq_nonneg s),G.atCenter]
  have center : 881*s ≤ 1000*t := by
    by_contra! bad
    have h := mul_self_lt_mul_self (by linarith only [G.tp] : 0≤1000*t) bad
    nlinarith only [h,sq,sq_nonneg s]
  have span : 1000000 ≤ 4*v*r := by
    nlinarith only [mul_le_mul_of_nonneg_right G.vp rp.le,rlarge]
  have bound := mul_le_mul_of_nonneg_right span G.lp.le
  nlinarith only [center,bound,G.span,sp.le]

/-- A sufficient product-only inequality on the chosen origin. The block ends
are strictly before the supplied cutoff, by the definition of kept. -/
theorem population {n origin cutoff : ℕ} (lo : 2^2047≤n) (hi : n<2^2048)
    (late : 4*n≤5*cutoff^2) (early : (10000*origin)^2 ≤ 8809^2*n) :
    2^653 < (kept n origin cutoff).card := by
  have sq : Real.sqrt (n:ℝ)^2 = n := Real.sq_sqrt (by positivity)
  have realBound : (10000*(origin:ℝ))^2 ≤ 8809^2*(n:ℝ) := by exact_mod_cast early
  have originBound : (origin:ℝ) ≤ 8809*Real.sqrt n/10000 := by
    by_contra! bad
    have h := mul_self_lt_mul_self (by positivity : (0:ℝ) ≤ 8809*Real.sqrt n)
      (show 8809*Real.sqrt n < 10000*(origin:ℝ) by linarith only [bad])
    nlinarith only [h,sq,realBound]
  have rbig : (1000000:ℕ) ≤ roundedSixth n :=
    (by decide +kernel : 1000000≤2^341).trans (QuotientStripTailCost.root_bounds lo hi).2.2.1
  have count := two_blocks (halfDirections (2^327)) (kept n origin cutoff) (owner n origin) (by
    intro d hd
    obtain ⟨member,ratio⟩ := in_upper_half hd
    have place (t L : ℝ) (G : Band (Real.sqrt n) (roundedSixth n) d.1 d.2 t L) :
        (origin:ℝ) ≤ t-L :=
      originBound.trans (fits G (by exact_mod_cast ratio) (by exact_mod_cast rbig))
    obtain ⟨i,ki,j,kj,diff,oi,oj,_⟩ := two_for_each_fits lo hi late member place
    exact ⟨i,ki,j,kj,diff,oi,oj⟩)
  have all := many_directions
  have half := half_card (2^327)
  omega

/-- Evaluate only the partner quotient on a specific product. The two other
parts of the public restart satisfy its bound on every full-width input. -/
theorem clipped_origin_bound {n D : ℕ} (lo : 2^2047 ≤ n)
    (partner : (10000*((n-1)/D+1))^2 ≤ 8809^2*n) :
    (10000*clippedStart n D)^2 ≤ 8809^2*n := by
  have f := original_fits lo
  have s := Real.sqrt_nonneg (n:ℝ)
  have e : 10000*(first n:ℝ) ≤ 8809*Real.sqrt n := by linarith only [f,s]
  have f2 : (10000*first n)^2 ≤ 8809^2*n := by
    exact_mod_cast (show ((10000:ℝ)*first n)^2 ≤ 8809^2*(n:ℝ) by
      nlinarith only [pow_le_pow_left₀ (by positivity : (0:ℝ)≤10000*(first n:ℝ)) e 2,
        Real.sq_sqrt (by positivity : (0:ℝ)≤(n:ℝ))])
  have edge := (by decide +kernel : (10000*2^1023)^2 ≤ 8809^2*2^2047).trans
    (Nat.mul_le_mul_left (8809^2) lo)
  unfold clippedStart
  rcases le_total ((n-1)/D+1) (2^1023) with h | h
  · rw [max_eq_right h]
    rcases le_total (first n) (2^1023) with k | k
    · simpa only [max_eq_right k] using edge
    · simpa only [max_eq_left k] using f2
  · rw [max_eq_left h]
    rcases le_total (first n) ((n-1)/D+1) with k | k
    · simpa only [max_eq_right k] using partner
    · simpa only [max_eq_left k] using f2

/-- The same decimal product and smaller prime as the independently generated
Pocklington control. The measured endpoint uses the strongest integer partner
cap for two 1,024-bit primes. -/
theorem fresh_before_hit :
    2^653 < (kept OffsetWinnerExamples.fresh.N
      (clippedStart OffsetWinnerExamples.fresh.N (2^1024-1)) OffsetWinnerExamples.fresh.p).card := by
  apply population (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact clipped_origin_bound (by decide +kernel) (by decide +kernel)

end PrimeFactors.QuotientStripFreshRestart
