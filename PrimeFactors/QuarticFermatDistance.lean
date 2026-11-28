import PrimeFactors.RecognizingQuarticProducts
import PrimeFactors.Fermat
import PrimeFactors.Isolation

/-! The position of a Sophie Germain factor pair in an unweighted Fermat scan.
When the two displayed factors are prime, it is the first successful midpoint. -/
namespace PrimeFactors.QuarticFermatDistance

open RecognizingQuarticProducts

def rank (x y : ℕ) := (x^2+2*y^2)-ceilSqrt (x^4+4*y^4)+1

/-- Every recognized strip with x at least sixteen has x≥2y. -/
theorem twice_le {x y : ℕ} (large : 16≤x) (strip : x^4+4*y^4<(x+1)^4) : 2*y≤x := by
  by_contra! bad
  have next : x+1≤2*y := by omega
  have cubic : y^4<(x+1)^3 := by nlinarith [sq_nonneg x]
  have up := cubic.trans_le (Nat.pow_le_pow_left next 3)
  have small : y<8 := by
    apply Nat.lt_of_mul_lt_mul_left (a:=y^3)
    nlinarith only [up]
  omega

/-- On this family the inclusive midpoint rank is between (3y²+1)/2 and
2y². The work bound counts the initial midpoint as the first exact test. -/
theorem rank_bounds {x y : ℕ} (yp : 0<y) (wide : 2*y≤x) :
    3*y^2+1≤2*rank x y ∧ rank x y≤2*y^2 := by
  let N := x^4+4*y^4
  let c := (y^2+1)/2
  have h : 4*y^2≤x^2 := by nlinarith only [Nat.pow_le_pow_left wide 2]
  have scaled := Nat.mul_le_mul_right (y^2) h
  have doubled : y^2≤2*c := by dsimp [c]; omega
  have big := Nat.pow_le_pow_left (Nat.add_le_add_left doubled (2*x^2)) 2
  have low : x^2<ceilSqrt N := by
    apply lt_of_not_ge
    intro short
    have := ceilSqrt_le_iff.mp short
    dsimp [N] at this
    have : 0<y^4 := pow_pos yp _
    nlinarith
  have high : ceilSqrt N≤x^2+c := by
    apply ceilSqrt_le_iff.mpr
    dsimp [N]
    nlinarith only [scaled,big,Nat.zero_le (y^4)]
  change 3*y^2+1≤2*(x^2+2*y^2-ceilSqrt N+1) ∧ x^2+2*y^2-ceilSqrt N+1≤2*y^2
  dsimp [c] at high
  omega

theorem midpoint_hit (x y : ℕ) :
    (x^2+2*y^2)^2=(x^4+4*y^4)+(2*x*y)^2 := by ring

/-- In a semiprime no smaller midpoint in the Fermat interval can hit. -/
theorem first {x y : ℕ} (pp : (factors x y).1.Prime) (qp : (factors x y).2.Prime)
    {m : ℕ} (start : ceilSqrt (x^4+4*y^4)≤m) (early : m<x^2+2*y^2) :
    ¬ IsSquare (m^2-(x^4+4*y^4)) := by
  let p := (factors x y).1
  let q := (factors x y).2
  have order : p≤q := by dsimp [p,q,factors]; omega
  have prod : p*q=x^4+4*y^4 := factor_product x y
  have sum : p+q=2*x^2+4*y^2 := factor_sum x y
  have p2 : 2≤p := pp.two_le
  have q2 : 2≤q := qp.two_le
  have bound : p+q≤p*q := by
    have l := Nat.mul_le_mul_right q p2
    have r := Nat.mul_le_mul_left p q2
    omega
  intro hit
  have lower := ceilSqrt_le_iff.mp start
  have low : 4*(p*q)≤(2*m)^2 := by rw [prod]; nlinarith only [lower]
  have high : 2*m<p*q+1 := by omega
  obtain ⟨a,eq⟩ := hit
  have square : IsSquare ((2*m)^2-4*(p*q)) := by
    refine ⟨2*a,?_⟩
    have ha := Nat.sub_add_cancel lower
    rw [eq] at ha
    have diff := Nat.sub_add_cancel low
    rw [prod] at diff
    rw [prod]
    nlinarith only [ha,diff]
  have := semiprime_sum_of_square_discriminant pp qp order low high square
  omega

private theorem rank_of_bracket (x y r : ℕ)
    (lower : r^2<x^4+4*y^4) (upper : x^4+4*y^4≤(r+1)^2) :
    rank x y=x^2+2*y^2-(r+1)+1 := by
  have high := ceilSqrt_le_iff.mpr upper
  have low : ¬ceilSqrt (x^4+4*y^4)≤r := fun h => (not_le_of_gt lower) (ceilSqrt_le_iff.mp h)
  rw [rank,show ceilSqrt (x^4+4*y^4)=r+1 by omega]

theorem example_rank : rank 111 10=199 :=
  (rank_of_bracket 111 10 12322 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

end PrimeFactors.QuarticFermatDistance
