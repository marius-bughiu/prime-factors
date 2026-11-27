import PrimeFactors.JacobiSquareScaleSieve
import Mathlib.Data.Real.Sqrt

/-! When a squarefree scale is tried for a product of two even neighbors
of odd primes, its root must be even. The tests for the factor sum and
the factor gap cannot both reach their final square test at that scale. -/

namespace PrimeFactors.FourNeighborSquareBands

/-- A squarefree multiplier cannot supply both factors of two. -/
theorem even_root {t h : ℕ} (free : Squarefree t) (four : 4 ∣ t*h^2) : 2 ∣ h := by
  by_contra odd
  have cop : (4:ℕ).Coprime (h^2) := ((Nat.prime_two.coprime_iff_not_dvd.mpr odd).pow_left 2).pow_right 2
  exact (Nat.squarefree_iff_prime_squarefree.mp free 2 Nat.prime_two) (cop.dvd_of_dvd_mul_right four)

/-- Applies to each of the four choices of even neighbors. -/
theorem even_root_of_product {t h a b : ℕ} (free : Squarefree t)
    (ea : 2 ∣ a) (eb : 2 ∣ b) (hit : t*h^2=a*b) : 2 ∣ h := by
  apply even_root free
  rw [hit]
  exact Nat.mul_dvd_mul ea eb

/-- At scales two and above the four root formulas use r or r+1. -/
def evenNeighbor (r : ℕ) : ℕ := if 2 ∣ r then r else r+1

theorem choose_even {r h : ℕ} (near : h=r ∨ h=r+1) (even : 2 ∣ h) : evenNeighbor r=h := by
  unfold evenNeighbor
  split_ifs <;> omega

/-- At scale one the two sum roots are the outer neighbors. -/
theorem choose_even_outer {r h : ℕ} (pos : 1 ≤ r) (near : h=r-1 ∨ h=r+2) (even : 2 ∣ h) :
    (if 2 ∣ r then r+2 else r-1)=h := by split_ifs <;> omega

private theorem nearby {l x r : ℝ} (hx : 0 ≤ x) (lr : 0 < l-r) (hr : 0 ≤ r)
    (low : (l-r)^2 ≤ x^2) (high : x^2 ≤ (l+r)^2) : l-r ≤ x ∧ x ≤ l+r := by
  constructor
  · by_contra! h
    nlinarith only [mul_pos (sub_pos.mpr h) (show 0 < l-r+x by linarith),low]
  · by_contra! h
    nlinarith only [mul_pos (sub_pos.mpr h) (show 0 < x+(l+r) by linarith),high]

/-- Even candidate roots for a balanced sum and a balanced gap cannot
coexist, also when the two numerical candidates need not be the true ones.
The sum uses distance from N+1, the gap uses distance from N−1. -/
theorem incompatible {n t y z : ℕ} (large : 9 ≤ n) (pos : 0 < t)
    (ey : 2 ∣ y) (ez : 2 ∣ z)
    (sum_lo : 4*(n:ℝ) < ((t:ℝ)*y^2-(n+1))^2)
    (sum_hi : 2*((t:ℝ)*y^2-(n+1))^2 ≤ 9*n)
    (gap_hi : 2*((t:ℝ)*z^2-((n:ℝ)-1))^2 ≤ n) : False := by
  let l := Real.sqrt n
  let c := Real.sqrt t
  let v := c*(y:ℝ)
  let w := c*(z:ℝ)
  have ls : l^2=(n:ℝ) := Real.sq_sqrt (by positivity)
  have cs : c^2=(t:ℝ) := Real.sq_sqrt (by positivity)
  have hl : 3 ≤ l := calc
    (3:ℝ) = Real.sqrt 9 := by rw [show (9:ℝ)=3^2 by norm_num,Real.sqrt_sq (by norm_num)]
    _ ≤ l := Real.sqrt_le_sqrt (by exact_mod_cast large)
  have hc : 1 ≤ c := calc
    (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ c := Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ t by omega))
  have hv : 0 ≤ v := mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  have hw : 0 ≤ w := mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  have vv : v^2=(t:ℝ)*y^2 := by dsimp only [v]; rw [mul_pow,cs]
  have ww : w^2=(t:ℝ)*z^2 := by dsimp only [w]; rw [mul_pow,cs]
  rw [←vv,←ls] at sum_lo sum_hi
  rw [←ww,←ls] at gap_hi
  have magnitude {x b : ℝ} (bp : 0 < b) (sq : x^2 ≤ b^2) : |x| ≤ b := by
    apply (sq_le_sq₀ (abs_nonneg x) bp.le).mp
    simpa only [sq_abs] using sq
  have sb := abs_le.mp (magnitude (x:=v^2-(l^2+1)) (b:=17/8*l) (by linarith) (by nlinarith only [sum_hi,sq_nonneg l]))
  have gb := abs_le.mp (magnitude (x:=w^2-(l^2-1)) (b:=3/4*l) (by linarith) (by nlinarith only [gap_hi,sq_nonneg l]))
  obtain ⟨vl,vu⟩ := nearby (x:=v) (l:=l) (r:=11/10) hv (by linarith) (by norm_num)
    (by nlinarith only [sb.1,hl]) (by nlinarith only [sb.2,hl])
  obtain ⟨wl,wu⟩ := nearby (x:=w) (l:=l) (r:=3/4) hw (by linarith) (by norm_num)
    (by nlinarith only [gb.1,hl]) (by nlinarith only [gb.2,hl])
  have eq : y=z := by
    rcases lt_trichotomy y z with lt | equal | gt
    · have step : (y:ℝ)+2 ≤ z := by exact_mod_cast (show y+2 ≤ z by omega)
      have skip := mul_le_mul_of_nonneg_left step (show 0 ≤ c by linarith)
      change c*y ≤ _ at vu
      change c*z ≤ _ at wu
      change _ ≤ c*y at vl
      nlinarith only [skip,vl,wu,hc]
    · exact equal
    · have step : (z:ℝ)+2 ≤ y := by exact_mod_cast (show z+2 ≤ y by omega)
      have skip := mul_le_mul_of_nonneg_left step (show 0 ≤ c by linarith)
      change c*y ≤ _ at vu
      change _ ≤ c*z at wl
      nlinarith only [skip,wl,vu,hc]
  have same : v=w := by dsimp only [v,w]; rw [eq]
  rw [←same] at gb
  have small : |v^2-(l^2+1)| ≤ 2*l := abs_le.mpr ⟨by linarith [gb.1],by linarith [gb.2]⟩
  nlinarith only [mul_nonneg (sub_nonneg.mpr small)
    (show 0 ≤ 2*l+|v^2-(l^2+1)| by linarith [abs_nonneg (v^2-(l^2+1))]),sq_abs (v^2-(l^2+1)),sum_lo]

end PrimeFactors.FourNeighborSquareBands
