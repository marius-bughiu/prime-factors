import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

namespace PrimeFactors.ReciprocalDivisorWindow

/-- Twice the logarithm of the determinant divided by the height budget to the
power of the dimension. Dimension-dependent LLL constants cancel in comparisons. -/
noncomputable def budget (a b w : ℝ) (m k : ℕ) : ℝ :=
  a*m*((m:ℝ)+1) + w*k*((k:ℝ)+1) - 2*b*m*((k:ℝ)+1)

theorem log_budget {n d W : ℝ} (hn : 0<n) (hd : 0<d) (hW : 0<W) (m k : ℕ) :
    Real.log (n^(m*(m+1))*W^(k*(k+1))/d^(2*m*(k+1))) =
    budget (Real.log n) (Real.log d) (Real.log W) m k := by
  rw [Real.log_div (mul_ne_zero (pow_ne_zero _ hn.ne') (pow_ne_zero _ hW.ne')) (pow_ne_zero _ hd.ne'),
      Real.log_mul (pow_ne_zero _ hn.ne') (pow_ne_zero _ hW.ne')]
  simp only [Real.log_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,budget]
  ring

/-- If XY=N, rescaling the radius W to WY/X and replacing m by k-m
preserves the determinant's relative height at the two reciprocal locations. -/
theorem reciprocal {X Y W : ℝ} (hx : 0<X) (hy : 0<Y) (hw : 0<W) (i j : ℕ) :
    budget (Real.log (X*Y)) (Real.log Y) (Real.log (W*Y/X)) j (i+j) =
    budget (Real.log (X*Y)) (Real.log X) (Real.log W) i (i+j) := by
  rw [Real.log_div (mul_ne_zero hw.ne' hy.ne') hx.ne', Real.log_mul hw.ne' hy.ne',
    Real.log_mul hx.ne' hy.ne']
  simp only [budget,Nat.cast_add]
  ring

theorem interval_width {N A B : ℝ} (ha : 0<A) (hb : 0<B) :
    N/A-N/B = (B-A)*(N/(A*B)) := by
  field_simp
  ring

/-- An interval [A,B] maps to [N/B,N/A]. When both certificates use the
respective lower divisor bound, the exact discrepancy is the displayed term. -/
theorem endpoint_penalty {N A B W : ℝ} (hn : 0<N) (ha : 0<A) (hb : 0<B) (hw : 0<W)
    (i j : ℕ) :
    budget (Real.log N) (Real.log (N/B)) (Real.log (W*(N/(A*B)))) j (i+j) -
      budget (Real.log N) (Real.log A) (Real.log W) i (i+j) =
      Real.log (B/A)*((j:ℝ)-i)*(i+j+1) := by
  rw [Real.log_div hn.ne' hb.ne',
    Real.log_mul hw.ne' (div_ne_zero hn.ne' (mul_ne_zero ha.ne' hb.ne')),
    Real.log_div hn.ne' (mul_ne_zero ha.ne' hb.ne'),Real.log_mul ha.ne' hb.ne',
    Real.log_div hb.ne' ha.ne']
  simp only [budget,Nat.cast_add]
  ring

end PrimeFactors.ReciprocalDivisorWindow
