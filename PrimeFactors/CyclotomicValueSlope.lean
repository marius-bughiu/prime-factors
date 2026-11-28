import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! A quantitative slope estimate for the classical Bernoulli generating
function at positive arguments, and a lower bound for its associated
exponential product on the normalized factor interval. -/

namespace PrimeFactors.CyclotomicValueSlope

open Real Set

noncomputable def f (z : ℝ) := z/(exp z-1)

theorem hasDeriv {z : ℝ} (hz : 0<z) :
    HasDerivAt f ((exp z-1-z*exp z)/(exp z-1)^2) z := by
  have nz : exp z-1≠0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hz)).ne'
  simpa only [f,id_eq,one_mul,sub_zero] using
    (hasDerivAt_id z).div ((Real.hasDerivAt_exp z).sub_const 1) nz

/-- Subtract z²/2 from the positive numerator of −f′. The remainder starts
at zero and its derivative is z(exp z−1), which is nonnegative. -/
private theorem numerator {z : ℝ} (hz : 0<z) :
    z^2/2≤1+(z-1)*exp z := by
  let g := fun t : ℝ => 1+(t-1)*exp t-t^2/2
  have diff (t : ℝ) : HasDerivAt g (t*(exp t-1)) t := by
    dsimp only [g]
    convert ((((hasDerivAt_id t).sub_const 1).mul (Real.hasDerivAt_exp t)).const_add 1).sub
      (((hasDerivAt_id t).pow 2).div_const 2) using 1
    simp only [id_eq]
    ring
  have cont : ContinuousOn g (Icc 0 z) := fun t _ => (diff t).continuousAt.continuousWithinAt
  obtain ⟨t,ht,eq⟩ := exists_hasDerivAt_eq_slope g (fun t => t*(exp t-1)) hz cont
    (fun t _ => diff t)
  have ng := mul_nonneg ht.1.le (sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht.1.le))
  rw [eq] at ng
  have pos := (le_div_iff₀ (by linarith : 0<z-0)).mp ng
  have start : g 0=0 := by norm_num [g]
  rw [zero_mul, start, sub_zero] at pos
  exact sub_nonneg.mp pos

private theorem denominator {z : ℝ} (hz : 0<z) (top : z≤1/4) : exp z-1≤(4/3)*z := by
  have estimate := Real.exp_bound_div_one_sub_of_interval hz.le (by linarith)
  have base := (le_div_iff₀ (by linarith : 0<1-z)).mp estimate
  have epos := (Real.exp_pos z).le
  have bounded : exp z≤4/3 := by nlinarith only [base,mul_nonneg (sub_nonneg.mpr top) epos]
  nlinarith only [base,mul_nonneg (sub_nonneg.mpr bounded) hz.le]

/-- Uniform derivative bound on the positive interval to one quarter. -/
theorem derivative_bound {z : ℝ} (hz : 0<z) (top : z≤1/4) : deriv f z≤ -(9/32) := by
  rw [(hasDeriv hz).deriv]
  have dpos := sub_pos.mpr (Real.one_lt_exp_iff.mpr hz)
  apply (div_le_iff₀ (sq_pos_of_pos dpos)).mpr
  have squared := sq_le_sq' (by linarith only [dpos,hz] : -((4/3)*z)≤exp z-1) (denominator hz top)
  nlinarith only [numerator hz,squared]

theorem slope {u v : ℝ} (pos : 0<u) (ord : u≤v) (top : v≤1/4) :
    f v-f u≤ -(v-u)/4 := by
  obtain eq|lt := ord.eq_or_lt
  · simp [eq]
  have cont : ContinuousOn f (Icc u v) := fun t ht =>
    (hasDeriv (pos.trans_le ht.1)).continuousAt.continuousWithinAt
  have diff : DifferentiableOn ℝ f (Ioo u v) := fun t ht =>
    (hasDeriv (pos.trans ht.1)).differentiableAt.differentiableWithinAt
  obtain ⟨t,ht,eq⟩ := exists_deriv_eq_slope f lt cont diff
  have upper := derivative_bound (pos.trans ht.1) (ht.2.le.trans top)
  rw [eq] at upper
  have step := (div_le_iff₀ (sub_pos.mpr lt)).mp upper
  linarith

/-- Each factor of the product is at least 1/9 because exp(t)≥1+t. -/
theorem response_lower {u v : ℝ} (hu : 1/8≤u) (hv : 1/8≤v) :
    (1:ℝ)/81 ≤ (1-exp (-u))*(1-exp (-v)) := by
  have one (t : ℝ) (ht : 1/8≤t) : (1:ℝ)/9≤1-exp (-t) := by
    rw [Real.exp_neg]
    have high : 9/8≤exp t := by linarith only [Real.add_one_le_exp t,ht]
    have inv : (exp t)⁻¹≤8/9 := (inv_le_comm₀ (Real.exp_pos t) (by norm_num)).mpr (by
      norm_num
      exact high)
    linarith
  have bound := mul_le_mul (one u hu) (one v hv) (by norm_num) (by linarith [one u hu])
  norm_num at bound ⊢
  exact bound

end PrimeFactors.CyclotomicValueSlope
