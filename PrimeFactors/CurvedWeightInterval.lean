import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PrimeFactors.CurvedWeightInterval

/-- The balanced factor curve with product 8z², midpoint h and signed half-gap d. -/
def balanced (z h d : ℝ) : Prop := 3*|d| ≤ h ∧ h^2-d^2=8*z^2

/-- Minimum of the weighted trace after the coefficient signs have been normalized. -/
noncomputable def lower (z u v : ℝ) : ℝ :=
  if u ≤ 3*v then (3*u-v)*z else Real.sqrt (8*z^2*(u^2-v^2))

theorem coordinates {z h e : ℝ} (hz : 0≤z) (he : 0≤e)
    (balance : 3*e≤h) (curve : h^2-e^2=8*z^2) : e≤z ∧ h≤3*z := by
  have eh := (sq_le_sq₀ (by positivity : 0≤3*e) (by linarith : 0≤h)).mpr balance
  have ez : e≤z := (sq_le_sq₀ he hz).mp (by nlinarith only [eh,curve])
  refine ⟨ez,(sq_le_sq₀ (by linarith) (by positivity)).mp ?_⟩
  nlinarith only [(sq_le_sq₀ he hz).mpr ez,curve]

/-- At the outer end the secant has slope no greater than 1/3. Squaring
the nonnegative sides leaves exactly 8*(z-e)² and works also at e=z. -/
theorem endpoint_gap {z h e : ℝ} (he : 0≤e) (balance : 3*e≤h)
    (curve : h^2-e^2=8*z^2) : 3*(3*z-h)≤z-e := by
  have hpos : 0≤3*h := by linarith
  have cmp : 8*z+e≤3*h := le_of_not_gt (by
    intro bad
    have strict := (sq_lt_sq₀ hpos (by linarith)).mpr bad
    nlinarith only [strict,curve,sq_nonneg (z-e)])
  linarith

theorem outer_lower {z h e u v : ℝ} (hz : 0≤z) (he : 0≤e) (hu : 0≤u)
    (balance : 3*e≤h) (curve : h^2-e^2=8*z^2) (outer : u≤3*v) :
    (3*u-v)*z ≤ u*h-v*e := by
  have ⟨ez,hz'⟩ := coordinates hz he balance curve
  have slope := endpoint_gap he balance curve
  have vu : 0≤v := by linarith
  nlinarith only [mul_le_mul_of_nonneg_left slope vu,
    mul_le_mul_of_nonneg_right outer (sub_nonneg.mpr hz')]

/-- Completing the square around the stationary point gives the inner minimum. -/
theorem inner_lower {z h e u v : ℝ} (he : 0≤e) (hv : 0≤v)
    (balance : 3*e≤h) (curve : h^2-e^2=8*z^2) (inner : 3*v≤u) :
    Real.sqrt (8*z^2*(u^2-v^2)) ≤ u*h-v*e := by
  have nonnegative : 0≤u*h-v*e := sub_nonneg.mpr
    (mul_le_mul (by linarith : v≤u) (by linarith : e≤h) he (by linarith))
  apply (Real.sqrt_le_iff).mpr
  refine ⟨nonnegative,?_⟩
  have identity : (u*h-v*e)^2-8*z^2*(u^2-v^2)=(u*e-v*h)^2 := by
    rw [← curve]
    ring
  linarith only [identity,sq_nonneg (u*e-v*h)]

/-- Both bounds hold on the actual signed product curve. -/
theorem trace_bounds {z h d u v : ℝ} (hz : 0≤z) (hu : 0≤u) (hv : 0≤v)
    (onCurve : balanced z h d) :
    lower z u v ≤ u*h+v*d ∧ u*h+v*d ≤ (3*u+v)*z := by
  obtain ⟨bal,cv⟩ := onCurve
  have cv' : h^2-|d|^2=8*z^2 := by rwa [sq_abs]
  have ⟨ez,hz'⟩ := coordinates hz (abs_nonneg d) bal cv'
  constructor
  · have left : lower z u v ≤ u*h-v*|d| := by
      unfold lower
      split_ifs with edge
      · exact outer_lower hz (abs_nonneg d) hu bal cv' edge
      · exact inner_lower (abs_nonneg d) hv bal cv' (le_of_not_ge edge)
    exact left.trans (by linarith only [mul_le_mul_of_nonneg_left (neg_abs_le d) hv])
  · linarith only [mul_le_mul_of_nonneg_left ((le_abs_self d).trans ez) hv,
      mul_le_mul_of_nonneg_left hz' hu]

theorem edge_points {z : ℝ} (hz : 0≤z) :
    balanced z (3*z) z ∧ balanced z (3*z) (-z) := by
  simp only [balanced,abs_neg,abs_of_nonneg hz,le_refl,true_and,neg_sq]
  constructor <;> ring

/-- An explicit minimizer when the slope is strictly inside the stationary branch. -/
theorem stationary_point {z u v : ℝ} (hv : 0≤v) (inner : 3*v<u) :
    let t := Real.sqrt (8*z^2/(u^2-v^2))
    balanced z (u*t) (-v*t) ∧ u*(u*t)+v*(-v*t) = Real.sqrt (8*z^2*(u^2-v^2)) := by
  let K := u^2-v^2
  have kp : 0<K := sub_pos.mpr ((sq_lt_sq₀ hv (by linarith : 0≤u)).mpr (by linarith))
  let t := Real.sqrt (8*z^2/K)
  have tp : 0≤t := Real.sqrt_nonneg _
  have sqt : K*t^2=8*z^2 := by
    dsimp [t]
    rw [Real.sq_sqrt (div_nonneg (by positivity) kp.le),mul_comm K,div_mul_cancel₀ _ kp.ne']
  change balanced z (u*t) (-v*t) ∧ u*(u*t)+v*(-v*t) = Real.sqrt (8*z^2*K)
  constructor
  · refine ⟨?_,?_⟩
    · rw [neg_mul,abs_neg,abs_of_nonneg (mul_nonneg hv tp)]
      linarith only [mul_le_mul_of_nonneg_right inner.le tp]
    · change (u*t)^2-(-v*t)^2=8*z^2
      calc _ = K*t^2 := by dsimp [K]; ring
           _ = _ := sqt
  · have eq : (K*t)^2=8*z^2*K := by
      calc _ = (K*t^2)*K := by ring
           _ = _ := by rw [sqt]
    rw [← eq,Real.sqrt_sq (mul_nonneg kp.le tp)]
    dsimp [K]
    ring

/-- The two bounds are sharp for real points. Integer factor pairs may leave gaps. -/
theorem extrema_attained {z u v : ℝ} (hz : 0≤z) (hv : 0≤v) :
    (∃ h d, balanced z h d ∧ u*h+v*d=lower z u v) ∧
    (∃ h d, balanced z h d ∧ u*h+v*d=(3*u+v)*z) := by
  have ends := edge_points hz
  constructor
  · by_cases edge : u≤3*v
    · exact ⟨3*z,-z,ends.2,by rw [lower,if_pos edge]; ring⟩
    · obtain ⟨onCurve,hit⟩ := stationary_point (z := z) hv (lt_of_not_ge edge)
      exact ⟨_,_,onCurve,by simpa only [lower,if_neg edge] using hit⟩
  · exact ⟨3*z,z,ends.1,by ring⟩

/-- Exact extrema in the range of the signed weighted trace over real balanced factors. -/
theorem extrema {z u v : ℝ} (hz : 0≤z) (hu : 0≤u) (hv : 0≤v) :
    let traces := {t : ℝ | ∃ h d, balanced z h d ∧ u*h+v*d=t}
    IsLeast traces (lower z u v) ∧ IsGreatest traces ((3*u+v)*z) := by
  obtain ⟨low,high⟩ := extrema_attained (u := u) hz hv
  refine ⟨⟨low,?_⟩,⟨high,?_⟩⟩
  · rintro _ ⟨h,d,cv,rfl⟩
    exact (trace_bounds hz hu hv cv).1
  · rintro _ ⟨h,d,cv,rfl⟩
    exact (trace_bounds hz hu hv cv).2

end PrimeFactors.CurvedWeightInterval
