import PrimeFactors.InverseCyclotomicMeasurements
import PrimeFactors.CyclotomicValueSlope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Separation in the prime sum for one bounded evaluation at a positive
real point. The two factors can be relaxed to positive real numbers with
fixed product, so the comparison also covers trial sums between integers. -/
namespace PrimeFactors.CyclotomicProductCurve

open Set Polynomial CyclotomicValueSlope
open scoped Polynomial

noncomputable def term (u : ℝ) := 1-Real.exp (-u)
noncomputable def response (K v : ℝ) := term (K/v)*term v
noncomputable def total (K v : ℝ) := K/v+v

private theorem term_deriv (u : ℝ) : HasDerivAt term (Real.exp (-u)) u := by
  simpa [term] using ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u).neg.exp)

private theorem term_mul {u : ℝ} (pos : 0<u) :
    term u*f u=u*Real.exp (-u) := by
  have ep : Real.exp u≠0 := (Real.exp_pos u).ne'
  have den : Real.exp u-1≠0 := sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr pos).ne'
  unfold term f
  rw [Real.exp_neg]
  field_simp
  ring

private theorem product_rule {u v h g r t : ℝ} (vp : 0<v)
    (l : t*h=v*Real.exp (-v)) (a : r*g=u*Real.exp (-u)) :
    r*t*(h-g)/v=Real.exp (-u)*(-u/v)*t+r*Real.exp (-v) := by
  apply (div_eq_iff vp.ne').mpr
  calc
    _ = r*(t*h)-t*(r*g) := by ring
    _ = _ := by rw [l,a]; field_simp; ring

private theorem response_deriv {K v : ℝ} (kp : 0<K) (vp : 0<v) :
    HasDerivAt (response K) (response K v*(f v-f (K/v))/v) v := by
  have inv : HasDerivAt (fun z : ℝ => K/z) (-(K/v)/v) v := by
    convert (hasDerivAt_const v K).div (hasDerivAt_id v) vp.ne' using 1
    simp
    ring
  have derivative := ((term_deriv (K/v)).comp v inv).mul (term_deriv v)
  convert derivative using 1
  exact product_rule vp (term_mul vp) (term_mul (div_pos kp vp))

private theorem total_deriv {K v : ℝ} (vp : 0<v) :
    HasDerivAt (total K) ((v-K/v)/v) v := by
  convert ((hasDerivAt_const v K).div (hasDerivAt_id v) vp.ne').add (hasDerivAt_id v) using 1
  simp
  field_simp
  ring

private noncomputable def potential (K v : ℝ) := response K v+total K v/324

private theorem potential_deriv {K v : ℝ} (kp : 0<K) (vp : 0<v) :
    HasDerivAt (potential K)
      (response K v*(f v-f (K/v))/v+((v-K/v)/v)/324) v :=
  (response_deriv kp vp).add ((total_deriv vp).div_const 324)

private theorem derivative_sign {r d g : ℝ} (rd : (1:ℝ)/81≤r) (dp : 0≤d)
    (gd : g≤ -d/4) : r*g+d/324≤0 := by
  have a := mul_le_mul_of_nonneg_left gd (by linarith : 0≤r)
  have b := mul_le_mul_of_nonneg_right rd dp
  linarith

theorem compare_on {K v w : ℝ} (kp : 0<K) (vp : 0<v) (order : v≤w)
    (low : 1/8≤K/w) (start : K/v≤v) (high : w≤1/4) :
    (total K w-total K v)/324 ≤ response K v-response K w := by
  have anti : AntitoneOn (potential K) (Icc v w) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v w)
    · exact fun z hz => (potential_deriv kp (vp.trans_le hz.1)).continuousAt.continuousWithinAt
    · exact fun z hz => (potential_deriv kp (vp.trans_le (interior_subset hz).1)).differentiableAt.differentiableWithinAt
    · intro z hz
      obtain ⟨vz,zw⟩ := interior_subset hz
      have zp := vp.trans_le vz
      have lower : 1/8≤K/z := low.trans (div_le_div_of_nonneg_left kp.le zp zw)
      have upper : K/z≤z := (div_le_div_of_nonneg_left kp.le vp vz).trans (start.trans vz)
      have h := derivative_sign (r:=response K z) (response_lower lower (lower.trans upper))
        (sub_nonneg.mpr upper) (slope (div_pos kp zp) upper (zw.trans high))
      rw [(potential_deriv kp zp).deriv]
      calc
        _ = (response K z*(f z-f (K/z)) + (z-K/z)/324)/z := by ring
        _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg h zp.le
  have both := anti (left_mem_Icc.mpr order) (right_mem_Icc.mpr order) order
  unfold potential at both
  linarith

/-- Reading at the point exp(−1/(8B)) for real trial factors. -/
noncomputable def trial (B p q : ℝ) := term (p/(8*B))*term (q/(8*B))

theorem ordered_separation {B p q a b : ℝ} (bp : 0<B) (p0 : B≤p) (a0 : B≤a)
    (pq : p≤q) (qb : q≤b) (limit : b≤2*B) (same : p*q=a*b) :
    (a+b-(p+q))/(2592*B) ≤ trial B p q-trial B a b := by
  let d := 8*B
  have dp : 0<d := by dsimp [d]; positivity
  have q0 := (bp.trans_le p0).trans_le pq
  have b0 := q0.trans_le qb
  let K := (p/d)*(q/d)
  have kp : 0<K := mul_pos (div_pos (bp.trans_le p0) dp) (div_pos q0 dp)
  have kv : K/(q/d)=p/d := by dsimp [K]; field_simp; ring
  have kw : K/(b/d)=a/d := by
    dsimp [K]
    field_simp
    linear_combination d^2*same
  have low : 1/8≤K/(b/d) := by
    rw [kw]
    apply (le_div_iff₀ dp).mpr
    dsimp [d]; linarith
  have high : b/d≤1/4 := by
    apply (div_le_iff₀ dp).mpr
    dsimp [d]; linarith
  have result := compare_on kp (div_pos q0 dp) (div_le_div_of_nonneg_right qb dp.le)
    low (kv ▸ div_le_div_of_nonneg_right pq dp.le) high
  simp only [total,response,kv,kw] at result
  calc
    _ = (a/d+b/d-(p/d+q/d))/324 := by dsimp [d]; ring
    _ ≤ _ := result

noncomputable def reading (N : ℕ) (B : ℝ) : ℝ :=
  (InverseCyclotomicMeasurements.polynomial N).eval₂ (Int.castRingHom ℝ) (Real.exp (-(1/(8*B))))

/-- The true real response coincides with the public-index polynomial
evaluated at the single point exp(−1/(8B)). -/
theorem actual_value {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q) (B : ℝ) :
    reading (p*q) B=trial B p q := by
  simp only [reading,InverseCyclotomicMeasurements.sparse hp hq order,eval₂_mul,eval₂_sub,
    eval₂_one,eval₂_pow,eval₂_X,trial,term,←Real.exp_nat_mul]
  ring_nf

private theorem increasing_sum {p q a b : ℝ} (same : p*q=a*b) (pq : p≤q) (qb : q≤b)
    (bp : 0<b) : p+q≤a+b := by
  have id : b*(a+b-(p+q))=(b-q)*(b-p) := by linear_combination -same
  have nn : 0≤b*(a+b-(p+q)) := id ▸ mul_nonneg (sub_nonneg.mpr qb) (sub_nonneg.mpr (pq.trans qb))
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right nn bp)

theorem separation {B p q a b : ℝ} (pos : 0<B) (p0 : B≤p) (a0 : B≤a)
    (pq : p≤q) (ab : a≤b) (qh : q≤2*B) (bh : b≤2*B) (same : p*q=a*b) :
    |(a+b)-(p+q)|/(2592*B) ≤ |trial B p q-trial B a b| := by
  rcases le_total q b with order|order
  · rw [abs_of_nonneg (sub_nonneg.mpr (increasing_sum same pq order ((pos.trans_le a0).trans_le ab)))]
    exact (ordered_separation pos p0 a0 pq order bh same).trans (le_abs_self _)
  · rw [abs_sub_comm (a+b),abs_of_nonneg (sub_nonneg.mpr
      (increasing_sum same.symm ab order ((pos.trans_le p0).trans_le pq))),abs_sub_comm (trial B p q)]
    exact (ordered_separation pos a0 p0 ab order qh same.symm).trans (le_abs_self _)

/-- A candidate can have nonintegral factors. If its sum is integral and its
response is compatible with the one rounded input, the sum is the true one. -/
theorem unique_sum {p q s : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q)
    {B a b y : ℝ} (pos : 0<B) (p0 : B≤p) (qh : (q:ℝ)≤2*B) (a0 : B≤a)
    (ab : a≤b) (bh : b≤2*B) (prod : (p:ℝ)*q=a*b) (total_s : a+b=(s:ℝ))
    (actual : |y-reading (p*q) B|≤1/(8192*B)) (candidate : |y-trial B a b|≤1/(8192*B)) :
    s=p+q := by
  rw [actual_value hp hq order] at actual
  have apart := separation pos p0 a0 (by exact_mod_cast order.le) ab qh bh prod
  rw [total_s,←Nat.cast_add] at apart
  have both := abs_sub_le (trial B p q) y (trial B a b)
  rw [abs_sub_comm (trial B p q) y] at both
  have gap : |(s:ℝ)-(p+q:ℕ)| < 1 := by
    have bound : |(s:ℝ)-(p+q:ℕ)|/(2592*B) ≤ 2/(8192*B) := calc
      _ ≤ 1/(8192*B)+1/(8192*B) := apart.trans (both.trans (add_le_add actual candidate))
      _ = _ := by ring
    have right : 2/(8192*B)<1/(2592*B) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
      linarith
    exact (div_lt_div_iff_of_pos_right (by positivity : 0<2592*B)).mp (bound.trans_lt right)
  obtain ⟨lower,upper⟩ := abs_lt.mp gap
  rcases lt_trichotomy s (p+q) with h|eq|h
  · have h' : (s:ℝ)+1≤((p+q:ℕ):ℝ) := by exact_mod_cast h
    exfalso
    linarith
  · exact eq
  · have h' : ((p+q:ℕ):ℝ)+1≤(s:ℝ) := by exact_mod_cast h
    exfalso
    linarith

end PrimeFactors.CyclotomicProductCurve
