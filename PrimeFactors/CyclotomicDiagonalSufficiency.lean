import PrimeFactors.CyclotomicDiagonalEstimate

/-! Upper error of the equal-coordinate estimate for the positive cyclotomic
reading. Small sum deficits, and in particular small squared factor gaps,
guarantee that the estimate meets the required tolerance. -/

namespace PrimeFactors.CyclotomicDiagonalSufficiency

open Real Set CyclotomicValueSlope CyclotomicProductCurve CyclotomicDiagonalEstimate
open private PrimeFactors.CyclotomicProductCurve.response_deriv
  PrimeFactors.CyclotomicProductCurve.total_deriv from PrimeFactors.CyclotomicProductCurve

/-- The derivative of the Bernoulli generating function is at least −1
everywhere on the positive axis. -/
theorem derivative_lower {z : ℝ} (pos : 0 < z) : -1 ≤ deriv f z := by
  rw [(hasDeriv pos).deriv]
  apply (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr (one_lt_exp_iff.mpr pos)))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left (add_one_le_exp z) (exp_pos z).le]

private theorem kernel_change {u v : ℝ} (pos : 0 < u) (uv : u ≤ v) :
    -(v-u) ≤ f v-f u := by
  obtain eq | lt := uv.eq_or_lt
  · simp [eq]
  have cont : ContinuousOn f (Icc u v) := fun t ht =>
    (hasDeriv (pos.trans_le ht.1)).continuousAt.continuousWithinAt
  have diff : DifferentiableOn ℝ f (Ioo u v) := fun t ht =>
    (hasDeriv (pos.trans ht.1)).differentiableAt.differentiableWithinAt
  obtain ⟨t,ht,eq⟩ := exists_deriv_eq_slope f lt cont diff
  have slope := derivative_lower (pos.trans ht.1)
  rw [eq] at slope
  linarith only [(le_div_iff₀ (sub_pos.mpr lt)).mp slope]

private theorem response_bounds {u v : ℝ} (pos : 0 < u) (uv : u ≤ v) (top : v ≤ 1/4) :
    0 ≤ term u*term v ∧ term u*term v ≤ 1/16 := by
  have nonneg {z : ℝ} (h : 0 ≤ z) : 0 ≤ term z :=
    sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr h))
  have upper (z : ℝ) : term z ≤ z := by unfold term; linarith only [add_one_le_exp (-z)]
  constructor
  · exact mul_nonneg (nonneg pos.le) (nonneg (pos.le.trans uv))
  · have hup := (upper u).trans (uv.trans top)
    have hvp := (upper v).trans top
    exact (mul_le_mul hup hvp (nonneg (pos.le.trans uv)) (by norm_num)).trans_eq (by norm_num)

private theorem normalized {K v w : ℝ} (kp : 0 < K) (vp : 0 < v) (ordered : v ≤ w)
    (start : K/v ≤ v) (top : w ≤ 1/4) :
    response K v-response K w ≤ (total K w-total K v)/16 := by
  let F := fun z => response K z+total K z/16
  have diff {z : ℝ} (zp : 0 < z) : HasDerivAt F
      (response K z*(f z-f (K/z))/z+((z-K/z)/z)/16) z :=
    (PrimeFactors.CyclotomicProductCurve.response_deriv kp zp).add
      ((PrimeFactors.CyclotomicProductCurve.total_deriv zp).div_const 16)
  have mono : MonotoneOn F (Icc v w) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc v w)
    · exact fun z hz => (diff (vp.trans_le hz.1)).continuousAt.continuousWithinAt
    · exact fun z hz => (diff (vp.trans_le (interior_subset hz).1)).hasDerivWithinAt
    · intro z hz
      obtain ⟨vz,zw⟩ := interior_subset hz
      have zp := vp.trans_le vz
      have order : K/z ≤ z := (div_le_div_of_nonneg_left kp.le vp vz).trans (start.trans vz)
      have h := response_bounds (div_pos kp zp) order (zw.trans top)
      change 0 ≤ response K z ∧ response K z ≤ 1/16 at h
      have slope := mul_le_mul_of_nonneg_left (kernel_change (div_pos kp zp) order) h.1
      have small := mul_le_mul_of_nonneg_right h.2 (sub_nonneg.mpr order)
      rw [show response K z*(f z-f (K/z))/z+((z-K/z)/z)/16 =
        (response K z*(f z-f (K/z))+(z-K/z)/16)/z by ring]
      exact div_nonneg (by linarith only [slope,small]) zp.le
  have comp := mono (left_mem_Icc.mpr ordered) (right_mem_Icc.mpr ordered) ordered
  dsimp only [F] at comp
  linarith

/-- At fixed product, the error made by substituting its square root for both
factors grows by at most 1/(128B) times the resulting sum deficit. -/
theorem error_upper {B p q : ℝ} (pos : 0 < B) (low : B ≤ p) (order : p ≤ q)
    (high : q ≤ 2*B) :
    diagonal (p*q) B-trial B p q ≤ (p+q-2*sqrt (p*q))/(128*B) := by
  let D := 8*B
  let r := sqrt (p*q)
  have dp : 0 < D := by dsimp [D]; positivity
  have pp := pos.trans_le low
  have qp := pp.trans_le order
  have rp : 0 < r := sqrt_pos_of_pos (mul_pos pp qp)
  have rq : r ≤ q := (sqrt_le_left qp.le).mpr (by
    simpa only [sq] using mul_le_mul_of_nonneg_right order qp.le)
  have square : r^2=p*q := sq_sqrt (mul_nonneg pp.le qp.le)
  let K := (r/D)^2
  have kp : 0 < K := sq_pos_of_pos (div_pos rp dp)
  have at_r : K/(r/D)=r/D := by dsimp only [K]; field_simp; ring
  have at_q : K/(q/D)=p/D := by dsimp only [K]; field_simp; rw [square]; ring
  have top : q/D ≤ 1/4 := (div_le_iff₀ dp).mpr (by dsimp [D]; linarith)
  have result := normalized kp (div_pos rp dp) (div_le_div_of_nonneg_right rq dp.le) at_r.le top
  simp only [total,response,at_r,at_q] at result
  calc
    _ ≤ (p/D+q/D-(r/D+r/D))/16 := result
    _ = _ := by dsimp [D,r]; ring

private theorem deficit_nonneg {p q : ℝ} (pp : 0 ≤ p) (pq : p ≤ q) :
    0 ≤ p+q-2*sqrt (p*q) := by
  have root : sqrt (p*q) ≤ (p+q)/2 := (sqrt_le_left (by linarith)).mpr
    (by nlinarith only [sq_nonneg (q-p)])
  linarith

theorem deficit_sufficient {B p q : ℝ} (pos : 0 < B) (low : B ≤ p) (order : p ≤ q)
    (high : q ≤ 2*B) (near : p+q-2*sqrt (p*q) ≤ 1/64) :
    |diagonal (p*q) B-trial B p q| ≤ 1/(8192*B) := by
  have deficit := deficit_nonneg (pos.trans_le low).le order
  have nn := (div_nonneg deficit (by positivity)).trans (error_lower pos low order high)
  rw [abs_of_nonneg nn]
  apply (error_upper pos low order high).trans
  calc
    _ ≤ (1/64)/(128*B) := div_le_div_of_nonneg_right near (by positivity)
    _ = _ := by ring

private theorem deficit_of_gap {B p q : ℝ} (pos : 0 < B) (low : B ≤ p) (order : p ≤ q)
    (near : (q-p)^2 ≤ B/16) : p+q-2*sqrt (p*q) ≤ 1/64 := by
  have p0 := (pos.trans_le low).le
  have q0 := p0.trans order
  have root := sq_sqrt (mul_nonneg p0 q0)
  have small : p ≤ sqrt (p*q) := le_sqrt_of_sq_le (by
    simpa only [sq] using mul_le_mul_of_nonneg_left order p0)
  have high : 4*B ≤ p+q+2*sqrt (p*q) := by linarith
  have size := mul_le_mul_of_nonneg_left high (deficit_nonneg p0 order)
  have scaled : (p+q-2*sqrt (p*q))*B ≤ (1/64)*B := by
    nlinarith only [near,root,size]
  exact (mul_le_mul_iff_of_pos_right pos).mp scaled

/-- A sufficient condition on the ordinary prime gap for the product-only
diagonal estimate to achieve the prescribed precision. -/
theorem gap_sufficient {B : ℝ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (pq : p<q)
    (pos : 0 < B) (low : B ≤ p) (high : (q:ℝ) ≤ 2*B) (near : ((q:ℝ)-p)^2 ≤ B/16) :
    |diagonal (p*q : ℕ) B-reading (p*q) B| ≤ 1/(8192*B) := by
  rw [actual_value hp hq pq,Nat.cast_mul]
  have order : (p:ℝ) ≤ q := by exact_mod_cast pq.le
  exact deficit_sufficient pos low order high (deficit_of_gap pos low order near)

/-- The pair 101,103 attains the sufficient squared-gap threshold exactly.
Fermat's first midpoint also gives the factors. -/
theorem control_10403 :
    101*103 = 10403 ∧ (103-101 : ℝ)^2 = 64/16 ∧
    |diagonal 10403 64-reading 10403 64| ≤ 1/(8192*64) ∧
    ceilSqrt 10403 = 102 ∧ 102^2 = 10403+1^2 := by
  have lo : ¬ceilSqrt 10403 ≤ 101 := fun h => (by decide : ¬10403 ≤ 101^2) (ceilSqrt_le_iff.mp h)
  have hi : ceilSqrt 10403 ≤ 102 := ceilSqrt_le_iff.mpr (by decide)
  refine ⟨by decide,by norm_num,?_,by omega,by decide⟩
  exact gap_sufficient (p:=101) (q:=103) (by norm_num) (by norm_num) (by decide)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end PrimeFactors.CyclotomicDiagonalSufficiency
