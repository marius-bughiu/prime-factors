import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-! # Signed frequency filters for a single coefficient

A filter with normalized complex weights can remove an unwanted term exactly.
The width of the sampled band limits how well conditioned that cancellation is.
-/
namespace PrimeFactors.SignedIndexNotches

set_option maxHeartbeats 1000000

/-- Complex phase, written explicitly so the geometric estimate can use real trigonometry. -/
noncomputable def phase (t : ℝ) : ℂ := (Real.cos t : ℂ) + Real.sin t * Complex.I

theorem in_disk {θ t : ℝ} (ht : |t|≤θ) (small : θ≤Real.pi/2) :
    ‖1 - (Real.cos θ : ℂ)*phase t‖ ≤ Real.sin θ := by
  have t0 : 0≤θ := (abs_nonneg t).trans ht
  have upper : θ≤Real.pi := by linarith [Real.pi_pos]
  have ordering : Real.cos θ ≤ Real.cos t := by
    simpa only [Real.cos_abs] using Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg t) upper ht
  have ct := Real.cos_nonneg_of_mem_Icc (show θ∈Set.Icc (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith [Real.pi_pos], small⟩)
  have st := Real.sin_nonneg_of_nonneg_of_le_pi t0 upper
  have cube : ‖1-(Real.cos θ : ℂ)*phase t‖^2 ≤ (Real.sin θ)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [phase, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, mul_one, mul_one, add_zero, zero_add, sub_zero, zero_sub, neg_mul, mul_neg, neg_neg]
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq t,
      mul_nonneg ct (sub_nonneg.mpr ordering),
      mul_eq_zero_of_right (Real.cos θ ^ 2) (sub_eq_zero.mpr (Real.sin_sq_add_cos_sq t))]
  nlinarith [norm_nonneg (1 - (Real.cos θ:ℂ)*phase t)]

/-- If the first r positive moments vanish and the zeroth is one, a bounded polynomial
    multiplier can be applied r times with the norm cost A^r. -/
theorem moment_bound {ι : Type*} (s : Finset ι) (z : ι → ℂ) (center : ℂ) (A : ℝ)
    (A0 : 0≤A) (disk : ∀ j∈s, ‖1-center*z j‖ ≤ A) (r : ℕ) (c : ι → ℂ)
    (normed : ∑ j∈s, c j = 1)
    (zero : ∀ k, 0<k → k≤r → ∑ j∈s, c j * (z j)^k = 0) :
    1 ≤ A^r * ∑ j∈s, ‖c j‖ := by
  induction r generalizing c with
  | zero =>
    simpa [normed] using (norm_sum_le s c)
  | succ r ih =>
    let b j := c j*(1-center*z j)
    have shift (k : ℕ) :
        ∑ j∈s, b j*(z j)^k = (∑ j∈s, c j*(z j)^k) - center*(∑ j∈s, c j*(z j)^(k+1)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by dsimp [b]; ring)
    have first : ∑ j∈s, c j*z j=0 := by simpa using zero 1 (by omega) (by omega)
    have b0 : ∑ j∈s, b j=1 := by simpa [normed, first] using shift 0
    have bz (k : ℕ) (pos : 0<k) (le : k≤r) : ∑ j∈s, b j * (z j)^k = 0 := by
      simp [shift, zero k pos (by omega), zero (k+1) (by omega) (by omega)]
    have bnorm : ∑ j∈s, ‖b j‖ ≤ A*∑ j∈s, ‖c j‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      change ‖c j*(1-center*z j)‖ ≤ A*‖c j‖
      rw [norm_mul, mul_comm A]
      exact mul_le_mul_of_nonneg_left (disk j hj) (norm_nonneg _)
    calc
      _ ≤ _ := ih b b0 bz
      _ ≤ A^r*(A*∑ j∈s, ‖c j‖) := mul_le_mul_of_nonneg_left bnorm (pow_nonneg A0 _)
      _ = _ := by rw [pow_succ]; ring

/-- At a log-spaced grid δ,2δ,...,rδ, exact cancellation requires this coefficient norm.
    The phase for a sample at t_j is z_j=exp(i t_j δ), with |t_j δ|≤θ.
    Setting r=1 also applies to any one chosen gap. -/
theorem grid_lower {ι : Type*} (s : Finset ι) (angles : ι → ℝ) (c : ι → ℂ) (r : ℕ)
    {θ : ℝ} (lo : 0≤θ) (small : θ≤Real.pi/2) (band : ∀ j∈s, |angles j|≤θ)
    (normed : ∑ j∈s, c j = 1)
    (zero : ∀ k, 0<k → k≤r → ∑ j∈s, c j * phase (angles j)^k = 0) :
    1 ≤ Real.sin θ ^ r * ∑ j∈s, ‖c j‖ :=
  moment_bound s _ (Real.cos θ) (Real.sin θ)
    (Real.sin_nonneg_of_nonneg_of_le_pi lo (by linarith [Real.pi_pos]))
    (fun j hj => in_disk (band j hj) small) r c normed zero

/-- The two endpoint samples attain equality for a single requested zero. -/
theorem endpoints {θ : ℝ} (pos : 0<θ) (small : θ≤Real.pi/2) :
    ∃ b c : ℂ, b+c=1 ∧ b*phase (-θ)+c*phase θ=0 ∧
      Real.sin θ*(‖b‖+‖c‖)=1 := by
  have st : 0<Real.sin θ := Real.sin_pos_of_pos_of_lt_pi pos (by linarith [Real.pi_pos])
  have unit (t : ℝ) : ‖phase t‖=1 := by simpa only [phase, Complex.ofReal_cos, Complex.ofReal_sin] using Complex.norm_cos_add_sin_mul_I t
  have up := unit θ
  have dn := unit (-θ)
  have dist : ‖phase θ - phase (-θ)‖ = 2*Real.sin θ := by
    have eqn : phase θ - phase (-θ) = (2*Real.sin θ:ℝ)*Complex.I := by
      rw [phase,phase,Real.cos_neg,Real.sin_neg,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_ofNat]
      ring
    rw [eqn, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have nz : phase θ - phase (-θ)≠0 := by intro eqn; simp [eqn] at dist; linarith
  refine ⟨phase θ/(phase θ-phase (-θ)), -phase (-θ)/(phase θ-phase (-θ)), ?_, ?_, ?_⟩
  · field_simp [nz]; ring
  · field_simp [nz]; ring
  · rw [norm_div, norm_div, norm_neg, up, dn, dist]
    field_simp [st.ne']; ring

/-- A polynomial of degree at most r gives a filter using at most r+1 samples on a
    frequency grid. Every specified node is allowed except the target phase one. -/
noncomputable def polynomial (nodes : Finset ℂ) : Polynomial ℂ :=
  ∏ z∈nodes, (Polynomial.X - Polynomial.C z)*Polynomial.C ((1-z)⁻¹)

theorem polynomial_spec (nodes : Finset ℂ) (avoid : 1∉nodes) :
    (polynomial nodes).eval 1=1 ∧ (∀ z∈nodes, (polynomial nodes).eval z=0) ∧
      (polynomial nodes).natDegree ≤ nodes.card := by
  classical
  constructor
  · rw [polynomial, Polynomial.eval_prod]
    apply Finset.prod_eq_one
    intro z hz
    have ne : 1-z ≠ 0 := sub_ne_zero.mpr (fun eqn => avoid (eqn.symm ▸ hz))
    simp [Polynomial.eval_mul, ne]
  constructor
  · intro z hz
    rw [polynomial, Polynomial.eval_prod]
    apply Finset.prod_eq_zero hz
    simp
  · unfold polynomial
    apply (Polynomial.natDegree_prod_le ..).trans
    calc
      _ ≤ ∑ _ ∈ nodes, (1:ℕ) := by
        apply Finset.sum_le_sum
        intro z hz
        exact (Polynomial.natDegree_mul_le ..).trans (by simp)
      _ = _ := by simp

end PrimeFactors.SignedIndexNotches
