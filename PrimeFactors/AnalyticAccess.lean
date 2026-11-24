import PrimeFactors.DivisorSignal

namespace PrimeFactors

/-- Remove the known common frequency. The remaining wave oscillates at
half the logarithm of the ratio of the two primes. -/
noncomputable def ratioWave (n : ℕ) [NeZero n] (t : ℝ) : ℝ :=
  Real.cos (t * Real.log n / 2) - boundaryProbe n t / 2

theorem ratioWave_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (distinct : p ≠ q)
    [NeZero (p * q)] {t : ℝ} (ht : 0 < t) :
    ratioWave (p * q) t = Real.cos (t * ((Real.log q - Real.log p) / 2)) := by
  rw [ratioWave, boundaryProbe_semiprime hp hq distinct ht, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  rw [show t * (Real.log p + Real.log q) / 2 =
    t * Real.log q / 2 + t * Real.log p / 2 by ring,
    show t * ((Real.log q - Real.log p) / 2) = t * Real.log q / 2 - t * Real.log p / 2 by ring,
    Real.cos_add, Real.cos_sub]
  ring

/-- A query constructed from the left endpoint and width of the current interval.
The phase at its midpoint is π/2 modulo 2π. -/
noncomputable def ratioQueryHeight (a w : ℝ) : ℝ :=
  ((4 * (⌊a / (2*w)⌋₊ : ℝ) + 1) * Real.pi) / (2*a + w)

/-- All candidate phases stay on a single monotone arc. Even near zero,
the phase span is greater than π/5. -/
theorem ratioQueryHeight_span {a w : ℝ} (ha : 0 ≤ a) (hw : 0 < w) :
    0 < ratioQueryHeight a w ∧
    Real.pi / 5 < ratioQueryHeight a w * w ∧ ratioQueryHeight a w * w ≤ Real.pi := by
  let k : ℝ := ⌊a / (2*w)⌋₊
  have denom : 0 < 2*a+w := by linarith
  have low : k * (2*w) ≤ a := (le_div_iff₀ (by positivity)).mp (Nat.floor_le (by positivity))
  have high : a < (k+1) * (2*w) := (div_lt_iff₀ (by positivity)).mp (Nat.lt_floor_add_one _)
  have hk : 0 ≤ k := Nat.cast_nonneg _
  change 0 < ((4*k+1)*Real.pi)/(2*a+w) ∧ _ ∧ _
  refine ⟨div_pos (mul_pos (by linarith) Real.pi_pos) denom, ?_, ?_⟩
  · change Real.pi/5 < ((4*k+1)*Real.pi)/(2*a+w)*w
    rw [div_mul_eq_mul_div, lt_div_iff₀ denom]
    have h : 2*a+w < 5*((4*k+1)*w) := by nlinarith [mul_nonneg hk hw.le]
    nlinarith [mul_lt_mul_of_pos_left h Real.pi_pos]
  · change ((4*k+1)*Real.pi)/(2*a+w)*w ≤ Real.pi
    rw [div_mul_eq_mul_div, div_le_iff₀ denom]
    have h : (4*k+1)*w ≤ 2*a+w := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h Real.pi_pos.le]

private theorem ratioQuery_centered_cos {a w : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (d : ℝ) :
    Real.cos (ratioQueryHeight a w * d) =
      -Real.sin (ratioQueryHeight a w * (d - (a+w/2))) := by
  let k := ⌊a / (2*w)⌋₊
  let t := ratioQueryHeight a w
  have midpoint : t*(a+w/2) = Real.pi/2 + k*(2*Real.pi) := by
    dsimp [t, ratioQueryHeight, k]
    field_simp [show 2*a+w ≠ 0 by linarith]
    ring
  have phase : t*d = (t*(d-(a+w/2)) + Real.pi/2) + k*(2*Real.pi) := by
    linarith [show t*d = t*(d-(a+w/2)) + t*(a+w/2) by ring]
  change Real.cos (t*d) = -Real.sin _
  rw [phase, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi_div_two]

/-- An estimate of the cosine with absolute error at most one tenth chooses a
three-quarter interval containing the true log-ratio. Its sign is sufficient. -/
theorem ratioQuery_contract {a w d y : ℝ} (ha : 0 ≤ a) (hw : 0 < w)
    (lo : a ≤ d) (hi : d ≤ a+w)
    (error : |y - Real.cos (ratioQueryHeight a w * d)| ≤ 1/10) :
    (0 ≤ y → a ≤ d ∧ d ≤ a+3*w/4) ∧ (y < 0 → a+w/4 ≤ d ∧ d ≤ a+w) := by
  let t := ratioQueryHeight a w
  obtain ⟨ht, gain, span⟩ := ratioQueryHeight_span ha hw
  change 0 < t at ht
  change Real.pi / 5 < t*w at gain
  change t*w ≤ Real.pi at span
  let u := t*(d-(a+w/2))
  have phase : |u| ≤ Real.pi/2 := by
    apply abs_le.mpr
    dsimp [u]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left lo ht.le]
    · nlinarith [mul_le_mul_of_nonneg_left hi ht.le]
  change |y - Real.cos (t*d)| ≤ 1/10 at error
  rw [show Real.cos (t*d) = -Real.sin u from ratioQuery_centered_cos ha hw d] at error
  obtain ⟨errlo, errhi⟩ := abs_le.mp error
  have chord := Real.mul_abs_le_abs_sin phase
  constructor
  · intro sign
    refine ⟨lo, ?_⟩
    by_contra! h
    have hu : Real.pi/20 < u := by
      dsimp [u]
      nlinarith [mul_lt_mul_of_pos_left h ht]
    have hu₀ : 0 < u := by linarith [Real.pi_pos]
    have su := Real.sin_pos_of_pos_of_lt_pi hu₀ (by linarith [(abs_le.mp phase).2, Real.pi_pos])
    rw [abs_of_pos hu₀, abs_of_pos su] at chord
    have scale : (2 / Real.pi) * (Real.pi/20) = 1/10 := by field_simp; ring
    linarith [mul_lt_mul_of_pos_left hu (show 0 < 2 / Real.pi by positivity)]
  · intro sign
    refine ⟨?_, hi⟩
    by_contra! h
    have hu : u < -(Real.pi/20) := by
      dsimp [u]
      nlinarith [mul_lt_mul_of_pos_left h ht]
    have hu₀ : u < 0 := by linarith [Real.pi_pos]
    have su := Real.sin_neg_of_neg_of_neg_pi_lt hu₀ (by linarith [(abs_le.mp phase).1, Real.pi_pos])
    rw [abs_of_neg hu₀, abs_of_neg su] at chord
    have scale : (2 / Real.pi) * (Real.pi/20) = 1/10 := by field_simp; ring
    linarith [mul_lt_mul_of_pos_left (neg_lt_neg hu) (show 0 < 2 / Real.pi by positivity)]

/-- Width of the uncertainty interval after k bounded-error measurements. -/
noncomputable def ratioWidth (k : ℕ) : ℝ := (3/4 : ℝ)^k

/-- Left endpoint selected from the observed signs only. -/
noncomputable def ratioLeft (readWave : ℝ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k+1 =>
    let a := ratioLeft readWave k
    let w := ratioWidth k
    if 0 ≤ readWave (ratioQueryHeight a w) then a else a+w/4

/-- Even adversarial errors at each query preserve containment at every step. -/
theorem ratioLeft_encloses {d : ℝ} (hd : 0 ≤ d) (upper : d ≤ 1) (readWave : ℝ → ℝ)
    (accuracy : ∀ t, 0 < t → |readWave t - Real.cos (t*d)| ≤ 1/10) (k : ℕ) :
    0 ≤ ratioLeft readWave k ∧ ratioLeft readWave k ≤ d ∧
      d ≤ ratioLeft readWave k + ratioWidth k := by
  induction k with
  | zero => simpa [ratioLeft, ratioWidth] using And.intro (le_refl (0:ℝ)) (And.intro hd upper)
  | succ k ih =>
    let a := ratioLeft readWave k
    let w := ratioWidth k
    let t := ratioQueryHeight a w
    have wpos : 0 < w := by dsimp [w, ratioWidth]; positivity
    obtain ⟨apos,lo,hi⟩ := ih
    obtain ⟨left,right⟩ := ratioQuery_contract apos wpos lo hi (accuracy t
      (ratioQueryHeight_span apos wpos).1)
    change 0 ≤ a at apos
    have next : ratioWidth (k+1) = 3*w/4 := by dsimp [w, ratioWidth]; rw [pow_succ]; ring
    rw [next]
    simp only [ratioLeft]
    change 0 ≤ (if 0 ≤ readWave t then a else a+w/4) ∧ _ ∧ _
    by_cases h : 0 ≤ readWave t
    · simp only [show ratioQueryHeight (ratioLeft readWave k) (ratioWidth k) = t from rfl,
        if_pos h]
      exact ⟨apos, left h⟩
    · simp only [show ratioQueryHeight (ratioLeft readWave k) (ratioWidth k) = t from rfl,
        if_neg h]
      obtain ⟨lo',hi'⟩ := right (lt_of_not_ge h)
      change a+w/4 ≤ d at lo'
      change d ≤ a+w at hi'
      exact ⟨by linarith, lo', by change d ≤ a+w/4+3*w/4; linarith⟩

/-- Distinct positive integers up to M give log-values separated by at least 1/M. -/
private theorem log_integer_separation {x y M : ℕ} (hx : 0 < x) (hxy : x < y) (hy : y ≤ M) :
    1/(M : ℝ) ≤ Real.log y - Real.log x := by
  have x₀ : 0 < (x : ℝ) := by exact_mod_cast hx
  have y₀ : 0 < (y : ℝ) := by exact_mod_cast hx.trans hxy
  have step : (x : ℝ)+1 ≤ y := by exact_mod_cast (Nat.succ_le_of_lt hxy)
  calc
    1/(M : ℝ) ≤ 1/(y : ℝ) := one_div_le_one_div_of_le y₀ (by exact_mod_cast hy)
    _ ≤ ((y : ℝ)-x)/y := (div_le_div_iff_of_pos_right y₀).2 (by linarith)
    _ = 1-((y : ℝ)/x)⁻¹ := by field_simp
    _ ≤ Real.log ((y : ℝ)/x) := Real.one_sub_inv_le_log_of_pos (div_pos y₀ x₀)
    _ = _ := Real.log_div y₀.ne' x₀.ne'

/-- A final interval of width < 1/M contains at most one translated log of a
positive candidate up to M. The translation can be half the log of the input. -/
theorem ratio_interval_unique {x y M : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hMx : x ≤ M) (hMy : y ≤ M) {a w translation : ℝ} (short : w < 1/(M : ℝ))
    (xlo : a ≤ Real.log x-translation) (xhi : Real.log x-translation ≤ a+w)
    (ylo : a ≤ Real.log y-translation) (yhi : Real.log y-translation ≤ a+w) : x = y := by
  by_contra ne
  rcases lt_or_gt_of_ne ne with h | h
  · linarith [log_integer_separation hx h hMy]
  · linarith [log_integer_separation hy h hMx]

/-- Given a constant-error evaluator of the original boundary probe, the translated
log of the actual larger factor stays in every interval selected from N. -/
theorem factor_log_in_ratio_interval {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p < q)
    (bal : q ≤ 2*p) [NeZero (p*q)] (readProbe : ℝ → ℝ)
    (accuracy : ∀ t, 0 < t → |readProbe t - boundaryProbe (p*q) t| ≤ 1/5) (k : ℕ) :
    let readWave := fun t => Real.cos (t * Real.log (p*q : ℕ) / 2) - readProbe t/2
    let d := Real.log q - Real.log (p*q : ℕ)/2
    ratioLeft readWave k ≤ d ∧ d ≤ ratioLeft readWave k + ratioWidth k := by
  let d := (Real.log q - Real.log p)/2
  have ppos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have qpos : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  have logs := Real.log_lt_log ppos (by exact_mod_cast ord : (p:ℝ)<q)
  have logn : Real.log (p*q : ℕ) = Real.log p + Real.log q := by
    rw [Nat.cast_mul, Real.log_mul ppos.ne' qpos.ne']
  have balanced := Real.log_le_log qpos (by exact_mod_cast bal : (q:ℝ) ≤ 2*p)
  rw [Real.log_mul (by norm_num) ppos.ne'] at balanced
  have nonneg : 0 ≤ d := by dsimp [d]; linarith
  have bounded : d ≤ 1 := by
    dsimp [d]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  let readWave := fun t => Real.cos (t * Real.log (p*q : ℕ) / 2) - readProbe t/2
  have err (t : ℝ) (ht : 0 < t) : |readWave t - Real.cos (t*d)| ≤ 1/10 := by
    rw [show Real.cos (t*d) = ratioWave (p*q) t from
      (ratioWave_semiprime hp hq ord.ne ht).symm]
    dsimp only [readWave, ratioWave]
    obtain ⟨low, high⟩ := abs_le.mp (accuracy t ht)
    apply abs_le.mpr
    constructor <;> linarith
  change ratioLeft readWave k ≤ _ ∧ _ ≤ ratioLeft readWave k + _
  rw [show Real.log q - Real.log (p*q : ℕ)/2 = d by rw [logn]; dsimp [d]; ring]
  exact (ratioLeft_encloses nonneg bounded readWave err k).2

private theorem ratio_cos_lipschitz (x y : ℝ) : |Real.cos x-Real.cos y| ≤ |x-y| := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul]
  simp only [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have one : |Real.sin ((x+y)/2)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have last : |Real.sin ((x-y)/2)| ≤ |x-y|/2 := by
    simpa only [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using
      Real.abs_sin_le_abs (x := (x-y)/2)
  have major := mul_le_mul one last (abs_nonneg _) zero_le_one
  linarith

/-- The rational height fed to an evaluator may have fixed absolute error:
over 0 ≤ d ≤ 1, the remaining cosine costs at most that much extra error. -/
theorem ratioWave_height_error {d t t' y : ℝ} (lo : 0 ≤ d) (hi : d ≤ 1)
    (sample : |y-Real.cos (t'*d)| ≤ 1/20) (height : |t'-t| ≤ 1/20) :
    |y-Real.cos (t*d)| ≤ 1/10 := by
  have h := ratio_cos_lipschitz (t'*d) (t*d)
  rw [← sub_mul, abs_mul, abs_of_nonneg lo] at h
  have bound := mul_le_mul_of_nonneg_left hi (abs_nonneg (t'-t))
  linarith [abs_sub_le y (Real.cos (t'*d)) (Real.cos (t*d))]

/-- Two frequencies within 2ε/T remain consistent with a common adversarial
ε-accurate response at *every* height through T, including adaptive selections.
This is a result about the continuous cosine measurement model. -/
theorem ratioWave_common_responses {d d' T ε : ℝ} (close : T*|d-d'| ≤ 2*ε) :
    ∃ response : ℝ → ℝ, ∀ t, 0 ≤ t → t ≤ T →
      |response t - Real.cos (t*d)| ≤ ε ∧ |response t - Real.cos (t*d')| ≤ ε := by
  refine ⟨fun t => (Real.cos (t*d) + Real.cos (t*d'))/2, ?_⟩
  intro t ht bound
  have diff := ratio_cos_lipschitz (t*d) (t*d')
  rw [← mul_sub, abs_mul, abs_of_nonneg ht] at diff
  have dist := mul_le_mul_of_nonneg_right bound (abs_nonneg (d-d'))
  obtain ⟨low,high⟩ := abs_le.mp (diff.trans (dist.trans close))
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

private theorem ratio_sinh_le_sin {x : ℝ} (x₀ : 0 ≤ x) (xmax : x ≤ Real.log 2) :
    Real.sinh x ≤ 4 * Real.sin x := by
  have expBound : Real.exp x ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr xmax
  have logBound := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have sinBound := Real.mul_le_sin x₀ (by linarith [Real.two_le_pi])
  have half : (1/2 : ℝ) ≤ 2/Real.pi := (le_div_iff₀ Real.pi_pos).2 (by linarith [Real.pi_le_four])
  have ex := Real.add_one_le_exp (-2*x)
  have shift : Real.exp (-2*x) * Real.exp x = Real.exp (-x) := by rw [← Real.exp_add]; congr 1; ring
  rw [Real.sinh_eq]
  nlinarith [mul_le_mul_of_nonneg_right ex (Real.exp_pos x).le,
    mul_le_mul_of_nonneg_right expBound x₀, mul_le_mul_of_nonneg_right half x₀]

/-- On the balanced range, factor sum is well-conditioned as a function of
the cosine, including at zero where the derivative of the cosine vanishes. -/
theorem ratio_cosh_condition {a b : ℝ} (a₀ : 0 ≤ a) (b₀ : 0 ≤ b)
    (aMax : a ≤ Real.log 2) (bMax : b ≤ Real.log 2) :
    |Real.cosh a - Real.cosh b| ≤ 4 * |Real.cos a - Real.cos b| := by
  wlog ordered : a ≤ b generalizing a b
  · simpa only [abs_sub_comm (Real.cosh b) (Real.cosh a), abs_sub_comm (Real.cos b) (Real.cos a)]
      using this b₀ a₀ bMax aMax (le_of_not_ge ordered)
  have anti : AntitoneOn (fun x : ℝ => 4 * Real.cos x + Real.cosh x) (Set.Icc 0 (Real.log 2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x => 4 * -Real.sin x + Real.sinh x)
      (convex_Icc _ _) (by fun_prop)
    · intro x _
      exact (((Real.hasDerivAt_cos x).const_mul 4).add (Real.hasDerivAt_cosh x)).hasDerivWithinAt
    · intro x hx
      have h := interior_subset hx
      linarith [ratio_sinh_le_sin h.1 h.2]
  have h := anti ⟨a₀,aMax⟩ ⟨b₀,bMax⟩ ordered
  dsimp only at h
  have cosOrder := Real.cos_le_cos_of_nonneg_of_le_pi a₀
    (show b ≤ Real.pi by linarith [Real.two_le_pi, Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]) ordered
  have hypOrder : Real.cosh a ≤ Real.cosh b := Real.cosh_le_cosh.mpr
    (by rwa [abs_of_nonneg a₀, abs_of_nonneg b₀])
  rw [abs_of_nonpos (sub_nonpos.mpr hypOrder), abs_of_nonneg (sub_nonneg.mpr cosOrder)]
  linarith

private theorem factor_sum_cosh {p q : ℕ} (pp : 0 < p) (qp : 0 < q) :
    2*Real.sqrt (p*q : ℕ)*Real.cosh ((Real.log q-Real.log p)/2) = (p : ℝ)+q := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast pp
  have hq : 0 < (q:ℝ) := by exact_mod_cast qp
  let s := Real.sqrt (p*q : ℕ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast Nat.mul_pos pp qp)
  have sq : s^2 = (p:ℝ)*q := by dsimp [s]; rw [Real.sq_sqrt (by positivity), Nat.cast_mul]
  have phase : (Real.log q-Real.log p)/2 = Real.log ((q:ℝ)/s) := by
    rw [Real.log_div hq.ne' hs.ne']
    dsimp only [s]
    rw [Real.log_sqrt (by positivity), Nat.cast_mul, Real.log_mul hp.ne' hq.ne']
    ring
  rw [phase, Real.cosh_log (div_pos hq hs)]
  change 2*s*(((q:ℝ)/s + ((q:ℝ)/s)⁻¹)/2) = _
  field_simp
  nlinarith

/-- Recover the integer sum by rounding one normalized boundary sample at t=1.
The clipping keeps small errors at the nearly equal-factor endpoint harmless. -/
noncomputable def sumFromBoundaryOne (n : ℕ) (reading : ℝ) : ℤ :=
  let c := Real.cos (Real.log n / 2) - reading/2
  let clipped := max (Real.cos (Real.log 2)) (min 1 c)
  ⌊2 * Real.sqrt n * Real.cosh (Real.arccos clipped) + 1/2⌋

theorem sumFromBoundaryOne_correct {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p < q)
    (bal : q ≤ 2*p) [NeZero (p*q)] {reading : ℝ}
    (err : |reading-boundaryProbe (p*q) 1| < 1/(8*Real.sqrt (p*q : ℕ))) :
    sumFromBoundaryOne (p*q) reading = (p : ℤ)+q := by
  let s := Real.sqrt (p*q : ℕ)
  have spos : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast Nat.mul_pos hp.pos hq.pos)
  let d := (Real.log q-Real.log p)/2
  have pp : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have qp : 0 < (q:ℝ) := by exact_mod_cast hq.pos
  have d₀ : 0 ≤ d := by
    dsimp [d]
    linarith [Real.log_le_log pp (by exact_mod_cast ord.le : (p:ℝ)≤q)]
  have dMax : d ≤ Real.log 2 := by
    have h := Real.log_le_log qp (by exact_mod_cast bal : (q:ℝ) ≤ 2*p)
    rw [Real.log_mul (by norm_num) pp.ne'] at h
    dsimp [d]
    linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  have logrange : Real.log 2 ≤ Real.pi := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2), Real.two_le_pi]
  have wave := ratioWave_semiprime hp hq ord.ne (t := 1) (by norm_num)
  simp only [ratioWave, one_mul] at wave
  let c := Real.cos (Real.log (p*q : ℕ)/2) - reading/2
  let c' := max (Real.cos (Real.log 2)) (min 1 c)
  let d' := Real.arccos c'
  have cLo : Real.cos (Real.log 2) ≤ Real.cos d :=
    Real.cos_le_cos_of_nonneg_of_le_pi d₀ logrange dMax
  have c'lo : Real.cos (Real.log 2) ≤ c' := le_max_left _ _
  have c'hi : c' ≤ 1 := max_le (Real.cos_le_one _) (min_le_left _ _)
  have cos' : Real.cos d' = c' := Real.cos_arccos ((Real.neg_one_le_cos _).trans c'lo) c'hi
  have d'hi := Real.arccos_le_arccos c'lo
  rw [Real.arccos_cos (Real.log_pos (by norm_num : (1:ℝ) < 2)).le logrange] at d'hi
  have cond := ratio_cosh_condition (Real.arccos_nonneg c') d₀ d'hi dMax
  change |Real.cosh d' - Real.cosh d| ≤ 4*|Real.cos d' - Real.cos d| at cond
  rw [cos'] at cond
  have clip : |c'-Real.cos d| ≤ |c-Real.cos d| := by
    dsimp [c']
    rw [← max_sub_sub_right, ← min_sub_sub_right]
    exact abs_le.mpr ⟨le_max_of_le_right (le_min (by linarith [Real.cos_le_one d, abs_nonneg (c-Real.cos d)])
      (neg_abs_le _)), max_le (by linarith [abs_nonneg (c-Real.cos d)])
      ((min_le_right _ _).trans (le_abs_self _))⟩
  have e : |c-Real.cos d| = |reading-boundaryProbe (p*q) 1|/2 := by
    rw [show c-Real.cos d = -(reading-boundaryProbe (p*q) 1)/2 by dsimp [c,d]; linarith,
      abs_div, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  change |reading-boundaryProbe (p*q) 1| < 1/(8*s) at err
  have tiny := (lt_div_iff₀ (by positivity : 0<8*s)).mp err
  have exactSum : 2*s*Real.cosh d = (p:ℝ)+q := factor_sum_cosh hp.pos hq.pos
  have gap : |2*s*Real.cosh d' - ((p:ℝ)+q)| < 1/2 := by
    rw [← exactSum, ← mul_sub, abs_mul, abs_of_pos (by positivity : 0<2*s)]
    have h := cond.trans (mul_le_mul_of_nonneg_left clip (by norm_num : 0≤(4:ℝ)))
    rw [e] at h
    nlinarith [mul_le_mul_of_nonneg_left h spos.le]
  obtain ⟨low,high⟩ := abs_lt.mp gap
  apply Int.floor_eq_iff.mpr
  simp only [Int.cast_add, Int.cast_natCast]
  change (p:ℝ)+q ≤ 2*s*Real.cosh d'+1/2 ∧ 2*s*Real.cosh d'+1/2 < (p:ℝ)+q+1
  constructor <;> linarith

end PrimeFactors
