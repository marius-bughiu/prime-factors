import PrimeFactors.AnalyticAccess
import PrimeFactors.CoupledDivisorWindow

namespace PrimeFactors.AnalyticDivisorWindow

/-- A lower endpoint for the factor, from a lower endpoint for its translated log. -/
noncomputable def lowerValue (n : ℕ) (a : ℝ) : ℝ := Real.exp (Real.log n / 2 + a)

/-- Center a window of 2W+1 odd positions at an explicitly chosen odd integer. -/
noncomputable def center (X : ℝ) (W : ℕ) : ℕ := 2*⌊X/2⌋₊+1+2*W

theorem center_odd (X : ℝ) (W : ℕ) : Odd (center X W) := by
  exact ⟨⌊X/2⌋₊+W, by unfold center; omega⟩

/-- The lower bound can be rounded outwards to any convenient rational X. -/
theorem center_contains {q W : ℕ} {X : ℝ} (odd : Odd q) (pos : 0≤X)
    (lo : X≤q) (diam : (q:ℝ)-X≤4*W) :
    ∃ x : ℤ, (q:ℤ)=(center X W:ℤ)+2*x ∧ |x|≤(W:ℤ) := by
  let b := ⌊X/2⌋₊
  have f0 : (b:ℝ) ≤ X/2 := Nat.floor_le (by positivity)
  have f1 : X/2 < (b:ℝ)+1 := Nat.lt_floor_add_one _
  have low : 2*b≤q := by exact_mod_cast (show 2*(b:ℝ)≤q by linarith)
  have high : q<2*b+2+4*W := by
    exact_mod_cast (show (q:ℝ)<2*(b:ℝ)+2+4*(W:ℝ) by linarith)
  obtain ⟨k,hk⟩ := odd
  refine ⟨(k:ℤ)-b-W, ?_, abs_le.mpr (by omega)⟩
  change (q:ℤ) = ((2*b+1+2*W:ℕ):ℤ)+2*((k:ℤ)-b-W)
  omega

/-- On an interval of log-width b ending at or below log M, exp changes by at most
M b. There is no division by the separation of the factors. -/
theorem lowerValue_bounds {n q : ℕ} {a b M : ℝ} (pos : 0 < (q:ℝ)) (cap : (q:ℝ)≤M)
    (lo : a ≤ Real.log q-Real.log n/2) (hi : Real.log q-Real.log n/2≤a+b) :
    lowerValue n a≤q ∧ (q:ℝ)-lowerValue n a≤M*b := by
  let z := Real.log n/2+a-Real.log q
  have zn : z≤0 := by dsimp [z]; linarith
  have zlo : -b≤z := by dsimp [z]; linarith
  have bp : 0≤b := by linarith
  have prod : lowerValue n a = q*Real.exp z := by
    rw [lowerValue, show Real.log n/2+a = Real.log q+z by dsimp [z]; ring,
      Real.exp_add, Real.exp_log pos]
  rw [prod]
  have small := Real.exp_le_one_iff.mpr zn
  have large := Real.add_one_le_exp z
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left small pos.le], by
    nlinarith [mul_le_mul_of_nonneg_left (show 1-b ≤ Real.exp z by linarith) pos.le,
      mul_le_mul_of_nonneg_right cap bp]⟩

/-- The existing bounded-error adaptive readings can stop as soon as one
prescribed-center window suffices. -/
theorem adaptive_center {p q W : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (bal : q≤2*p) (odd : Odd q) [NeZero (p*q)] (readProbe : ℝ → ℝ)
    (accuracy : ∀ t, 0<t → |readProbe t-boundaryProbe (p*q) t|≤1/5)
    (k : ℕ) (M : ℝ) (cap : (q:ℝ)≤M) (width : M*ratioWidth k≤4*W) :
    let wave := fun t => Real.cos (t*Real.log (p*q:ℕ)/2)-readProbe t/2
    let X := lowerValue (p*q) (ratioLeft wave k)
    ∃ x : ℤ, (q:ℤ)=(center X W:ℤ)+2*x ∧ |x|≤(W:ℤ) := by
  obtain ⟨lo,hi⟩ := factor_log_in_ratio_interval hp hq ord bal readProbe accuracy k
  obtain ⟨lb,gap⟩ := lowerValue_bounds (by exact_mod_cast hq.pos) cap lo hi
  exact center_contains odd (Real.exp_pos _).le lb (gap.trans width)

/-- Public lower bound on the half-log ratio from the one reading B(1) ± ε. -/
noncomputable def singleLeft (n : ℕ) (reading ε : ℝ) : ℝ :=
  Real.arccos (min 1 (Real.cos (Real.log n/2)-reading/2+ε/2))

private theorem chord {x : ℝ} (lo : 0≤x) (hi : x≤Real.pi/2) : x/2 ≤ Real.sin x := by
  have h := Real.mul_le_sin lo hi
  have half : (1/2:ℝ) ≤ 2/Real.pi := (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_le_four])
  linarith [mul_le_mul_of_nonneg_right half lo]

/-- The cosine cannot distinguish frequencies linearly near zero. Away from
zero the same inequality gives an error bound linear in the reading error. -/
theorem gap_condition {a δ ε : ℝ} (a0 : 0≤a) (lo : a≤δ) (hi : δ≤Real.pi/2)
    (error : Real.cos a-Real.cos δ≤ε) : (δ-a)*(δ+a)≤8*ε := by
  have c := chord (x := (δ+a)/2) (by linarith) (by linarith)
  have d := chord (x := (δ-a)/2) (by linarith) (by linarith)
  have product := mul_le_mul c d (by linarith : 0≤(δ-a)/2/2)
    (by linarith : 0 ≤ Real.sin ((δ+a)/2))
  rw [Real.cos_sub_cos, show (a-δ)/2 = -((δ-a)/2) by ring, Real.sin_neg,
    show (a+δ)/2 = (δ+a)/2 by ring] at error
  nlinarith

/-- The observed lower endpoint also measures the conditioning of the one-reading
test. The formula remains valid when that endpoint is exactly zero. -/
theorem single_encloses {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (bal : q≤2*p) [NeZero (p*q)] {reading ε b : ℝ}
    (error : |reading-boundaryProbe (p*q) 1|≤ε) (bp : 0≤b)
    (room : 8*ε ≤ b*(b+2*singleLeft (p*q) reading ε)) :
    let a := singleLeft (p*q) reading ε
    a≤Real.log q-Real.log (p*q:ℕ)/2 ∧ Real.log q-Real.log (p*q:ℕ)/2≤a+b := by
  let δ := (Real.log q-Real.log p)/2
  have pp : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have qp : 0<(q:ℝ) := by exact_mod_cast hq.pos
  have deq : Real.log q-Real.log (p*q:ℕ)/2 = δ := by
    rw [Nat.cast_mul, Real.log_mul pp.ne' qp.ne']; dsimp [δ]; ring
  have d0 : 0≤δ := by
    dsimp [δ]; linarith [Real.log_le_log pp (by exact_mod_cast ord.le : (p:ℝ) ≤ q)]
  have dmax : δ≤Real.pi/2 := by
    have h := Real.log_le_log qp (by exact_mod_cast bal : (q:ℝ)≤2*p)
    rw [Real.log_mul (by norm_num) pp.ne'] at h
    dsimp [δ]; linarith [Real.two_le_pi, Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  let u := Real.cos (Real.log (p*q:ℕ)/2)-reading/2+ε/2
  let a := singleLeft (p*q) reading ε
  have wave := ratioWave_semiprime hp hq ord.ne (t:=1) (by norm_num)
  simp only [ratioWave,one_mul] at wave
  change _ = Real.cos δ at wave
  obtain ⟨neg, plus⟩ := abs_le.mp error
  have ub : Real.cos δ ≤ u := by dsimp [u]; linarith
  have cl : Real.cos δ ≤ min 1 u := le_min (Real.cos_le_one _) ub
  have ac : Real.cos a = min 1 u := Real.cos_arccos ((Real.neg_one_le_cos _).trans cl) (min_le_left _ _)
  have a0 : 0≤a := Real.arccos_nonneg _
  have ad : a≤δ := by
    have h := Real.arccos_le_arccos cl
    rwa [Real.arccos_cos d0 (by linarith [Real.pi_pos])] at h
  have err : Real.cos a-Real.cos δ ≤ ε := by
    rw [ac]; have mm := min_le_right 1 u; dsimp [u] at mm ⊢; linarith
  have condition := gap_condition a0 ad dmax err
  change 8*ε≤b*(b+2*a) at room
  rw [deq]
  refine ⟨ad,?_⟩
  change δ ≤ a+b
  by_contra! h
  have pos : 0 < (δ-a-b)*(δ+a+b) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- One low-height sample can choose the odd center directly when the displayed
error budget holds. Both numerical tests use only the input, reading and bit bound. -/
theorem single_center {p q W : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (bal : q≤2*p) (odd : Odd q) [NeZero (p*q)] {reading ε b M : ℝ}
    (accurate : |reading-boundaryProbe (p*q) 1|≤ε) (bp : 0≤b)
    (room : 8*ε ≤ b*(b+2*singleLeft (p*q) reading ε))
    (cap : (q:ℝ)≤M) (width : M*b≤4*W) :
    let X := lowerValue (p*q) (singleLeft (p*q) reading ε)
    ∃ x : ℤ, (q:ℤ)=(center X W:ℤ)+2*x ∧ |x|≤(W:ℤ) := by
  obtain ⟨lo,hi⟩ := single_encloses hp hq ord bal accurate bp room
  obtain ⟨lb,gap⟩ := lowerValue_bounds (by exact_mod_cast hq.pos) cap lo hi
  exact center_contains odd (Real.exp_pos _).le lb (gap.trans width)

/-- A lower rational approximation to the displayed exponential may lose up to
E physical units. Positive slack suffices without deciding an equality at a floor. -/
theorem rounded_center {n q W : ℕ} {a b M X E : ℝ} (odd : Odd q) (pos : 0 < (q:ℝ))
    (cap : (q:ℝ)≤M) (left : a≤Real.log q-Real.log n/2) (right : Real.log q-Real.log n/2≤a+b)
    (xp : 0≤X) (outward : X≤lowerValue n a) (approx : lowerValue n a-X≤E)
    (width : M*b+E≤4*W) :
    ∃ x : ℤ, (q:ℤ)=(center X W:ℤ)+2*x ∧ |x|≤(W:ℤ) := by
  obtain ⟨lb,dist⟩ := lowerValue_bounds pos cap left right
  exact center_contains odd xp (outward.trans lb) (by linarith)

/-- A bound on every height actually used, including the last iteration. -/
theorem query_height_budget (readWave : ℝ → ℝ) {j k : ℕ} (used : j<k) {T : ℝ} (tp : 0≤T)
    (budget : 4 < T*ratioWidth (k-1)) :
    ratioQueryHeight (ratioLeft readWave j) (ratioWidth j) < T := by
  have left (i : ℕ) : 0≤ratioLeft readWave i := by
    induction i with
    | zero => simp [ratioLeft]
    | succ i ih =>
      simp only [ratioLeft]
      split_ifs
      · exact ih
      · exact add_nonneg ih (by unfold ratioWidth; positivity)
  have positive : 0 < ratioWidth j := by unfold ratioWidth; positivity
  have monotone : ratioWidth (k-1) ≤ ratioWidth j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  obtain ⟨_,_,peak⟩ := ratioQueryHeight_span (left j) positive
  exact lt_of_mul_lt_mul_right ((peak.trans Real.pi_le_four).trans_lt
    (budget.trans_le (mul_le_mul_of_nonneg_left monotone tp))) positive.le

/-- Exact adaptive sample counts and height budgets. Each case allows an extra
unit of outward rounding in the physical estimate of the factor. -/
theorem adaptive_budgets :
    ((2:ℝ)^1024*ratioWidth 1371+1≤4*2^453 ∧ 4<(2:ℝ)^571*ratioWidth 1370) ∧
    ((2:ℝ)^1024*ratioWidth 1234+1≤4*2^510 ∧ 4<(2:ℝ)^514*ratioWidth 1233) ∧
    ((2:ℝ)^1024*ratioWidth 1232+1≤4*2^511 ∧ 4<(2:ℝ)^513*ratioWidth 1231) := by
  unfold ratioWidth
  norm_num

/-- With a visible lower half-log gap of one eighth, these precisions pay the
one-reading error test for W=2^453, W=2^510 and W=2^511 respectively. -/
theorem single_budgets {a : ℝ} (visible : 1/8≤a) :
    8*(1/2:ℝ)^574 ≤ (1/2:ℝ)^569*((1/2:ℝ)^569+2*a) ∧
    8*(1/2:ℝ)^517 ≤ (1/2:ℝ)^512*((1/2:ℝ)^512+2*a) ∧
    8*(1/2:ℝ)^516 ≤ (1/2:ℝ)^511*((1/2:ℝ)^511+2*a) := by
  have scaled (k : ℕ) : 8*(1/2:ℝ)^(k+5) ≤ (1/2:ℝ)^k*((1/2:ℝ)^k+2*a) := by
    rw [pow_add]
    have pos : 0≤(1/2:ℝ)^k := by positivity
    calc _ = (1/2:ℝ)^k*(1/4) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) pos
  exact ⟨scaled 569, scaled 512, scaled 511⟩

/-- Near equality, two distinct positive frequencies u and 2u admit the same
one-height reading at quadratic error, though the associated real factors differ
linearly in u. This statement is about a continuous observation model. -/
theorem single_common_reading (C s : ℝ) {u : ℝ} (up : 0≤u) (sp : 0≤s) :
    (∃ y : ℝ, |y-(C-2*Real.cos u)|≤3*u^2/2 ∧ |y-(C-2*Real.cos (2*u))|≤3*u^2/2) ∧
      s*u≤s*Real.exp (2*u)-s*Real.exp u := by
  have sin1 := Real.abs_sin_le_abs (x:=(u+2*u)/2)
  have sin2 := Real.abs_sin_le_abs (x:=(u-2*u)/2)
  rw [abs_of_nonneg (by linarith : 0≤(u+2*u)/2)] at sin1
  rw [abs_of_nonpos (by linarith : (u-2*u)/2≤0)] at sin2
  have prod := mul_le_mul sin1 sin2 (abs_nonneg _) (by linarith)
  have close : |Real.cos u-Real.cos (2*u)| ≤ 3*u^2/2 := by
    rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    nlinarith
  constructor
  · refine ⟨C-Real.cos u-Real.cos (2*u), ?_, ?_⟩
    · convert close using 2
      ring
    · rw [abs_sub_comm] at close
      convert close using 2
      ring
  · have h := Real.add_one_le_exp u
    have e : 1≤Real.exp u := Real.one_le_exp_iff.mpr up
    have m := mul_le_mul_of_nonneg_right e (by linarith : 0≤Real.exp u-1)
    rw [two_mul, Real.exp_add]
    have diff : u≤Real.exp u*Real.exp u-Real.exp u := by nlinarith
    simpa only [mul_sub] using mul_le_mul_of_nonneg_left diff sp

/-- Choose the polynomial using only n, the supplied reading and its error.
The same polynomial works for every eligible ordered prime pair with that product. -/
theorem single_polynomial {n m r w h e : ℕ} [NeZero n] (large : 2^2047≤n)
    (parity : Odd n) (scale : CoupledDivisorWindow.LargerScale m r w h e)
    (reading ε b M : ℝ) (bp : 0≤b)
    (room : 8*ε≤b*(b+2*singleLeft n reading ε)) (width : M*b≤4*(2:ℝ)^w) :
    let C := center (lowerValue n (singleLeft n reading ε)) (2^w)
    ∃ F : Polynomial ℤ, F≠0 ∧ F.roots.toFinset.card<r ∧
      ∀ p q : ℕ, p*q=n → p.Prime → q.Prime → p<q → q≤2*p → (q:ℝ)≤M →
        |reading-boundaryProbe n 1|≤ε →
        ∃ x : ℤ, (q:ℤ)=(C:ℤ)+2*x ∧ |x|≤(2:ℤ)^w ∧ F.eval x=0 := by
  let C := center (lowerValue n (singleLeft n reading ε)) (2^w)
  obtain ⟨F,nz,count,works⟩ := CoupledDivisorWindow.at_larger_center large parity scale C (center_odd ..)
  refine ⟨F,nz,count,?_⟩
  intro p q pair hp hq ord bal cap error
  subst n
  have wcast : ((2^w : ℕ):ℝ) = (2:ℝ)^w := by simp only [Nat.cast_pow,Nat.cast_ofNat]
  obtain ⟨x,pos,near⟩ := single_center (W:=2^w) hp hq ord bal (Nat.odd_mul.mp parity).2 error
    bp room cap (by rw [wcast]; exact width)
  have near' : |x|≤(2:ℤ)^w := by simpa only [Nat.cast_pow,Nat.cast_ofNat] using near
  have low := CoupledDivisorWindow.larger_le_factor (Nat.mul_pos hp.pos hq.pos)
    (Nat.mul_comm p q) ord.le
  exact ⟨x,pos,near',works x q (by simpa only [Nat.cast_mul] using dvd_mul_left (q:ℤ) (p:ℤ)) pos (Int.ofNat_le.mpr low) near'⟩

end PrimeFactors.AnalyticDivisorWindow
