import PrimeFactors.CenteredBinomialDivisorWindow
import PrimeFactors.AnalyticDivisorWindow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! One conditional window from a supplied boundary reading at height one.
The finite Euler-product identity and the window bounds are unconditional.
The reading and its guaranteed error are explicit inputs to the selection. -/

namespace PrimeFactors.BinomialAnalyticWindow

open AnalyticDivisorWindow
open FeasibleDivisorCover (dimension divisorFloor)

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

/-- Absolute error sufficient when the observed lower half-log gap is at least 1/8. -/
noncomputable def epsilon : ℝ := (1/2:ℝ)^502

noncomputable def logWidth : ℝ := 25*epsilon/3

/-- The smaller common radius applicable to either factor. -/
def window : ℕ := 5359*FeasibleDivisorCover.radius false

/-- On the separated interval the slope of −cos is at least 3/25. -/
theorem separated_slope {a δ : ℝ} (visible : 1/8≤a) (lo : a≤δ) (hi : δ≤Real.pi/2) :
    (3/25)*(δ-a)≤Real.cos a-Real.cos δ := by
  rcases lo.lt_or_eq with h|rfl
  · obtain ⟨c,hc,deriv⟩ := exists_hasDerivAt_eq_slope Real.cos (fun x => -Real.sin x)
      h Real.continuous_cos.continuousOn (fun x _ => Real.hasDerivAt_cos x)
    have lower : 3/25≤Real.sin (1/8) := by
      have H := Real.sin_gt_sub_cube (by norm_num : (0:ℝ)<1/8) (by norm_num : (1/8:ℝ)≤1)
      norm_num at H ⊢
      linarith
    have sc := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos] : -(Real.pi/2)≤1/8)
      (hc.2.le.trans hi) (visible.trans hc.1.le)
    have bound := mul_le_mul_of_nonneg_right (lower.trans sc) (sub_nonneg.mpr h.le)
    have eq := (eq_div_iff (sub_ne_zero.mpr h.ne')).mp deriv
    linarith
  · simp

private theorem log_enclosure {p q : ℕ} [NeZero (p*q)] (hp : p.Prime) (hq : q.Prime)
    (ord : p<q) (bal : q≤2*p) (reading : ℝ)
    (visible : 1/8≤singleLeft (p*q) reading epsilon)
    (error : |reading-boundaryProbe (p*q) 1|≤epsilon) :
    let a := singleLeft (p*q) reading epsilon
    a≤Real.log q-Real.log (p*q:ℕ)/2 ∧ Real.log q-Real.log (p*q:ℕ)/2≤a+logWidth := by
  let δ := (Real.log q-Real.log p)/2
  let a := singleLeft (p*q) reading epsilon
  have pp : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have qp : 0<(q:ℝ) := by exact_mod_cast hq.pos
  have deq : Real.log q-Real.log (p*q:ℕ)/2 = δ := by
    rw [Nat.cast_mul,Real.log_mul pp.ne' qp.ne']; dsimp [δ]; ring
  have d0 : 0≤δ := by
    dsimp [δ]; linarith [Real.log_le_log pp (by exact_mod_cast ord.le : (p:ℝ)≤q)]
  have dmax : δ≤Real.pi/2 := by
    have h := Real.log_le_log qp (by exact_mod_cast bal : (q:ℝ)≤2*p)
    rw [Real.log_mul (by norm_num) pp.ne'] at h
    dsimp [δ]; linarith [Real.two_le_pi,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  let top := Real.cos (Real.log (p*q:ℕ)/2)-reading/2+epsilon/2
  have wave := ratioWave_semiprime hp hq ord.ne (t:=1) (by norm_num)
  simp only [ratioWave,one_mul] at wave
  change _=Real.cos δ at wave
  obtain ⟨neg,add⟩ := abs_le.mp error
  have up : Real.cos δ≤top := by dsimp [top]; linarith
  have clipped := le_min (Real.cos_le_one _) up
  have ac : Real.cos a=min 1 top := Real.cos_arccos
    ((Real.neg_one_le_cos _).trans clipped) (min_le_left _ _)
  have ad : a≤δ := by
    have close := Real.arccos_le_arccos clipped
    rwa [Real.arccos_cos d0 (by linarith [Real.pi_pos])] at close
  have err : Real.cos a-Real.cos δ≤epsilon := by
    rw [ac]; have limit := min_le_right 1 top; dsimp [top] at limit; linarith
  have measured := (separated_slope visible ad dmax).trans err
  change a≤_ ∧ _≤a+logWidth
  rw [deq]
  exact ⟨ad,by unfold logWidth; linarith⟩

/-- A one-unit outward approximation to the physical lower endpoint still fits. -/
theorem physical_budget : (2:ℝ)^1024*logWidth+1 ≤ 4*(window:ℝ) := by
  norm_num [epsilon,logWidth,window,FeasibleDivisorCover.radius,FeasibleDivisorCover.S]

/-- Lower log endpoint for the requested factor. The boolean selects the larger factor when true. -/
noncomputable def logLeft (n : ℕ) (reading : ℝ) (larger : Bool) : ℝ :=
  let a := singleLeft n reading epsilon
  if larger then a else -a-logWidth

/-- The same polynomial covers the requested factor for every compatible pair.
X may be a rational approximation, rounded down by at most one physical unit. -/
theorem selected_window {n : ℕ} [NeZero n] (big : 2^2047≤n) (parity : Odd n)
    (reading : ℝ) (larger : Bool) (visible : 1/8≤singleLeft n reading epsilon)
    (accurate : |reading-boundaryProbe n 1|≤epsilon) (X : ℝ) (xp : 0≤X)
    (outward : X≤lowerValue n (logLeft n reading larger))
    (approx : lowerValue n (logLeft n reading larger)-X≤1) :
    let C := AnalyticDivisorWindow.center X window
    ∃ F : Polynomial ℤ, F≠0 ∧ F.roots.toFinset.card≤dimension-1 ∧
      ∀ p q : ℕ, p*q=n → p.Prime → q.Prime → p<q → q≤2*p → q<2^1024 →
      let d := if larger then q else p
      ∃ x : ℤ, (d:ℤ)=(C:ℤ)+2*x ∧ |x|≤(window:ℤ) ∧ F.eval x=0 := by
  let C := AnalyticDivisorWindow.center X window
  obtain ⟨F,nz,rank,hit⟩ := CenteredBinomialDivisorWindow.at_center big parity false C (center_odd ..)
  refine ⟨F,nz,rank,?_⟩
  intro p q pair hp hq ord bal cap
  subst n
  obtain ⟨lo,hi⟩ := log_enclosure hp hq ord bal reading visible accurate
  let d := if larger then q else p
  let e := if larger then p else q
  have data : d.Prime ∧ d*e=p*q ∧ e<2^1024 ∧ d<2^1024 := by
    cases larger with
    | false => exact ⟨hp,rfl,cap,ord.trans cap⟩
    | true => exact ⟨hq,Nat.mul_comm _ _,ord.trans cap,cap⟩
  obtain ⟨prime,product,ecap,dcap⟩ := data
  have lower : divisorFloor (p*q) false≤d := by
    change (p*q)/2^1024+1≤d
    apply Nat.succ_le_of_lt
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0<2^1024)).mpr
    rw [← product]
    exact Nat.mul_lt_mul_of_pos_left ecap prime.pos
  have dsize : dimension-1<d := by
    have le : 2^1023≤(p*q)/2^1024 := (Nat.le_div_iff_mul_le (by positivity)).mpr (by
      rw [←pow_add]; exact big)
    change (p*q)/2^1024+1 ≤ d at lower
    have h : dimension-1<2^1023 := by decide +kernel
    omega
  have other : Real.log p-Real.log (p*q:ℕ)/2= -(Real.log q-Real.log (p*q:ℕ)/2) := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
    ring
  have endpoints : logLeft (p*q) reading larger≤Real.log d-Real.log (p*q:ℕ)/2 ∧
      Real.log d-Real.log (p*q:ℕ)/2≤logLeft (p*q) reading larger+logWidth := by
    cases larger with
    | false => simp only [logLeft,Bool.false_eq_true,if_false,d,other]; constructor <;> linarith
    | true => exact ⟨lo,hi⟩
  have odd : Odd d := by
    have : Odd (d*e) := product ▸ parity
    exact (Nat.odd_mul.mp this).1
  obtain ⟨x,pos,near⟩ := rounded_center odd (by exact_mod_cast prime.pos)
    (by exact_mod_cast dcap.le : (d:ℝ)≤(2:ℝ)^1024) endpoints.1 endpoints.2 xp outward approx physical_budget
  exact ⟨x,pos,near,hit x d prime dsize ⟨e,product.symm⟩ pos lower near⟩

/-- An exact choice of the rounded endpoint, depending only on the public inputs. -/
noncomputable def endpoint (n : ℕ) (reading : ℝ) (larger : Bool) : ℕ :=
  ⌊lowerValue n (logLeft n reading larger)⌋₊

/-- A single supplied reading selects one window for either factor chosen in advance.
The computation of that reading from n is a separate problem. -/
theorem from_reading {n : ℕ} [NeZero n] (big : 2^2047≤n) (parity : Odd n)
    (reading : ℝ) (larger : Bool) (visible : 1/8≤singleLeft n reading epsilon)
    (accurate : |reading-boundaryProbe n 1|≤epsilon) :
    let C := AnalyticDivisorWindow.center (endpoint n reading larger) window
    ∃ F : Polynomial ℤ, F≠0 ∧ F.roots.toFinset.card≤dimension-1 ∧
      ∀ p q : ℕ, p*q=n → p.Prime → q.Prime → p<q → q≤2*p → q<2^1024 →
      let d := if larger then q else p
      ∃ x : ℤ, (d:ℤ)=(C:ℤ)+2*x ∧ |x|≤(window:ℤ) ∧ F.eval x=0 := by
  exact selected_window big parity reading larger visible accurate (endpoint n reading larger)
    (Nat.cast_nonneg _) (Nat.floor_le (Real.exp_pos _).le)
    (by unfold endpoint; linarith [Nat.lt_floor_add_one (lowerValue n (logLeft n reading larger))])

end PrimeFactors.BinomialAnalyticWindow
