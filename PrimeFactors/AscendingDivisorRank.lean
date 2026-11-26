import PrimeFactors.QuantileThetaBounds
import PrimeFactors.ShortPascalRow
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! Population-average one-based rank of the smaller prime under an ascending
scan through the feasible odd integers. The final transfer takes the explicit
prime-count discrepancy and integrated masses as premises. -/

namespace PrimeFactors.AscendingDivisorRank

open Real MeasureTheory intervalIntegral

/-- Logarithmic width for the smaller factor at normalized product x=N/B². -/
noncomputable def logWidth (x : ℝ) : ℝ := (log 4 - log x)/2

/-- Conditional mean of the continuous ordinal at a fixed product under
uniform area in the two prime coordinates. -/
noncomputable def fiberMean (a : ℝ) := 1/a-1/(exp a-1)

/-- In the log coordinate v=log(p/(N/(2B))), the real normalized
ascending rank is (exp v-1)/(exp a-1). Its uniform mean has a closed form. -/
theorem fiber_integral {a : ℝ} (pos : 0<a) :
    (∫ v in (0:ℝ)..a, (exp v-1)/(exp a-1))/a = fiberMean a := by
  have ep : 0<exp a-1 := by linarith only [Real.one_lt_exp_iff.mpr pos]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_sub
    (Real.continuous_exp.intervalIntegrable 0 a) (continuous_const.intervalIntegrable 0 a),
    integral_exp,intervalIntegral.integral_const]
  simp only [Real.exp_zero, sub_zero,smul_eq_mul,mul_one]
  unfold fiberMean
  field_simp [pos.ne',ep.ne']
  first | ring1 | left; ring

/-- At fixed product the excess of one half over the mean ordinal is at
least one thirteenth of the logarithmic width. -/
theorem fiber_mean_bound {a : ℝ} (pos : 0<a) (short : a≤1/2) :
    fiberMean a ≤ 1/2-a/13 := by
  have tay := Real.exp_bound' pos.le (show a≤1 by linarith) (n:=4) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at tay
  have m : 0≤1-a/2+a^2/13 := by nlinarith [sq_nonneg a]
  have cmp := mul_le_mul_of_nonneg_left tay m
  have p3 : 0≤a^3 := by positivity
  have p5 : 0≤a^5 := by positivity
  have p4 := mul_le_mul_of_nonneg_left short p3
  have p6 := mul_le_mul_of_nonneg_left short p5
  have core : (1-a/2+a^2/13)*(exp a-1) ≤ a := by
    nlinarith only [cmp,p4,p6,p3,p5]
  have ep : 0<exp a-1 := by linarith only [Real.one_lt_exp_iff.mpr pos]
  unfold fiberMean
  calc
    _ = (exp a - 1-a)/(a*(exp a-1)) := by field_simp [pos.ne',ep.ne']
    _ ≤ _ := (div_le_iff₀ (mul_pos pos ep)).mpr (by nlinarith only [core])

private theorem dWidth {x : ℝ} (pos : 0<x) :
    HasDerivAt logWidth (-(1/x)/2) x := by
  simpa [logWidth] using
    (((hasDerivAt_const x (log 4)).sub (Real.hasDerivAt_log pos.ne')).div_const 2)

private theorem endpoints : logWidth 4=0 ∧ logWidth 2=log 2/2 := by
  constructor
  · simp [logWidth]
  · rw [logWidth,show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    ring

/-- Uniform area of the eligible factor pairs and its first log-width moment,
in units of B². The Jacobian of (p,q) ↦ (pq,log(sqrt(pq)/p)) has magnitude 1. -/
theorem width_moments :
    (∫ x in (2:ℝ)..4, logWidth x) = 1-log 2 ∧
    (∫ x in (2:ℝ)..4, (logWidth x)^2) = 1-log 2-(log 2)^2/2 := by
  have D {x : ℝ} (hx : x∈Set.uIcc (2:ℝ) 4) : 0<x := by
    rw [Set.uIcc_of_le (by norm_num)] at hx
    linarith only [hx.1]
  have cont : ContinuousOn logWidth (Set.uIcc (2:ℝ) 4) :=
    fun x hx => (dWidth (D hx)).continuousAt.continuousWithinAt
  constructor
  · have integ := integral_eq_sub_of_hasDerivAt
      (f:=fun x : ℝ => x*(logWidth x+1/2)) (f':=logWidth)
      (a:=(2:ℝ)) (b:=4) (fun x hx => ?_) cont.intervalIntegrable
    · rw [integ]
      dsimp only
      rw [endpoints.1,endpoints.2]
      ring
    · convert (hasDerivAt_id x).mul ((dWidth (D hx)).add_const (1/2)) using 1
      dsimp
      field_simp [(D hx).ne']
      ring
  · have integ := integral_eq_sub_of_hasDerivAt
      (f:=fun x : ℝ => x*((logWidth x)^2+logWidth x+1/2))
      (f':=fun x : ℝ => (logWidth x)^2) (a:=(2:ℝ)) (b:=4)
      (fun x hx => ?_) (cont.pow 2).intervalIntegrable
    · rw [integ]
      dsimp only
      rw [endpoints.1,endpoints.2]
      ring
    · have h := dWidth (D hx)
      convert (hasDerivAt_id x).mul (((h.pow 2).add h).add_const (1/2)) using 1
      dsimp
      field_simp [(D hx).ne']
      ring

/-- The full eligible area and its log-width moment have ratio above .217. -/
theorem mean_log_width :
    (217/1000:ℝ)*(1-log 2) < 1-log 2-(log 2)^2/2 := by
  have h := Real.log_two_lt_d9.le
  have lo := Real.log_two_gt_d9.le
  nlinarith only [h,lo,mul_nonneg (sub_nonneg.mpr h) (by linarith only [lo] :
    0≤693147181/1000000000+log 2)]

/-- For normalized factors x=p/B, y=q/B, the superlevel set is decreasing
in y and increasing in x. This gives interval sections in either variable. -/
def superlevel (t x y : ℝ) : Prop := (1-t)*y/2+t*sqrt (y/x) ≤ 1

theorem superlevel_iff {x y t : ℝ} (xp : 0<x)
    (den : 0<sqrt (x*y)-x*y/2) :
    t ≤ (x-x*y/2)/(sqrt (x*y)-x*y/2) ↔ superlevel t x y := by
  have root : x*sqrt (y/x) = sqrt (x*y) := calc
    _ = sqrt (x^2)*sqrt (y/x) := by rw [Real.sqrt_sq xp.le]
    _ = sqrt (x^2*(y/x)) := (Real.sqrt_mul (sq_nonneg x) _).symm
    _ = _ := by congr 1; field_simp; ring
  rw [le_div_iff₀ den, ←root, superlevel]
  constructor
  · intro h
    by_contra! bad
    nlinarith only [mul_lt_mul_of_pos_left bad xp,h]
  · intro h
    nlinarith only [mul_le_mul_of_nonneg_left h xp.le]

theorem superlevel_mono {x x' y y' t : ℝ} (xp : 0<x) (xx : x≤x')
    (yp : 0≤y') (yy : y'≤y) (lo : 0≤t) (hi : t≤1) (h : superlevel t x y) :
    superlevel t x' y' := by
  have q : y'/x' ≤ y/x := div_le_div₀ (yp.trans yy) yy xp xx
  exact (add_le_add (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left yy (sub_nonneg.mpr hi)) (by norm_num))
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt q) lo)).trans h

/-- Number of odd integers in [L,U] when L≤U. Substituting p for U gives the
one-based rank of an odd divisor p in the ascending scan. -/
def oddCount (L U : ℕ) : ℕ := (U+1)/2 - L/2

/-- Clipping the continuous lower endpoint to the actual partner limit and
rounding up moves it by strictly less than two units. -/
theorem lower_endpoints {n B : ℕ} (bpos : 0<B) (full : 2*B^2≤n) (cap : n≤(2*B-1)^2) :
    (n:ℝ)/(2*B) ≤ ShortPascalRow.lower n B ∧
    (ShortPascalRow.lower n B:ℝ) < (n:ℝ)/(2*B)+2 := by
  let d := 2*B-1
  let k := (n-1)/d
  have dp : 0<d := by dsimp [d]; omega
  have ds : d+1=2*B := by dsimp [d]; omega
  have small : k≤d := by
    have : n-1 < (d+1)*d := by change n ≤ d^2 at cap; nlinarith only [cap,Nat.sub_le n 1,dp]
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul dp).mpr this)
  have b : k*d≤n-1 := Nat.div_mul_le_self _ _
  have c := Nat.lt_mul_div_succ (n-1) dp
  change n-1 < d*(k+1) at c
  have lo : n ≤ (2*B)*ShortPascalRow.lower n B := by
    have plus : k+1 ≤ ShortPascalRow.lower n B := le_max_right ..
    have step := Nat.mul_le_mul (show d≤2*B by omega) plus
    omega
  have hi : ShortPascalRow.lower n B*(2*B)<n+2*(2*B) := by
    change max B (k+1)*(2*B) < _
    rcases le_total B (k+1) with left|right
    · rw [max_eq_right left]
      have eq : (k+1)*(2*B)=k*d+k+2*B := by rw [←ds]; ring
      omega
    · rw [max_eq_left right]
      nlinarith only [full,bpos]
  have lr : (n:ℝ) ≤ 2*(B:ℝ)*(ShortPascalRow.lower n B:ℝ) := by exact_mod_cast lo
  have hr : (ShortPascalRow.lower n B:ℝ)*(2*B) < (n:ℝ)+2*(2*B) := by exact_mod_cast hi
  have pr : (0:ℝ)<2*(B:ℝ) := by positivity
  constructor
  · exact (div_le_iff₀ pr).mpr (by linarith only [lr])
  · apply (sub_lt_iff_lt_add).mp
    apply (lt_div_iff₀ pr).mpr
    linarith only [hr]

theorem odd_enclosure {L U p : ℕ} {l s : ℝ} (lp : L≤p)
    (bottom : l≤L) (ceiling : (L:ℝ)<l+2) (top : s<(U:ℝ)+1) :
    2*(oddCount L p:ℝ) ≤ p-l+2 ∧ s-l-3 ≤ 2*(oddCount L U:ℝ) := by
  have i : 2*oddCount L p + L ≤ p+2 := by unfold oddCount; omega
  have w : U ≤ 2*oddCount L U + L := by unfold oddCount; omega
  have ir : 2*(oddCount L p:ℝ)+L ≤ (p:ℝ)+2 := by exact_mod_cast i
  have wr : (U:ℝ) ≤ 2*(oddCount L U:ℝ)+L := by exact_mod_cast w
  constructor <;> linarith

/-- A very short real interval forces both sorted primes into the top
3D positions of their bit-width band. No primality estimate enters here. -/
theorem top_band {p s l B D : ℝ} (bp : 0<B) (bs : B≤s) (su : s≤2*B)
    (lower : l=s^2/(2*B)) (divisor : l≤p) (width : D=s-l) : 2*B - p ≤ 3*D := by
  have gap := mul_nonneg (sub_nonneg.mpr bs) (sub_nonneg.mpr su)
  have prod : l*(2*B)=s^2 := (eq_div_iff (by positivity)).mp lower
  have core : B*(2*B-p) ≤ B*(3*D) := by
    nlinarith only [gap,prod,mul_le_mul_of_nonneg_left divisor bp.le,
      congrArg (B*·) width]
  exact (mul_le_mul_left bp).mp core

/-- Rounding the real bounds to odd test positions loses at most 5/(D−3),
where D is the continuous width and R its unrounded relative ordinal. -/
theorem rounding {k w D R : ℝ} (wp : 0<w) (wide : 3<D) (r0 : 0≤R) (r1 : R≤1)
    (tests : 2*k≤D*R+2) (slots : D-3≤2*w) : k/w ≤ R+5/(D-3) := by
  apply (div_le_iff₀ wp).mpr
  have gap : 0<D-3 := by linarith
  have add : 0≤R+5/(D-3) := by positivity
  have compare := mul_le_mul_of_nonneg_left slots add
  have cancel : 5/(D-3)*(D-3)=5 := div_mul_cancel₀ _ gap.ne'
  nlinarith only [compare,cancel,tests,r1]

/-- Population transfer normalized by B². P and T are respectively the
actual pair count and continuous-ordinal total in units of B². W is the
corresponding total of individually normalized, rounded integer ranks.
The two counting discrepancies and the rounding excess are supplied. -/
theorem ascending_mean {P T W : ℝ}
    (mass : (1-log 2)/710^2 - 12/10^16 ≤ P)
    (weighted : T ≤ ((1-log 2)/2 - (1-log 2-(log 2)^2/2)/13)/709^2 + 12/10^16)
    (round : W ≤ T + (6/10^6)*P) : W/P < 485/1000 := by
  have l := Real.log_two_lt_d9.le
  have w := mean_log_width
  have pos : 0<P := by linarith only [l,mass]
  apply (div_lt_iff₀ pos).mpr
  linarith only [mass,weighted,round,w,l]

/-- Aggregate integer rounding across the whole finite sample. The exceptional
set may contain arbitrary inputs, charged at a full interval each. Counts
and smooth rank masses are expressed in units of a common positive scale. -/
theorem finite_mean {α : Type*} [DecidableEq α] (S bad : Finset α) (rank actual : α → ℝ)
    {scale : ℝ} (sp : 0<scale) (rare : 10^6*bad.card ≤ S.card)
    (positive : ∀ i∈S, 0≤rank i) (fraction : ∀ i∈S, actual i≤1)
    (close : ∀ i∈S, i∉bad → actual i≤rank i+5/10^6)
    (mass : (1-log 2)/710^2-12/10^16 ≤ (S.card:ℝ)/scale)
    (weighted : (S.sum rank)/scale ≤
      ((1-log 2)/2-(1-log 2-(log 2)^2/2)/13)/709^2+12/10^16) :
    S.sum actual / S.card < 485/1000 := by
  have point : ∀ i∈S, actual i ≤ (rank i+5/10^6)+(if i∈bad then 1 else 0) := by
    intro i hi
    by_cases h : i∈bad
    · rw [if_pos h]
      linarith only [positive i hi,fraction i hi]
    · rw [if_neg h,add_zero]
      exact close i hi h
  have hsum := Finset.sum_le_sum point
  have boole : (∑ i∈S, if i∈bad then (1:ℝ) else 0)=
      ((S.filter (·∈bad)).card:ℝ) := by simp [Finset.sum_ite,Finset.filter_mem_eq_inter]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,boole,Finset.sum_const,nsmul_eq_mul] at hsum
  have sub : S.filter (·∈bad) ⊆ bad := fun _ h => (Finset.mem_filter.mp h).2
  have limit : (10:ℝ)^6*((S.filter (·∈bad)).card:ℝ) ≤ (S.card:ℝ) := by
    exact_mod_cast (Nat.mul_le_mul_left (10^6) (Finset.card_le_card sub)).trans rare
  have total : S.sum actual ≤ S.sum rank + 6/10^6*(S.card:ℝ) := by linarith only [hsum,limit]
  have normalized := div_le_div_of_nonneg_right total sp.le
  rw [add_div,mul_div_assoc] at normalized
  simpa only [div_div_div_cancel_right₀ sp.ne'] using ascending_mean mass weighted normalized

/-- The top-corner bound is negligible at the certified target population. -/
theorem exception_budget : 10^6*(3000010:ℕ)^2 < 2^2021 := by decide +kernel

theorem section_error {B ε : ℝ} (bp : 0<B) (ep : 0≤ε) (tight : ε≤4/10^13*B) :
    ε*(2*B/709+ε) < 12/10^16*B^2 := by
  have step := mul_le_mul tight (show 2*B/709+ε≤2*B/709+4/10^13*B by linarith)
    (show 0≤2*B/709+ε by positivity) (show 0≤4/10^13*B by positivity)
  nlinarith only [step,sq_pos_of_pos bp]

/-- A uniform search has mean normalized rank (W+1)/(2W). In reverse
order a hit at rank k moves to W+1−k. -/
theorem reverse_order {k w : ℝ} (pos : 0<w) :
    1-k/w ≤ (w+1-k)/w ∧ (1/2:ℝ) ≤ (w+1)/(2*w) := by
  constructor
  · apply (le_div_iff₀ pos).mpr
    have cancel := div_mul_cancel₀ k pos.ne'
    linarith only [cancel]
  · apply (le_div_iff₀ (by positivity)).mpr
    linarith

/-- The preimage length of an interval of normalized ranks at fixed product,
measured in the logarithmic factor coordinate v. -/
noncomputable def bandLength (a l h : ℝ) : ℝ :=
  log (1+h*(exp a-1)) - log (1+l*(exp a-1))

theorem band_membership {a l h v : ℝ} (ap : 0<a) (lp : 0≤l) (lh : l≤h) :
    (l≤(exp v-1)/(exp a-1) ∧ (exp v-1)/(exp a-1)≤h) ↔
    (log (1+l*(exp a-1))≤v ∧ v≤log (1+h*(exp a-1))) := by
  have e : 0<exp a-1 := by linarith only [Real.one_lt_exp_iff.mpr ap]
  have hp := lp.trans lh
  rw [le_div_iff₀ e,div_le_iff₀ e,Real.log_le_iff_le_exp (by positivity),
    Real.le_log_iff_exp_le (by positivity)]
  constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith

private theorem band_lower {a l h : ℝ} (ap : 0≤a) (lp : 0≤l) (lh : l≤h) :
    (h-l)*(exp a-1)/(1+h*(exp a-1)) ≤ bandLength a l h := by
  have e : 0≤exp a-1 := by linarith only [Real.one_le_exp_iff.mpr ap]
  have hp := lp.trans lh
  have dl : 0<1+l*(exp a-1) := by positivity
  have dh : 0<1+h*(exp a-1) := by positivity
  have bound := Real.one_sub_inv_le_log_of_pos (div_pos dh dl)
  rw [Real.log_div dh.ne' dl.ne'] at bound
  calc
    _ = 1-((1+h*(exp a-1))/(1+l*(exp a-1)))⁻¹ := by
      rw [inv_div]
      field_simp
      ring
    _ ≤ _ := bound

private theorem band_density {a : ℝ} (lo : 0≤a) (hi : a≤35/100) :
    a ≤ (exp a-1)*(1-23/50*a) := by
  have tay := Real.sum_le_exp_of_nonneg lo 4
  norm_num [Finset.sum_range_succ,Nat.factorial] at tay
  have c : 0≤1-23/50*a := by linarith only [hi]
  have prod := mul_le_mul_of_nonneg_right tay c
  have s2 := mul_le_mul_of_nonneg_left hi (sq_nonneg a)
  have s3 := mul_le_mul_of_nonneg_left hi (pow_nonneg lo 3)
  nlinarith only [prod,s2,s3,sq_nonneg a]

/-- Per-product log-area lower bounds simultaneously for both fixed bands.
Here a≤log(2)/2<0.35 throughout the full-width eligible region. -/
theorem two_bands {a : ℝ} (lo : 0≤a) (hi : a≤35/100) :
    a/10 ≤ bandLength a (1/100) (11/100) ∧
    (40/1021)*a ≤ bandLength a (48/100) (52/100) := by
  have e : 0≤exp a-1 := by linarith only [Real.one_le_exp_iff.mpr lo]
  have den := band_density lo hi
  constructor
  · apply le_trans _ (band_lower lo (by norm_num) (by norm_num))
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [den,mul_nonneg lo e]
  · apply le_trans _ (band_lower lo (by norm_num) (by norm_num))
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [den,mul_le_mul_of_nonneg_right hi e]

/-- In units of B², discarding all integer pairs in the corner forced by
D<2^40 costs less than 10^-16. -/
theorem occupancy_corner : (3*2^40+1)^2*(10:ℕ)^16 < (2^1023)^2 := by decide +kernel

/-- Numerical transfer from the smooth mass bounds, the two prime-count
discrepancies per band, and the discarded corner, all normalized by B². -/
theorem band_population {P early central : ℝ}
    (pop : P ≤ (1-log 2)/709^2+12/10^16)
    (forward : (1-log 2)/(10*710^2)-25/10^16 ≤ early)
    (middle : (1-log 2)*40/(1021*710^2)-25/10^16 ≤ central) :
    997*P < 10000*early ∧ 39*P < 1000*central := by
  have h := Real.log_two_lt_d9.le
  constructor <;> linarith only [pop,forward,middle,h]

/-- Natural-cardinality form of the two occupancy bounds. -/
theorem band_counts {P early central : ℕ} {B : ℝ} (bp : 0<B)
    (pop : (P:ℝ)/B^2 ≤ (1-log 2)/709^2+12/10^16)
    (forward : (1-log 2)/(10*710^2)-25/10^16 ≤ (early:ℝ)/B^2)
    (middle : (1-log 2)*40/(1021*710^2)-25/10^16 ≤ (central:ℝ)/B^2) :
    997*P < 10000*early ∧ 39*P < 1000*central := by
  obtain ⟨p,q⟩ := band_population pop forward middle
  have pos : 0<B^2 := sq_pos_of_pos bp
  rw [←mul_div_assoc,←mul_div_assoc,div_lt_div_iff_of_pos_right pos] at p q
  exact_mod_cast And.intro p q

end PrimeFactors.AscendingDivisorRank
