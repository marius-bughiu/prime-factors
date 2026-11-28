import PrimeFactors.InverseCyclotomicMeasurements
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Rational interval certificates for two small products and single supplied
evaluations. Alternative trial sums use real factors of the same product. -/

namespace PrimeFactors.SingleCyclotomicValueControl

open Polynomial Real Finset

private noncomputable def poly (u : ℝ) :=
  1+u+u^2/2+u^3/6+u^4/24+u^5/120

private noncomputable def lower (u : ℝ) := 1-1/poly u
private noncomputable def upper (u : ℝ) := 1-1/(poly u+7*u^6/4320)

/-- The Taylor remainder at a nonnegative argument has known sign and an
explicit upper bound. Taking reciprocals encloses exp at negative arguments. -/
private theorem term_box {a u b : ℝ} (a0 : 0≤a) (au : a≤u) (ub : u≤b) (b1 : b≤1) :
    lower a≤1-exp (-u) ∧ 1-exp (-u)≤upper b := by
  have b0 := a0.trans (au.trans ub)
  have left := sum_le_exp_of_nonneg a0 6
  have right := exp_bound' b0 b1 (n:=6) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at left right
  have pl : poly a ≤ exp u := by
    apply le_trans _ (exp_le_exp.mpr au)
    unfold poly
    linarith only [left]
  have ph : exp u≤poly b+7*b^6/4320 := by
    apply (exp_le_exp.mpr ub).trans
    unfold poly
    linarith only [right]
  have pos : 0<poly a := by unfold poly; positivity
  have l := one_div_le_one_div_of_le pos pl
  have r := one_div_le_one_div_of_le (exp_pos u) ph
  unfold lower upper
  rw [exp_neg, ←one_div]
  constructor <;> linarith

noncomputable def scaled (D a b : ℝ) := (1-exp (-(a/D)))*(1-exp (-(b/D)))
noncomputable def reading (a b : ℝ) := scaled 128 a b

private theorem rectangle {D a b al ah bl bh L H : ℝ}
    (a0 : 0≤al) (a1 : ah≤1) (b0 : 0≤bl) (b1 : bh≤1)
    (aLow : al≤a/D) (aHigh : a/D≤ah) (bLow : bl≤b/D) (bHigh : b/D≤bh)
    (lp : 0≤lower al) (lq : 0≤lower bl)
    (below : L<lower al*lower bl) (above : upper ah*upper bh<H) :
    L<scaled D a b ∧ scaled D a b<H := by
  obtain ⟨xl,xh⟩ := term_box a0 aLow aHigh a1
  obtain ⟨yl,yh⟩ := term_box b0 bLow bHigh b1
  exact ⟨below.trans_le (mul_le_mul xl yl lq (lp.trans xl)),
    (mul_le_mul xh yh (lq.trans yl) (lp.trans (xl.trans xh))).trans_lt above⟩

noncomputable def smallRoot (s : ℝ) := (s-sqrt (s^2-4*551))/2
noncomputable def largeRoot (s : ℝ) := (s+sqrt (s^2-4*551))/2
noncomputable def trial (s : ℝ) := reading (smallRoot s) (largeRoot s)

/-- These are actual real coordinates on the fixed product curve. -/
theorem coordinates {s : ℝ} (disc : 4*551≤s^2) :
    smallRoot s+largeRoot s=s ∧ smallRoot s*largeRoot s=551 := by
  have root := sq_sqrt (sub_nonneg.mpr disc)
  unfold smallRoot largeRoot
  constructor
  · ring
  · calc (s-sqrt (s^2-4*551))/2*((s+sqrt (s^2-4*551))/2) =
           (s^2-(sqrt (s^2-4*551))^2)/4 := by ring
         _ = 551 := by rw [root]; ring

/-- Within the balanced band, these three integers exhaust all possible
trial sums for the real product 551. -/
theorem integer_trials {s : ℕ} {a b : ℝ} (prod : a*b=551) (sum : a+b=s)
    (aTop : a≤32) (bTop : b≤32) : s=47 ∨ s=48 ∨ s=49 := by
  have roof := mul_nonneg (sub_nonneg.mpr aTop) (sub_nonneg.mpr bTop)
  have cap : (s:ℝ)<50 := by nlinarith only [roof,prod,sum]
  have high : s<50 := by exact_mod_cast cap
  have low : 47≤s := by
    by_contra! bad
    have h : (s:ℝ)≤46 := by exact_mod_cast (show s≤46 by omega)
    have sq := mul_self_le_mul_self (by positivity : 0≤(s:ℝ)) h
    rw [←sum] at sq
    nlinarith only [sq_nonneg (a-b),sq,prod]
  omega

theorem at_47 : 28068/1000000<trial 47 ∧ trial 47<28069/1000000 := by
  have sl : (2236067:ℝ)/1000000≤sqrt 5 := le_sqrt_of_sq_le (by norm_num)
  have sh : sqrt (5:ℝ)≤2236068/1000000 := (sqrt_le_left (by norm_num)).mpr (by norm_num)
  unfold trial
  apply rectangle (D:=128) (al:=11190983/64000000) (ah:=44763933/256000000)
    (bl:=49236067/256000000) (bh:=12309017/64000000) <;>
    first | norm_num [lower,upper,poly]; done
          | norm_num [smallRoot,largeRoot]; linarith

theorem at_48 : 27965/1000000<reading 19 29 ∧ reading 19 29<27966/1000000 := by
  apply rectangle (D:=128) (al:=19/128) (ah:=19/128) (bl:=29/128) (bh:=29/128)
    <;> norm_num [lower,upper,poly]

theorem at_49 : 27863/1000000<trial 49 ∧ trial 49<27864/1000000 := by
  have sl : (14035668:ℝ)/1000000≤sqrt 197 := le_sqrt_of_sq_le (by norm_num)
  have sh : sqrt (197:ℝ)≤14035669/1000000 := (sqrt_le_left (by norm_num)).mpr (by norm_num)
  unfold trial
  apply rectangle (D:=128) (al:=34964331/256000000) (ah:=8741083/64000000)
    (bl:=15758917/64000000) (bh:=63035669/256000000) <;>
    first | norm_num [lower,upper,poly]; done
          | norm_num [smallRoot,largeRoot]; linarith

/-- The measured expression is the public-index polynomial at the specified
point. The known factorization justifies the equality in this control. -/
theorem value_551 :
    (InverseCyclotomicMeasurements.polynomial 551).eval₂ (Int.castRingHom ℝ) (exp (-(1/128))) =
      reading 19 29 := by
  have form := InverseCyclotomicMeasurements.sparse (p:=19) (q:=29)
    (by norm_num) (by norm_num) (by norm_num)
  change InverseCyclotomicMeasurements.polynomial 551=_ at form
  rw [form]
  simp only [eval₂_mul,eval₂_sub,eval₂_one,eval₂_pow,eval₂_X,←Real.exp_nat_mul,reading,scaled]
  norm_num

theorem separation :
    trial 48=reading 19 29 ∧ 101/1000000<trial 47-trial 48 ∧ 101/1000000<trial 48-trial 49 := by
  have same : trial 48=reading 19 29 := by norm_num [trial,smallRoot,largeRoot,Real.sqrt_eq_iff_eq_sq]
  rw [same]
  exact ⟨rfl,by linarith only [at_47.1,at_48.2],by linarith only [at_48.1,at_49.2]⟩

/-- The real factors at the competing sum 370 for the eight-bit control. -/
noncomputable def pair370 : ℝ×ℝ :=
  ((370-sqrt 5376)/2,(370+sqrt 5376)/2)

private theorem sqrt_5376 :
    (73321211:ℝ)/1000000≤sqrt 5376 ∧ sqrt 5376≤73321212/1000000 :=
  ⟨le_sqrt_of_sq_le (by norm_num),(sqrt_le_left (by norm_num)).mpr (by norm_num)⟩

theorem real_trial_370 : pair370.1+pair370.2=370 ∧ pair370.1*pair370.2=32881 ∧
    128≤pair370.1 ∧ pair370.1≤pair370.2 ∧ pair370.2<256 := by
  dsimp only [pair370]
  refine ⟨by ring,?_,?_,?_,?_⟩
  · calc (370-sqrt (5376:ℝ))/2*((370+sqrt 5376)/2) =
           (370^2-(sqrt (5376:ℝ))^2)/4 := by ring
         _ = 32881 := by rw [sq_sqrt (by norm_num)]; norm_num
  all_goals linarith only [sqrt_5376.1,sqrt_5376.2]

/-- Both sums pass the centered discriminant tests, including the stronger
combined test modulo 1680. At sum 370, 17 and 353 witness the trace and norm
simultaneously at that modulus. The centered discriminant 1344 lies between
two consecutive integer squares. -/
theorem public_screens :
    (370/2)^2-32881=1344 ∧ (382/2)^2-32881=3600 ∧
    36^2<(1344:ℕ) ∧ (1344:ℕ)<37^2 ∧
    17+353=370 ∧ 17*353 ≡ 32881 [MOD 1680] ∧
    (168:ℕ)^2 ≡ 1344 [MOD 1680] ∧ (60:ℕ)^2=3600 ∧
    ∀ m∈([16,3,5,7]:List ℕ),
      (168:ℕ)^2 ≡ (370/2)^2-32881 [MOD m] ∧ (60:ℕ)^2 ≡ (382/2)^2-32881 [MOD m] := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide,?_⟩
  intro m hm
  have divides : m∣1680 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl <;> decide
  exact ⟨(show 168^2 ≡ (370/2)^2-32881 [MOD 1680] by decide).of_dvd divides,
    (show 60^2 ≡ (382/2)^2-32881 [MOD 1680] by decide).of_dvd divides⟩

theorem at_370 : 26248/1000000<scaled 1024 pair370.1 pair370.2 ∧
    scaled 1024 pair370.1 pair370.2<26249/1000000 := by
  apply rectangle (D:=1024) (al:=74169697/512000000) (ah:=296678789/2048000000)
    (bl:=443321211/2048000000) (bh:=110830303/512000000) <;>
    first | norm_num [lower,upper,poly]; done
          | dsimp only [pair370]; linarith only [sqrt_5376.1,sqrt_5376.2]

theorem at_382 : 26104/1000000<scaled 1024 131 251 ∧
    scaled 1024 131 251<26105/1000000 := by
  apply rectangle (D:=1024) (al:=131/1024) (ah:=131/1024) (bl:=251/1024) (bh:=251/1024)
    <;> norm_num [lower,upper,poly]

theorem value_32881 :
    (InverseCyclotomicMeasurements.polynomial 32881).eval₂ (Int.castRingHom ℝ) (exp (-(1/1024))) =
      scaled 1024 131 251 := by
  have form := InverseCyclotomicMeasurements.sparse (p:=131) (q:=251)
    (by norm_num) (by norm_num) (by norm_num)
  change InverseCyclotomicMeasurements.polynomial 32881=_ at form
  rw [form]
  simp only [eval₂_mul,eval₂_sub,eval₂_one,eval₂_pow,eval₂_X,←Real.exp_nat_mul,scaled]
  norm_num

theorem separation_32881 : Nat.Prime 131 ∧ Nat.Prime 251 ∧ 131*251=32881 ∧ 131+251=382 ∧
    (143:ℝ)/1000000 < scaled 1024 pair370.1 pair370.2-scaled 1024 131 251 :=
  ⟨by norm_num,by norm_num,by decide,by decide,by linarith only [at_370.1,at_382.2]⟩

end PrimeFactors.SingleCyclotomicValueControl
