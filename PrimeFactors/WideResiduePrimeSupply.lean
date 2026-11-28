import PrimeFactors.AdmissibleSumRealization
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! A finite consequence of the two arithmetic-progression prime-count
estimates of Ernvall-Hytönen and Palojärvi, Corollary 2
(https://arxiv.org/pdf/2003.01925#page=2). That corollary assumes Dirichlet
GRH. Its endpoint inequalities are hypotheses here. The difference of the
two logarithmic integrals is an ordinary proper integral defined below. -/
namespace PrimeFactors.WideResiduePrimeSupply

open Finset Real MeasureTheory
set_option exponentiation.threshold 4096

abbrev L : ℕ := 3*2^1022
abbrev B : ℕ := 2^1024

/-- The paper counts primes up to and including x in a reduced residue class. -/
noncomputable def through (m a x : ℕ) : Finset ℕ :=
  (range (x+1)).filter (fun p => p.Prime ∧ p%m=a)

/-- Primes with residue a in the half-open interval (A,A+W]. -/
noncomputable def inBand (m a A W : ℕ) := through m a (A+W) \ through m a A

theorem mem_band {m a A W p : ℕ} : p∈inBand m a A W ↔
    p.Prime ∧ p%m=a ∧ A<p ∧ p≤A+W := by
  simp only [inBand,through,mem_sdiff,mem_filter,mem_range,Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨hi,P,res⟩,out⟩
    exact ⟨P,res,lt_of_not_ge (fun lo => out ⟨lo,P,res⟩),hi⟩
  · rintro ⟨P,res,lo,hi⟩
    exact ⟨⟨hi,P,res⟩,fun h => (not_le_of_gt lo) h.1⟩

noncomputable abbrev intervalPrimes (m a : ℕ) := inBand m a L (2^1022)

theorem mem_interval {m a p : ℕ} : p∈intervalPrimes m a ↔
    p.Prime ∧ p%m=a ∧ L<p ∧ p≤B := mem_band

/-- Proper integral giving li(A+W)−li(A) whenever A>1. -/
noncomputable def increment (A W : ℕ) : ℝ := ∫ x in (A:ℝ)..((A+W:ℕ):ℝ), 1/log x

/-- The published upper bound, including its subtractive constant. -/
noncomputable def ehpError (m : ℕ) (x : ℝ) : ℝ :=
  (1/(8*π*m.totient)+1/(6*π))*sqrt x*log x+
    (0.184*log m+12969.946)*sqrt x-237.934

/-- The two estimates for one residue. The common value c stands for li(A). -/
def BandEndpoints (m a A W : ℕ) (c : ℝ) : Prop :=
  |((through m a A).card:ℝ)-c/m.totient| ≤ ehpError m A ∧
  |((through m a (A+W)).card:ℝ)-(c+increment A W)/m.totient| ≤ ehpError m (A+W:ℕ)

abbrev Endpoints (m a : ℕ) (c : ℝ) := BandEndpoints m a L (2^1022) c

/-- Both endpoints meet the domain requirement x≥m of Corollary 2. -/
theorem endpoint_domain {m : ℕ} (cap : m≤2^485) : m≤L ∧ L≤B := by
  exact ⟨cap.trans (by decide +kernel),by decide +kernel⟩

private theorem log_bound {x : ℝ} (xp : 0<x) (hi : x≤B) : log x≤710 := by
  have hx := log_le_log xp hi
  simp only [B,Nat.cast_pow,Nat.cast_ofNat,log_pow] at hx
  linarith only [hx,log_two_lt_d9]

/-- The proper logarithmic integral on a band is bounded below by its
width times the constant 1/710. -/
theorem increment_lower {A W : ℕ} (left : 2^1023≤A) (right : A+W≤B) :
    (W:ℝ)/710 ≤ increment A W := by
  have lo : (1:ℝ)<A := by exact_mod_cast (lt_of_lt_of_le (by decide : 1<2^1023) left)
  have ord : (A:ℝ)≤((A+W:ℕ):ℝ) := by exact_mod_cast Nat.le_add_right A W
  have cont : ContinuousOn (fun x : ℝ => 1/log x) (Set.Icc (A:ℝ) ((A+W:ℕ):ℝ)) := by
    apply continuousOn_const.div
    · exact continuousOn_log.mono (fun x hx => (lt_trans (by norm_num : (0:ℝ)<1) (lo.trans_le hx.1)).ne')
    · intro x hx
      exact (log_pos (lo.trans_le hx.1)).ne'
  have bound := intervalIntegral.integral_mono_on (μ:=volume) (f:=fun _ : ℝ => (1:ℝ)/710)
    (g:=fun x : ℝ => 1/log x) ord intervalIntegrable_const (cont.intervalIntegrable_of_Icc ord) (by
      intro x hx
      exact one_div_le_one_div_of_le (log_pos (lo.trans_le hx.1)) (log_bound (by linarith [hx.1]) (hx.2.trans (by exact_mod_cast right))))
  rw [intervalIntegral.integral_const,smul_eq_mul] at bound
  simpa only [increment,Nat.cast_add,add_sub_cancel_left,div_eq_mul_inv,one_mul] using bound

/-- On the entire interval the stated error term costs at most 13200·2^512 per endpoint. -/
theorem error_cap {m : ℕ} (low : 3≤m) (cap : m≤B) {x : ℝ} (xl : (2:ℝ)^1023≤x) (xh : x≤B) :
    ehpError m x ≤ 13200*(2:ℝ)^512 := by
  have mp : 0<m := by omega
  have tot : (1:ℝ)≤m.totient := by exact_mod_cast Nat.totient_pos.mpr mp
  have pi3 := pi_gt_three
  have phi : (24:ℝ)≤8*π*m.totient := by
    nlinarith only [mul_le_mul_of_nonneg_left tot (le_of_lt pi_pos),pi3]
  have coeff : (1/(8*π*m.totient)+1/(6*π)) ≤ (1/24+1/18:ℝ) :=
    add_le_add (one_div_le_one_div_of_le (by norm_num) phi)
      (one_div_le_one_div_of_le (by norm_num) (by linarith only [pi3]))
  have one : (1:ℝ)<2^1023 := by norm_num
  have xp : 1<x := one.trans_le xl
  have sx : sqrt x≤(2:ℝ)^512 := (Real.sqrt_le_left (by positivity)).mpr (by
    calc x ≤ B := xh
         _ = ((2:ℝ)^512)^2 := by norm_num [B])
  have lx := log_bound (by linarith only [xp]) xh
  have lm := log_bound (Nat.cast_pos.mpr mp) (by exact_mod_cast cap)
  have term := mul_le_mul (mul_le_mul_of_nonneg_right coeff (Real.sqrt_nonneg x)) lx
    (log_nonneg xp.le) (by positivity)
  have term' := mul_le_mul_of_nonneg_right (show 0.184*log (m:ℝ)+12969.946≤0.184*710+12969.946 by linarith only [lm]) (Real.sqrt_nonneg x)
  unfold ehpError
  linarith only [term,term',sx]

private theorem count_add (m a A W : ℕ) :
    (inBand m a A W).card + (through m a A).card = (through m a (A+W)).card := by
  exact card_sdiff_add_card_eq_card (filter_subset_filter _ (range_mono (Nat.succ_le_succ (Nat.le_add_right A W))))

/-- A uniform lower bound for any band inside [2^1023,2^1024]. -/
theorem band_lower {m a A W : ℕ} (low : 3≤m) (domain : m≤A) (left : 2^1023≤A)
    (right : A+W≤B) {c : ℝ} (bounds : BandEndpoints m a A W c) :
    (W:ℝ)/(710*(m.totient:ℝ)) - 26400*(2:ℝ)^512 ≤ ((inBand m a A W).card:ℝ) := by
  have ord := Nat.le_add_right A W
  have mcap := domain.trans (ord.trans right)
  have lowError := (abs_le.mp (bounds.1.trans (error_cap low mcap (by exact_mod_cast left)
    (by exact_mod_cast ord.trans right)))).2
  have highError := (abs_le.mp (bounds.2.trans (error_cap low mcap (by exact_mod_cast left.trans ord)
    (by exact_mod_cast right)))).1
  have ph : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (show 0<m by omega)
  have main := div_le_div_of_nonneg_right (increment_lower left right) ph.le
  have count : ((inBand m a A W).card:ℝ)+(through m a A).card=(through m a (A+W)).card := by
    exact_mod_cast count_add m a A W
  rw [add_div] at highError
  rw [←div_div]
  linarith only [count,main,highError,lowError]

/-- Each supplied pair of endpoint estimates gives more than 2^526 primes
in one specified class, uniformly over all moduli from 3 through 2^485. -/
theorem class_population {m a : ℕ} (low : 3≤m) (cap : m≤2^485) {c : ℝ}
    (bounds : Endpoints m a c) : 2^526 < (intervalPrimes m a).card := by
  have bound := band_lower low (endpoint_domain cap).1 (by decide : 2^1023≤L)
    (by decide : L+2^1022≤B) bounds
  have ph : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (show 0<m by omega)
  have phCap : (m.totient:ℝ)≤2^485 := by exact_mod_cast (Nat.totient_le m).trans cap
  have main : (2:ℝ)^1022/(710*2^485) ≤ ((2^1022:ℕ):ℝ)/(710*m.totient) := by
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact div_le_div_of_nonneg_left (pow_nonneg (by norm_num : (0:ℝ)≤2) 1022)
      (mul_pos (by norm_num : (0:ℝ)<710) ph)
      (mul_le_mul_of_nonneg_left phCap (by norm_num))
  have margin : (2:ℝ)^526 < (2:ℝ)^1022/(710*2^485)-26400*2^512 := by norm_num
  exact_mod_cast (show (2:ℝ)^526 < (intervalPrimes m a).card by
    change _ < ((inBand m a L (2^1022)).card:ℝ)
    exact (margin.trans_le (sub_le_sub_right main _)).trans_le bound)

/-- Two distinct representatives can be chosen strictly below the upper endpoint,
since the upper endpoint is composite. -/
theorem supply {m : ℕ} (low : 3≤m) (cap : m≤2^485) (c : ℝ)
    (bounds : ∀ a<m, a.Coprime m → Endpoints m a c) :
    AdmissibleSumRealization.TwoRepresentatives m (L+1) B := by
  intro a ha unit
  have cnt := class_population low cap (bounds a ha unit)
  obtain ⟨p,q,pl,ql,ne⟩ := Finset.one_lt_card_iff.mp (by omega : 1<(intervalPrimes m a).card)
  have strict (v : ℕ) (h : v∈intervalPrimes m a) : v<B :=
    (mem_interval.mp h).2.2.2.lt_of_ne (fun eq =>
      (Nat.Prime.not_prime_pow (by decide : 2≤1024) (x:=2))
        ((congrArg Nat.Prime eq).mp (mem_interval.mp h).1))
  obtain ⟨P,pc,lp,_⟩ := mem_interval.mp pl
  obtain ⟨Q,qc,lq,_⟩ := mem_interval.mp ql
  rcases lt_or_gt_of_ne ne with lt|gt
  · exact ⟨p,q,lp,lt,strict q ql,P,Q,pc,qc⟩
  · exact ⟨q,p,lq,gt,strict p pl,Q,P,qc,pc⟩

/-- The integer product varies with the prescribed local sum and product classes. -/
theorem realized {m : ℕ} [NeZero m] (low : 3≤m) (cap : m≤2^485) (c : ℝ)
    (bounds : ∀ a<m, a.Coprime m → Endpoints m a c) (r s : ZMod m) (unit : IsUnit r) :
    AdmissibleSum r s ↔ AdmissibleSumRealization.Realized (L+1) B r s :=
  AdmissibleSumRealization.iff_realized (supply low cap c bounds) r s unit

end PrimeFactors.WideResiduePrimeSupply
