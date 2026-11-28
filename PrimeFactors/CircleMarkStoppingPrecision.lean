import PrimeFactors.CircleMarkStoppingMoments
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Real.Sqrt

/-! Mean square accuracy of the ordinary average of independent, uniform
first-hit ranks. All tuples in the Cartesian sample space have equal weight. -/
namespace PrimeFactors.CircleMarkStoppingPrecision

open Finset CircleMarkStoppingMoments CircleMarkTargetFrequency
open scoped BigOperators

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Arithmetic mean of the K observed ranks. -/
noncomputable def empirical {K : ℕ} (r : α → ℚ) (draw : Fin K → α) : ℚ :=
  (∑ j, r (draw j))/K

/-- Average squared error over every ordered tuple sampled with replacement. -/
noncomputable def meanSquare (r : α → ℚ) (μ : ℚ) (K : ℕ) : ℚ :=
  𝔼 draw : Fin K → α, (empirical r draw-μ)^2

omit [Nonempty α] in
private theorem split_draw {K : ℕ} (f : (Fin (K+1) → α) → ℚ) (g : α → (Fin K → α) → ℚ)
    (eqn : ∀ s, f s = g (s 0) (fun j => s j.succ)) :
    (𝔼 s, f s) = 𝔼 a, 𝔼 t, g a t := by
  calc _ = 𝔼 t : α × (Fin K → α), g t.1 t.2 :=
          Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (K+1) => α)).symm _ _ eqn
       _ = _ := by
         rw [←univ_product_univ]
         exact expect_product' ..

private theorem centered_totals (r : α → ℚ) (zero : (𝔼 x, r x)=0) (K : ℕ) :
    (𝔼 s : Fin K → α, ∑ j, r (s j))=0 ∧
      (𝔼 s : Fin K → α, (∑ j, r (s j))^2)=K*(𝔼 x, (r x)^2) := by
  induction K with
  | zero => simp
  | succ k ih =>
    constructor
    · rw [split_draw _ (fun a t => r a+∑ j, r (t j)) (fun _ => Fin.sum_univ_succ _)]
      simp only [expect_add_distrib,Fintype.expect_const,ih.1,add_zero,zero]
    · have expand (a b : ℚ) : (a+b)^2=a^2+(2*a)*b+b^2 := by ring
      rw [split_draw _ (fun a t => (r a+∑ j, r (t j))^2) (fun _ => by rw [Fin.sum_univ_succ])]
      simp only [expand,expect_add_distrib,Fintype.expect_const,←mul_expect,
        ih.1,mul_zero,add_zero,ih.2,Nat.cast_succ]
      ring

/-- For independent uniform draws, the variance of their average is the
single-draw variance divided by the number of draws. -/
theorem sample_variance (r : α → ℚ) {μ : ℚ} (first : (𝔼 x, r x)=μ) {K : ℕ} (kp : 0<K) :
    meanSquare r μ K=(𝔼 x, (r x-μ)^2)/K := by
  have kn : (K:ℚ)≠0 := by exact_mod_cast kp.ne'
  have centered : (𝔼 x, (r x-μ))=0 := by rw [expect_sub_distrib,Fintype.expect_const,first,sub_self]
  have totals := (centered_totals (fun x => r x-μ) centered K).2
  have move (s : Fin K → α) : empirical r s-μ=(∑ j, (r (s j)-μ))/K := by
    simp only [empirical,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  unfold meanSquare
  simp_rw [move,div_pow]
  rw [←expect_div,totals]
  field_simp
  ring

/-- Within-prime variance and between-prime variance of the first-hit rank. -/
noncomputable def rankVariance (p q : ℕ) : ℚ :=
  (((p:ℚ)-1)^2+((q:ℚ)-1)^2-8)/96 + ((p:ℚ)-q)^2/64

/-- Variance of the actual finite population of first-hit ranks. -/
theorem population_variance {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) :
    rawMoment (p*q) 2-(rawMoment (p*q) 1)^2=rankVariance p q := by
  rw [first_moment diff op oq,second_moment diff op oq,rankVariance]
  ring

/-- Comparing the single-draw variance with the number of eligible targets
gives an exact correction term depending only on the prime gap. -/
theorem population_comparison {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) :
    64*rankVariance p q - 8/3*((targets (p*q)).card:ℚ)=(5*((p:ℚ)-q)^2-16)/3 := by
  rw [(counts diff op oq ∅).1]
  obtain ⟨x,hx⟩ := hp.out.odd_of_ne_two op
  obtain ⟨y,hy⟩ := hq.out.odd_of_ne_two oq
  rw [show (p-1)/2=x by omega,show (q-1)/2=y by omega,hx,hy,rankVariance]
  push_cast
  ring

/-- The two raw moments suffice to compute the mean square error of the
ordinary sample average on the full Cartesian space. -/
theorem rank_error (p q : ℕ) (r : α → ℚ)
    (first : (𝔼 x, r x)=((p:ℚ)+q+2)/8)
    (second : (𝔼 x, (r x)^2)=((p:ℚ)*(p+1)+(q:ℚ)*(q+1))/24) {K : ℕ} (kp : 0<K) :
    meanSquare r (((p:ℚ)+q+2)/8) K=rankVariance p q/K := by
  rw [sample_variance r first kp]
  congr 1
  let μ : ℚ := ((p:ℚ)+q+2)/8
  have expand (x : α) : (r x-μ)^2=(r x)^2-r x*(2*μ)+μ^2 := by ring
  change (𝔼 x, (r x-μ)^2)=_
  simp only [expand,expect_add_distrib,expect_sub_distrib,Fintype.expect_const,←expect_mul,
    first,second,rankVariance,μ]
  ring

/-- A strict lower bound in terms of any common power-of-two lower endpoint,
for positive odd primes with distinct values. -/
theorem variance_lower {p q w : ℕ} (op : Odd p) (oq : Odd q) (order : p<q)
    (wp : 0<w) (lo : 2^w≤p) : (2:ℚ)^(2*w)/48 < rankVariance p q := by
  have even : Even (2^w : ℕ) := Even.pow_of_ne_zero (by decide : Even 2) wp.ne'
  obtain ⟨a,ha⟩ := op
  obtain ⟨b,hb⟩ := oq
  obtain ⟨c,hc⟩ := even
  have pl : (2:ℚ)^w+1 ≤ p := by exact_mod_cast (show 2^w+1≤p by omega)
  have ql : (2:ℚ)^w+3 ≤ q := by exact_mod_cast (show 2^w+3≤q by omega)
  have pw : (1:ℚ)≤2^w := one_le_pow₀ (by norm_num)
  have psq := sq_le_sq' (show -((p:ℚ)-1)≤2^w by linarith) (show (2:ℚ)^w≤p-1 by linarith)
  have qsq := sq_le_sq' (show -((q:ℚ)-1)≤2^w+2 by linarith) (show (2:ℚ)^w+2≤q-1 by linarith)
  rw [mul_comm 2 w,pow_mul,rankVariance]
  have two : (2:ℚ)≤2^w := by
    simpa only [pow_one] using (pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) wp)
  nlinarith only [psq,qsq,two,sq_nonneg ((p:ℚ)-q)]

/-- A root-mean-square accuracy requirement for the ordinary sample average
forces a minimum sample size at every dyadic lower endpoint. -/
theorem rms_budget {p q w K : ℕ} {mse e : ℚ} (op : Odd p) (oq : Odd q) (order : p<q)
    (wp : 0<w) (lo : 2^w≤p) (kp : 0<K) (ep : 0<e)
    (error : mse=rankVariance p q/K) (rms : Real.sqrt (mse:ℝ)<(e:ℝ)) :
    (2:ℚ)^(2*w) < 48*e^2*K := by
  have square : mse<e^2 := by
    have bound := (Real.sqrt_lt' (by exact_mod_cast ep : 0<(e:ℝ))).mp rms
    exact_mod_cast bound
  rw [error] at square
  have total := (div_lt_iff₀ (by exact_mod_cast kp : 0<(K:ℚ))).mp square
  linarith only [variance_lower op oq order wp lo,total]

set_option exponentiation.threshold 4096

/-- At 1024-bit prime width the two accuracy thresholds yield explicit
sample-size requirements. The denominator in the second threshold allows
the extra residue information available on some products. -/
theorem full_budget {p q K : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (lo : 2^1023≤p) (order : p<q) (kp : 0<K) {mse : ℚ} (error : mse=rankVariance p q/K) :
    (Real.sqrt (mse:ℝ)<1/8 → 2^2048<3*K) ∧
    (Real.sqrt (mse:ℝ)<1/2 → 2^2044<3*K) := by
  have pgt := (by decide +kernel : 2<2^1023).trans_le lo
  have lower (e : ℚ) (ep : 0<e) (small : Real.sqrt (mse:ℝ)<(e:ℝ)) :=
    rms_budget (hp.out.odd_of_ne_two pgt.ne') (hq.out.odd_of_ne_two (pgt.trans order).ne')
      order (by decide : 0<1023) lo kp ep error small
  constructor
  · intro small
    have b := lower (1/8) (by norm_num) (by push_cast; exact small)
    have scale : (2:ℚ)^2048=4*2^(2*1023) := by norm_num
    have c := mul_lt_mul_of_pos_left b (by decide : (0:ℚ)<4)
    rw [←scale] at c
    have coeff : (4:ℚ)*(48*(1/8)^2*K)=3*K := by ring
    rw [coeff] at c
    exact_mod_cast c
  · intro small
    have b := lower (1/2) (by norm_num) (by push_cast; exact small)
    have scale : (2:ℚ)^(2*1023)=4*2^2044 := by norm_num
    rw [scale] at b
    exact_mod_cast (show (2:ℚ)^2044 < 3*K by linarith only [b])

/-- Mean square error when the observations are the actual first-hit ranks
of independent, uniformly selected Jacobi-negative target classes. -/
theorem actual_error {p q K : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (kp : 0<K) :
    meanSquare (fun t => (rank (p*q) t : ℚ)) (((p:ℚ)+q+2)/8) K=rankVariance p q/K := by
  have nonempty : 0<(targets (p*q)).card := by
    rw [(counts diff op oq ∅).1]
    have := hp.out.two_le
    have := hq.out.two_le
    exact Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)
  obtain ⟨t,ht⟩ := card_pos.mp nonempty
  letI : Nonempty ↥(targets (p*q)) := ⟨⟨t,ht⟩⟩
  apply rank_error _ _ _ _ _ kp
  · simpa only [pow_one] using
      (rawMoment_eq_target_mean (p*q) 1 (by decide)).symm.trans (first_moment diff op oq)
  · exact (rawMoment_eq_target_mean (p*q) 2 (by decide)).symm.trans (second_moment diff op oq)

/-- At one-eighth RMS accuracy the average needs more than eight thirds
as many draws as there are eligible targets; at one-half it needs over one sixth. -/
theorem population_budget {p q K : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (kp : 0<K) :
    let e := Real.sqrt ((meanSquare (fun t => (rank (p*q) t : ℚ)) (((p:ℚ)+q+2)/8) K : ℚ) : ℝ)
    (e<1/8 → 8*(targets (p*q)).card<3*K) ∧ (e<1/2 → (targets (p*q)).card<6*K) := by
  rw [actual_error order.ne op oq kp]
  obtain ⟨a,ha⟩ := hp.out.odd_of_ne_two op
  obtain ⟨b,hb⟩ := hq.out.odd_of_ne_two oq
  have gap : (p:ℚ)+2≤q := by exact_mod_cast (show p+2≤q by omega)
  have gapSq := sq_le_sq' (show -((q:ℚ)-p)≤2 by linarith) (show (2:ℚ)≤q-p by linarith)
  have compare := population_comparison order.ne op oq
  have lower : 8*((targets (p*q)).card:ℚ)<192*rankVariance p q := by
    nlinarith only [compare,gapSq]
  have cv (d : ℚ) (pos : 0<d) (r : Real.sqrt ((rankVariance p q/(K:ℚ):ℚ):ℝ)<(d:ℝ)) :
      rankVariance p q < d^2*K := by
    apply (div_lt_iff₀ (by exact_mod_cast kp : 0<(K:ℚ))).mp
    exact_mod_cast (Real.sqrt_lt' (by exact_mod_cast pos : 0<(d:ℝ))).mp r
  constructor
  · intro r
    have bound := cv (1/8) (by norm_num) (by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using r)
    exact_mod_cast (show 8*((targets (p*q)).card:ℚ)<3*K by linarith only [lower,bound])
  · intro r
    have bound := cv (1/2) (by norm_num) (by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using r)
    exact_mod_cast (show ((targets (p*q)).card:ℚ)<6*K by linarith only [lower,bound])

/-- Sample counts required for the actual target-rank average at full width. -/
theorem full_width {p q K : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lo : 2^1023≤p) (order : p<q) (kp : 0<K) :
    let e := Real.sqrt ((meanSquare (fun t => (rank (p*q) t : ℚ)) (((p:ℚ)+q+2)/8) K : ℚ) : ℝ)
    (e<1/8 → 2^2048<3*K) ∧ (e<1/2 → 2^2044<3*K) := by
  have big := (by decide +kernel : 2<2^1023).trans_le lo
  exact full_budget lo order kp (actual_error order.ne big.ne' (big.trans order).ne' kp)

/-- Independent estimates need to distinguish adjacent even factor sums.
Their population means lie a quarter unit apart. -/
theorem sum_unique {s t : ℤ} (se : Even s) (te : Even t) {m : ℚ}
    (sm : |m-((s:ℚ)+2)/8|<1/8) (tm : |m-((t:ℚ)+2)/8|<1/8) : s=t := by
  obtain ⟨x,hx⟩ := se
  obtain ⟨y,hy⟩ := te
  rw [abs_lt] at sm tm
  have l : (s:ℚ)<(t:ℚ)+2 := by linarith
  have r : (t:ℚ)<(s:ℚ)+2 := by linarith
  have L : s<t+2 := by exact_mod_cast l
  have R : t<s+2 := by exact_mod_cast r
  omega

end PrimeFactors.CircleMarkStoppingPrecision
