import PrimeFactors.CircleMarkMidcutReadout
import PrimeFactors.CircleMarkStoppingPrecision

/-! Precision of the signed midpoint estimator when sampling uniformly from the
entire residue ring. Ineligible residues contribute zero to the signed score. -/
namespace PrimeFactors.CircleMarkMidcutSampling

open Finset CircleMarkTargetFrequency CircleMarkMidcutReadout CircleMarkStoppingPrecision
open scoped Classical BigOperators

/-- A single signed observation, normalized to estimate the smaller prime. -/
noncomputable def estimate (n : ℕ) [NeZero n] (t : ZMod n) : ℚ :=
  1+(n:ℚ)/cutoff n*(score n t:ℚ)

noncomputable def variance (n p : ℕ) [NeZero n] : ℚ :=
  (n:ℚ)*(targets n).card/(cutoff n:ℚ)^2-((p:ℚ)-1)^2

/-- Raw moments of the signed observation on all residues. -/
theorem score_moments {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q)
    (op : p≠2) (oq : q≠2) :
    (𝔼 t : ZMod (p*q), (score (p*q) t:ℚ)) = (cutoff (p*q):ℚ)*((p:ℚ)-1)/(p*q:ℕ) ∧
    (𝔼 t : ZMod (p*q), (score (p*q) t:ℚ)^2) = ((targets (p*q)).card:ℚ)/(p*q:ℕ) := by
  constructor
  · rw [Fintype.expect_eq_sum_div_card,ZMod.card,←Int.cast_sum]
    congr 1
    exact_mod_cast imbalance_eq order op oq
  · have obs (t : ZMod (p*q)) : (score (p*q) t:ℚ)^2=
        if t∈targets (p*q) then 1 else 0 := by
      by_cases h : t∈hits (p*q) (Icc 1 (cutoff (p*q)))
      · have target := (mem_filter.mp h).1
        simp [score,h,target]
      · by_cases target : t∈targets (p*q) <;> simp [score,h,target]
    rw [Fintype.expect_eq_sum_div_card,ZMod.card]
    simp only [obs,sum_boole,filter_mem_eq_inter,univ_inter]

theorem unbiased {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (order : p<q)
    (op : p≠2) (oq : q≠2) : (𝔼 t, estimate (p*q) t)=(p:ℚ) := by
  have a := (score_moments order op oq).1
  have np : ((p*q:ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_ne_zero hp.out.ne_zero hq.out.ne_zero)
  have kp : (cutoff (p*q):ℚ)≠0 := by exact_mod_cast (cutoff_pos order op).ne'
  simp only [estimate,expect_add_distrib,Fintype.expect_const,←mul_expect,a]
  generalize ((p*q:ℕ):ℚ)=N at np ⊢
  generalize (cutoff (p*q):ℚ)=k at kp ⊢
  field_simp
  ring

/-- Average squared deviation of one public observation from the smaller prime. -/
theorem single_variance {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (order : p<q)
    (op : p≠2) (oq : q≠2) :
    (𝔼 t, (estimate (p*q) t-p)^2)=variance (p*q) p := by
  have ns : ((p*q:ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_ne_zero hp.out.ne_zero hq.out.ne_zero)
  have ks : (cutoff (p*q):ℚ)≠0 := by exact_mod_cast (cutoff_pos order op).ne'
  let n := p*q
  let a := (n:ℚ)/cutoff n
  obtain ⟨s1,s2⟩ := score_moments order op oq
  have expand (t : ZMod n) : (estimate n t-p)^2=
      a^2*(score n t:ℚ)^2 - (2*((p:ℚ)-1)*a)*(score n t:ℚ) + ((p:ℚ)-1)^2 := by
    simp only [estimate,a]; ring
  change (𝔼 t, (estimate n t-p)^2)=_
  simp only [expand,expect_add_distrib,expect_sub_distrib,Fintype.expect_const,←mul_expect]
  dsimp only [a,n]
  rw [s1,s2,variance]
  generalize ((p*q:ℕ):ℚ)=N at ns ⊢
  generalize (cutoff (p*q):ℚ)=k at ks ⊢
  field_simp
  ring

/-- Exact mean squared error of the ordinary average of uniform draws
with replacement, counted on the full Cartesian sample space. -/
theorem sample_error {p q draws : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q)
    (op : p≠2) (oq : q≠2) (dp : 0<draws) :
    meanSquare (estimate (p*q)) p draws=variance (p*q) p/draws := by
  rw [sample_variance _ (unbiased order op oq) dp,single_variance order op oq]

private theorem target_size {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) :
    ((targets (p*q)).card:ℚ)=((p:ℚ)-1)*((q:ℚ)-1)/2 := by
  rw [(counts order.ne op oq ∅).1]
  obtain ⟨x,hx⟩ := hp.out.odd_of_ne_two op
  obtain ⟨y,hy⟩ := hq.out.odd_of_ne_two oq
  rw [show (p-1)/2=x by omega,show (q-1)/2=y by omega,hx,hy]
  push_cast
  ring

/-- At every pair of distinct odd primes, the single-draw variance
exceeds the size of the entire sampling population. -/
theorem variance_gt_product {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) : ((p*q:ℕ):ℚ)<variance (p*q) p := by
  let n : ℚ := (p:ℚ)*q
  let k : ℚ := cutoff (p*q)
  let T : ℚ := ((p:ℚ)-1)*((q:ℚ)-1)/2
  have np : 0<n := mul_pos (by exact_mod_cast hp.out.pos) (by exact_mod_cast hq.out.pos)
  have kp : 0<k := by dsimp [k]; exact_mod_cast cutoff_pos order op
  have pp := hp.out.two_le
  have pbig : (3:ℚ)≤p := by exact_mod_cast (show 3≤p by omega)
  obtain ⟨r,pr⟩ := hp.out.odd_of_ne_two op
  obtain ⟨s,qs⟩ := hq.out.odd_of_ne_two oq
  rw [variance,target_size order op oq,Nat.cast_mul]
  change n<n*T/k^2-((p:ℚ)-1)^2
  apply (lt_sub_iff_add_lt).mpr
  apply (lt_div_iff₀ (sq_pos_of_pos kp)).mpr
  by_cases twins : q=p+2
  · have sqrt_eq : (p*q).sqrt=p := by
      apply Nat.le_antisymm
      · apply Nat.le_of_lt_succ
        apply Nat.sqrt_lt'.mpr
        rw [twins]; nlinarith
      · exact Nat.le_sqrt.mpr (Nat.mul_le_mul_left p order.le)
    have eqn : 2*cutoff (p*q)+1=p := by rw [cutoff,sqrt_eq]; omega
    have krel : 2*k+1=(p:ℚ) := by dsimp [k]; exact_mod_cast eqn
    have qrel : (q:ℚ)=p+2 := by exact_mod_cast twins
    have mlt : ((p:ℚ)-1)^2<n := by dsimp [n]; rw [qrel]; nlinarith only [pbig]
    have kt : 2*k^2<T := by dsimp [T]; rw [qrel,←krel]; nlinarith only [kp]
    calc _ < (2*n)*k^2 := mul_lt_mul_of_pos_right (by linarith only [mlt]) (sq_pos_of_pos kp)
         _ < _ := by simpa only [mul_left_comm,mul_assoc,mul_comm] using mul_lt_mul_of_pos_left kt np
  · have gap : (p:ℚ)+4≤q := by exact_mod_cast (show p+4≤q by omega)
    have kshort : 4*k^2≤n-1 := by
      have h : 2*cutoff (p*q)≤(p*q).sqrt := Nat.mul_div_le _ _
      have bound := (Nat.pow_le_pow_left h 2).trans (Nat.sqrt_le' _)
      have b : 4*(cutoff (p*q))^2≤p*q := by nlinarith only [bound]
      obtain ⟨v,nodd⟩ := (hp.out.odd_of_ne_two op).mul (hq.out.odd_of_ne_two oq)
      have strict : 4*(cutoff (p*q))^2+1≤p*q := by omega
      change 4*((cutoff (p*q):ℚ))^2≤(p:ℚ)*q-1
      have cast : 4*((cutoff (p*q):ℚ))^2+1≤(p:ℚ)*q := by exact_mod_cast strict
      linarith
    have prod := mul_le_mul (show (1:ℚ)≤p-2 by linarith)
      (show (2:ℚ)≤q-p-2 by linarith) (by norm_num) (by linarith)
    have low : n-1≤4*T-((p:ℚ)-1)^2 := by dsimp [n,T]; nlinarith only [prod]
    have left := mul_le_mul_of_nonneg_left low np.le
    have right := mul_le_mul_of_nonneg_right kshort (show 0≤n+((p:ℚ)-1)^2 by positivity)
    have strict : 0<((p:ℚ)-1)^2 := sq_pos_of_pos (by linarith only [pbig])
    nlinarith only [left,right,strict]

/-- To achieve root-mean-square error below one for the smaller odd prime,
this estimator requires more independent draws than there are residues. -/
theorem draws_gt_product {p q draws : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q)
    (op : p≠2) (oq : q≠2) (dp : 0<draws)
    (accuracy : Real.sqrt ((meanSquare (estimate (p*q)) p draws:ℚ):ℝ)<1) : p*q<draws := by
  rw [sample_error order op oq dp] at accuracy
  have bound := (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mp accuracy
  have b : ((variance (p*q) p/(draws:ℚ):ℚ):ℝ)<1 := by simpa only [one_pow] using bound
  have err : variance (p*q) p/(draws:ℚ)<1 := by exact_mod_cast b
  have upper := (div_lt_iff₀ (by exact_mod_cast dp : 0<(draws:ℚ))).mp err
  rw [one_mul] at upper
  exact_mod_cast (variance_gt_product order op oq).trans upper

end PrimeFactors.CircleMarkMidcutSampling
