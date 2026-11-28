import PrimeFactors.CyclotomicProductCurve
import PrimeFactors.CyclotomicLogCoefficients
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Truncating the logarithm of a binary inverse cyclotomic reading

For the positive reading `(1−exp(−p/(8B)))(1−exp(−q/(8B)))`, the series
for its negative logarithm has two positive contributions, at multiples of
`p` and of `q`. A cutoff by polynomial degree retains respectively
`⌊K/p⌋` and `⌊K/q⌋` terms. The first omitted term on each branch already
forces an error for the direct truncation. The argument allows the two
omitted contributions to occur at the same degree.
-/

namespace PrimeFactors.CyclotomicLogTail

open Real Finset CyclotomicProductCurve

noncomputable def radius (B d : ℕ) : ℝ := exp (-((d:ℝ)/(8*B)))

/-- Only the multiples `d,2*d,…,d*⌊K/d⌋` occur through degree `K`. -/
noncomputable def branch (B d K : ℕ) : ℝ :=
  ∑ j∈range (K/d), radius B d^(j+1)/((j:ℝ)+1)

/-- Exponentiating the truncated negative logarithm gives a one-sided
approximation to the original positive polynomial reading. -/
noncomputable def approx (B p q K : ℕ) : ℝ := exp (-(branch B p K+branch B q K))

theorem branch_eq_filtered (B K : ℕ) {d : ℕ} (dp : 0<d) :
    branch B d K = ∑ m∈(Icc 1 K).filter (fun m => d∣m),
      (d:ℝ)*exp (-((m:ℝ)/(8*B)))/m := by
  unfold branch
  apply sum_bij (fun j _ => (j+1)*d)
  · intro j hj
    have jr := mem_range.mp hj
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos (by omega) dp,
      (Nat.le_div_iff_mul_le dp).mp jr⟩,dvd_mul_left d (j+1)⟩
  · intro i _ j _ eq
    exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_right dp eq)
  · intro m hm
    obtain ⟨hm,dv⟩ := mem_filter.mp hm
    obtain ⟨mp,mk⟩ := mem_Icc.mp hm
    obtain ⟨n,hn⟩ := dv
    cases n with
    | zero => simp [hn] at mp
    | succ j =>
      refine ⟨j, mem_range.mpr ((Nat.le_div_iff_mul_le dp).mpr ?_),?_⟩
      · simpa only [hn,mul_comm] using mk
      · simp only [hn,mul_comm]
  · intro j _
    rw [radius,←exp_nat_mul]
    push_cast
    rw [show ((j:ℝ)+1)* -((d:ℝ)/(8*B))= -(((j:ℝ)+1)*d/(8*B)) by ring]
    field_simp
    ring

/-- Integrating the actual logarithmic-derivative coefficient at degree m
divides it by m. The ordinary prefix through K retains exactly both branches. -/
theorem dense_prefix {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) (B K : ℕ) :
    (∑ m∈Icc 1 K, ((PowerSeries.coeff ℤ m (CyclotomicLogCoefficients.logSeries (p*q)):ℤ):ℝ)
      *exp (-((m:ℝ)/(8*B)))/m) = branch B p K+branch B q K := by
  rw [branch_eq_filtered B K hp.pos,branch_eq_filtered B K hq.pos,sum_filter,sum_filter,
    ←sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  rw [CyclotomicLogCoefficients.coefficient hp hq ord (mem_Icc.mp hm).1]
  by_cases pm : p∣m <;> by_cases qm : q∣m <;> simp [pm,qm,add_mul,add_div]

theorem log_series {B d : ℕ} (bp : 0<B) (dp : 0<d) :
    HasSum (fun j : ℕ => radius B d^(j+1)/((j:ℝ)+1)) (-log (1-radius B d)) := by
  apply hasSum_pow_div_log_of_abs_lt_one
  rw [radius,abs_of_pos (exp_pos _)]
  apply exp_lt_one_iff.mpr
  exact neg_neg_of_pos (div_pos (by exact_mod_cast dp) (by positivity))

theorem first_omitted {B d : ℕ} (bp : 0<B) (dp : 0<d) (K : ℕ) :
    radius B d^(K/d+1)/((K/d:ℕ)+1:ℝ) ≤ -log (1-radius B d)-branch B d K := by
  have sum := sum_le_hasSum (range (K/d+1)) (fun i _ => by
    dsimp [radius]
    positivity) (log_series bp dp)
  rw [sum_range_succ] at sum
  simpa only [branch,le_sub_iff_add_le,add_comm] using sum

private theorem uniform_term {B d : ℕ} (bp : 0<B) (lo : B≤d) (hi : d≤2*B) (K : ℕ) :
    exp (-(K:ℝ)/(8*B)-1/4)/((K:ℝ)/B+1) ≤ radius B d^(K/d+1)/((K/d:ℕ)+1:ℝ) := by
  have bpos : (0:ℝ)<B := by exact_mod_cast bp
  have dl : (B:ℝ)≤d := by exact_mod_cast lo
  have dh : (d:ℝ)≤2*B := by exact_mod_cast hi
  have i := Nat.div_mul_le_self K d
  have bound : ((K/d:ℕ):ℝ)*d≤K := by exact_mod_cast i
  have idx : ((K/d:ℕ):ℝ)≤(K:ℝ)/B := by
    apply (le_div_iff₀ bpos).mpr
    exact (mul_le_mul_of_nonneg_left dl (Nat.cast_nonneg _)).trans bound
  rw [radius, ←exp_nat_mul]
  apply div_le_div₀ (exp_pos _).le _ (by positivity) (by linarith)
  apply exp_le_exp.mpr
  push_cast
  rw [show (-(K:ℝ)/(8*B)-1/4)=(-(K:ℝ)-2*B)/(8*B) by field_simp; ring]
  rw [show (((K/d:ℕ):ℝ)+1)* -((d:ℝ)/(8*B))=(-(d:ℝ)*((K/d:ℕ):ℝ)-d)/(8*B) by ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [bound]

theorem missing_log {B p q : ℕ} (bp : 0<B) (pl : B≤p) (ph : p≤2*B)
    (ql : B≤q) (qh : q≤2*B) (K : ℕ) :
    2*exp (-(K:ℝ)/(8*B)-1/4)/((K:ℝ)/B+1) ≤
      -log (trial B p q)-(branch B p K+branch B q K) := by
  have hp := (uniform_term bp pl ph K).trans (first_omitted bp (bp.trans_le pl) K)
  have hq := (uniform_term bp ql qh K).trans (first_omitted bp (bp.trans_le ql) K)
  have unitLT (d : ℕ) (pos : 0<d) : radius B d < 1 := by
    apply exp_lt_one_iff.mpr
    exact neg_neg_of_pos (div_pos (by exact_mod_cast pos) (by positivity))
  change _ ≤ -log ((1-radius B p)*(1-radius B q)) - _
  rw [log_mul (sub_pos.mpr (unitLT p (bp.trans_le pl))).ne'
    (sub_pos.mpr (unitLT q (bp.trans_le ql))).ne']
  rw [mul_div_assoc]
  linarith only [hp,hq]

/-- The bound on the discarded logarithm also bounds the absolute reading error,
since the true reading is at least `1/81`. -/
theorem reading_error {B p q : ℕ} (bp : 0<B) (pl : B≤p) (ph : p≤2*B)
    (ql : B≤q) (qh : q≤2*B) (K : ℕ) :
    (1/81:ℝ)*(2*exp (-(K:ℝ)/(8*B)-1/4)/((K:ℝ)/B+1)) ≤ approx B p q K - trial B p q := by
  have bpos : (0:ℝ)<B := by exact_mod_cast bp
  have scale (d : ℕ) (low : B≤d) : (1:ℝ)/8 ≤ (d:ℝ)/(8*B) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have : (B:ℝ)≤d := by exact_mod_cast low
    linarith
  have floor := CyclotomicValueSlope.response_lower (scale p pl) (scale q ql)
  change (1:ℝ)/81 ≤ trial B p q at floor
  have pos : 0<trial B p q := by linarith
  let R := -log (trial B p q)-(branch B p K+branch B q K)
  have bound := missing_log bp pl ph ql qh K
  have ident : trial B p q * exp R = approx B p q K := by
    rw [←exp_log pos, ←exp_add]
    unfold approx
    congr 1
    dsimp [R]
    ring
  calc
    _ ≤ trial B p q * R := mul_le_mul floor bound (by positivity) pos.le
    _ ≤ trial B p q*(exp R-1) := mul_le_mul_of_nonneg_left
      (by linarith only [Real.add_one_le_exp R]) pos.le
    _ = _ := by rw [mul_sub, mul_one, ident]

/-- A direct logarithm-series cutoff at most `4B log B` overshoots the true
reading by at least `1/(432B)`. This exceeds the sufficient decoder tolerance. -/
theorem short_error {B p q K : ℕ} (bp : 0<B) (pl : B≤p) (ph : p≤2*B)
    (ql : B≤q) (qh : q≤2*B) (short : (K:ℝ)≤4*B*log B) :
    1/(432*(B:ℝ)) ≤ approx B p q K-trial B p q := by
  have bpos : (0:ℝ)<B := by exact_mod_cast bp
  have rt := sqrt_pos_of_pos bpos
  have s2 := sq_sqrt bpos.le
  have cutoff : (K:ℝ)/(8*B) ≤ log B/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have first : 1/√(B:ℝ)≤exp (-(K:ℝ)/(8*B)) := by
    rw [one_div, ←exp_log rt, ←exp_neg, exp_le_exp, log_sqrt bpos.le, neg_div]
    exact neg_le_neg cutoff
  have second : (3:ℝ)/4 ≤ exp (-(1:ℝ)/4) := by
    linarith only [Real.add_one_le_exp (-(1:ℝ)/4)]
  have ratio : (K:ℝ)/B ≤ 4*log B := by
    apply (div_le_iff₀ bpos).mpr
    linarith
  have logrt := log_le_sub_one_of_pos rt
  rw [log_sqrt bpos.le] at logrt
  have den : (K:ℝ)/B+1≤8*√(B:ℝ) := by linarith
  have both := mul_le_mul first second (by norm_num) (exp_pos _).le
  calc
    _ = (1/81:ℝ)*(2*((1/√(B:ℝ))*(3/4))/(8*√(B:ℝ))) := by
      field_simp
      nlinarith
    _ ≤ (1/81:ℝ)*(2*exp (-(K:ℝ)/(8*B)-1/4)/((K:ℝ)/B+1)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [sub_eq_add_neg, exp_add]
      exact div_le_div₀ (by positivity) (by linarith only [both]) (by positivity) den
    _ ≤ _ := reading_error bp pl ph ql qh K

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 1100 in
/-- At full factor width the raw cutoff can include even degree `2^1034`
and the actual polynomial reading still lies outside the error budget. -/
theorem full_width {p q K : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q)
    (lo : 2^1023≤p) (hi : q<2^1024) (cutoff : K≤2^1034) :
    1/(8192*(2:ℝ)^1023) <
      approx (2^1023) p q K - reading (p*q) ((2:ℝ)^1023) := by
  let B := (2:ℕ)^1023
  have pos : 0<B := pow_pos (by decide : 0<(2:ℕ)) 1023
  have bpos : (0:ℝ)<B := by exact_mod_cast pos
  have top : q≤2*B := by
    change q≤2*2^1023
    rw [mul_comm, ←pow_succ]
    exact hi.le
  have c : K≤2048*B := cutoff.trans_eq (show (2:ℕ)^1034=2048*2^1023 by decide +kernel)
  have c' : (K:ℝ)≤2048*B := by exact_mod_cast c
  have id : (B:ℝ)=(2:ℝ)^1023 := by
    change ((2^1023:ℕ):ℝ)=(2:ℝ)^1023
    rw [Nat.cast_pow,Nat.cast_ofNat]
  have lb : 2048 ≤ 4*log (B:ℝ) := by
    rw [id,Real.log_pow]
    norm_num1
    linarith only [log_two_gt_d9]
  have short : (K:ℝ)≤4*B*log (B:ℝ) :=
    c'.trans (by nlinarith only [mul_le_mul_of_nonneg_right lb bpos.le])
  rw [actual_value pp qp ordered]
  have result := short_error pos lo (ordered.le.trans top) (lo.trans ordered.le) top short
  rw [←id]
  apply lt_of_lt_of_le _ result
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

end PrimeFactors.CyclotomicLogTail
