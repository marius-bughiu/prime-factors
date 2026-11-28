import PrimeFactors.CyclotomicLogTail

/-! The direct positive logarithm series has a geometric tail once the
cutoff is measured in polynomial degrees. This bound controls truncation
error for exact coefficients and arithmetic. -/
namespace PrimeFactors.CyclotomicLogUpper

open Real Finset CyclotomicLogTail CyclotomicProductCurve

private theorem denominator {B d : ℕ} (bp : 0 < B) (lo : B ≤ d) :
    (1:ℝ)/9 ≤ 1-radius B d := by
  have low : (B:ℝ) ≤ d := by exact_mod_cast lo
  have u : (1:ℝ)/8 ≤ d/(8*(B:ℝ)) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have high : 9/8 ≤ exp (d/(8*(B:ℝ))) := by linarith only [add_one_le_exp (d/(8*(B:ℝ))),u]
  rw [radius,exp_neg]
  have inv : (exp (d/(8*(B:ℝ))))⁻¹ ≤ 8/9 :=
    (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num; exact high)
  linarith

/-- The next omitted multiple of d is strictly beyond the inclusive cutoff K. -/
theorem branch_error {B d : ℕ} (bp : 0 < B) (lo : B ≤ d) (K : ℕ) :
    0 ≤ -log (1-radius B d)-branch B d K ∧
    -log (1-radius B d)-branch B d K < 9*exp (-(K:ℝ)/(8*B)) := by
  let r := radius B d
  have dp := bp.trans_le lo
  have rp : 0 < r := exp_pos _
  have den := denominator bp lo
  change (1:ℝ)/9 ≤ 1-r at den
  have small : |r| < 1 := by rw [abs_of_pos rp]; linarith
  have estimate := abs_log_sub_add_sum_range_le small (K/d)
  rw [abs_of_pos rp] at estimate
  change |branch B d K + log (1-r)| ≤ _ at estimate
  have positive := first_omitted bp dp K
  have pn : 0 ≤ r^(K/d+1)/(((K/d:ℕ):ℝ)+1) := by positivity
  refine ⟨pn.trans positive,?_⟩
  have deg : K < (K/d+1)*d := by simpa [mul_comm] using Nat.lt_mul_div_succ K dp
  have deg' : (K:ℝ) < (((K/d:ℕ):ℝ)+1)*d := by exact_mod_cast deg
  have power : r^(K/d+1) < exp (-(K:ℝ)/(8*B)) := by
    dsimp [r,radius]
    rw [←exp_nat_mul, exp_lt_exp]
    push_cast
    rw [show (((K/d:ℕ):ℝ)+1) * -((d:ℝ)/(8*B)) =
      -((((K/d:ℕ):ℝ)+1)*d)/(8*B) by ring]
    exact div_lt_div_of_pos_right (neg_lt_neg deg') (by positivity)
  have ratio : r^(K/d+1)/(1-r) ≤ 9*r^(K/d+1) := by
    apply (div_le_iff₀ (by linarith only [den] : 0<1-r)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left den (pow_nonneg rp.le (K/d+1))]
  exact lt_of_le_of_lt (by linarith only [(abs_le.mp estimate).1,ratio] :
    -log (1-r)-branch B d K ≤ 9*r^(K/d+1)) (by linarith only [power])

theorem missing_log_upper {B p q : ℕ} (bp : 0 < B) (pl : B ≤ p) (ql : B ≤ q) (K : ℕ) :
    0 ≤ -log (trial B p q)-(branch B p K+branch B q K) ∧
    -log (trial B p q)-(branch B p K+branch B q K) < 18*exp (-(K:ℝ)/(8*B)) := by
  have one := branch_error bp pl K
  have two := branch_error bp ql K
  have dp := denominator bp pl
  have dq := denominator bp ql
  have mulLog : log (trial B p q) = log (1-radius B p)+log (1-radius B q) :=
    log_mul (by linarith only [dp] : 1-radius B p≠0) (by linarith only [dq] : 1-radius B q≠0)
  rw [mulLog]
  constructor <;> linarith only [one.1,one.2,two.1,two.2]

/-- For 0 ≤ partial ≤ full, exponentiating the negative values contracts
their difference. This accounts for conversion from log error to reading error. -/
private theorem exp_contraction {a b : ℝ} (ap : 0 ≤ a) (ab : a ≤ b) :
    0 ≤ exp (-a)-exp (-b) ∧ exp (-a)-exp (-b) ≤ b-a := by
  have small := exp_le_one_iff.mpr (neg_nonpos.mpr ap)
  have r := exp_le_one_iff.mpr (sub_nonpos.mpr ab)
  have prod := mul_le_mul_of_nonneg_right small (sub_nonneg.mpr r)
  have id : exp (-a)*exp (a-b)=exp (-b) := by rw [←exp_add]; congr 1; ring
  rw [mul_sub,mul_one,id,one_mul] at prod
  exact ⟨sub_nonneg.mpr (exp_le_exp.mpr (neg_le_neg ab)),by linarith only [prod,add_one_le_exp (a-b)]⟩

theorem reading_error_upper {B p q : ℕ} (bp : 0 < B) (pl : B ≤ p) (ql : B ≤ q) (K : ℕ) :
    0 ≤ approx B p q K-trial B p q ∧
    approx B p q K-trial B p q < 18*exp (-(K:ℝ)/(8*B)) := by
  have bound := missing_log_upper bp pl ql K
  have nonneg (d : ℕ) : 0 ≤ branch B d K := by
    apply sum_nonneg
    intro i hi
    unfold radius
    positivity
  have tpos : 0 < trial B p q :=
    mul_pos (by linarith only [denominator bp pl] : 0<1-radius B p)
      (by linarith only [denominator bp ql] : 0<1-radius B q)
  have h := exp_contraction (add_nonneg (nonneg p) (nonneg q)) (sub_nonneg.mp bound.1)
  rw [neg_neg,exp_log tpos] at h
  exact ⟨h.1,h.2.trans_lt bound.2⟩

/-- A sufficient cutoff at any width, obtained by solving the geometric
error bound for the single-reading tolerance 1/(8192B). -/
theorem sufficient {B p q K : ℕ} (bp : 0 < B) (pl : B ≤ p) (ql : B ≤ q)
    (cutoff : 8*(B:ℝ)*log (147456*B) ≤ K) :
    |approx B p q K-trial B p q| < 1/(8192*(B:ℝ)) := by
  have bpos : (0:ℝ) < B := by exact_mod_cast bp
  have err := reading_error_upper bp pl ql K
  rw [abs_of_nonneg err.1]
  apply err.2.trans_le
  have large : log (147456*(B:ℝ)) ≤ (K:ℝ)/(8*B) :=
    (le_div_iff₀ (by positivity)).mpr (by linarith only [cutoff])
  have shrink := exp_le_exp.mpr (neg_le_neg large)
  rw [←neg_div, exp_neg (log _), exp_log (by positivity)] at shrink
  calc
    _ ≤ 18*(147456*(B:ℝ))⁻¹ := mul_le_mul_of_nonneg_left shrink (by norm_num)
    _ = _ := by field_simp; ring

private theorem full_scale : 18*(8192*(2:ℝ)^1023) < exp 721 := by
  have scale : (2:ℝ)^1040 = exp (1040*log 2) := by
    rw [←show ((1040:ℕ):ℝ)=1040 by norm_num,exp_nat_mul,exp_log (by norm_num)]
  have size : (1:ℝ)/8 + 1040*log 2 < 721 := by linarith only [log_two_lt_d9]
  have tiny : (9:ℝ)/8 ≤ exp (1/8) := by linarith only [add_one_le_exp ((1:ℝ)/8)]
  calc
    18*(8192*(2:ℝ)^1023) = (9/8)*2^1040 := by ring
    _ ≤ exp (1/8)*exp (1040*log 2) := by
      rw [←scale]
      exact mul_le_mul_of_nonneg_right tiny (by positivity)
    _ < exp 721 := by rw [←exp_add]; exact exp_lt_exp.mpr size

set_option exponentiation.threshold 1100 in
/-- A degree cutoff of 5768B suffices at the full factor width, with the
positive log series evaluated in exact arithmetic. -/
theorem full_width {p q K : ℕ} (hp : p.Prime) (hq : q.Prime) (pq : p<q)
    (low : 2^1023 ≤ p) (cutoff : 5768*2^1023 ≤ K) :
    |approx (2^1023) p q K-reading (p*q) ((2:ℝ)^1023)| < 1/(8192*(2:ℝ)^1023) := by
  let B := (2:ℕ)^1023
  have bp : 0<B := by dsimp [B]; positivity
  have bpos : (0:ℝ)<B := by exact_mod_cast bp
  have id : (B:ℝ)=(2:ℝ)^1023 := by
    dsimp only [B]
    rw [Nat.cast_pow,Nat.cast_ofNat]
  have upper := reading_error_upper bp low (low.trans pq.le) K
  have lower : 5768*(B:ℝ)≤K := by exact_mod_cast cutoff
  have enough : -(K:ℝ)/(8*B) ≤ -721 := (div_le_iff₀ (by positivity)).mpr (by linarith only [lower])
  rw [actual_value hp hq pq,←id,abs_of_nonneg upper.1]
  apply upper.2.trans_le
  calc
    _ ≤ 18*exp (-721) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr enough) (by norm_num)
    _ ≤ 1/(8192*(B:ℝ)) := by
      rw [id, exp_neg, ←div_eq_mul_inv]
      apply (div_le_div_iff₀ (exp_pos _) (by positivity)).mpr
      rw [one_mul]
      exact full_scale.le

end PrimeFactors.CyclotomicLogUpper
