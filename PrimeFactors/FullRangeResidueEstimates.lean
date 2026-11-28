import PrimeFactors.UnconditionalPrimePairSumFrequency

/-! Uniform prime-count estimates for every suffix of the 1,024-bit range, at
modulus 25. The analytic inputs are Ernvall-Hytönen and Palojärvi, Corollary 2
(https://arxiv.org/pdf/2003.01925#page=2) under Dirichlet GRH, or the
unconditional Bennett–Martin–O'Bryant–Rechnitzer, Theorem 1.3
(https://personal.math.ubc.ca/~gerg/papers/downloads/EBPAP.pdf#page=5).
Each theorem takes the stated pointwise estimate as an explicit hypothesis. -/

namespace PrimeFactors.FullRangeResidueEstimates

open Real MeasureTheory WideResiduePrimeSupply
open private PrimeFactors.WideResiduePrimeSupply.count_add from PrimeFactors.WideResiduePrimeSupply
open private PrimeFactors.UnconditionalPrimePairSumFrequency.endpoint_cap from
  PrimeFactors.UnconditionalPrimePairSumFrequency

set_option exponentiation.threshold 4096

abbrev X : ℕ := 2^1023
abbrev U : ℕ := B/27000
abbrev M : ℕ := B/58000
abbrev ehpD : ℕ := 52800*2^512
abbrev bmorD : ℕ := 4*B/(840*700^2)
abbrev ehpF : ℕ := 2^478
abbrev bmorF : ℕ := 412

/-- The primes congruent to x in (z,B]. -/
noncomputable def tail (x : ZMod 25) (z : ℕ) : Finset ℕ :=
  ResiduePairMultiplicity.primes 25 (z+1) (B+1) x.val

theorem mem_tail {x : ZMod 25} {z p : ℕ} : p∈tail x z ↔
    z<p ∧ p≤B ∧ p.Prime ∧ p%25=x.val := by
  simp only [tail,ResiduePairMultiplicity.mem_primes,Nat.lt_succ_iff,Nat.succ_le_iff]

/-- Inequalities for all unit classes. The constants are natural numbers. -/
structure Estimates (D upperCap lowerCap : ℕ) : Prop where
  suffix (a b : ZMod 25) (ua : IsUnit a) (ub : IsUnit b) (z : ℕ) (lo : X≤z) (hi : z≤B) :
    (tail a z).card ≤ (tail b z).card+D
  upper (a : ZMod 25) (ua : IsUnit a) : (tail a X).card ≤ upperCap
  lower (a : ZMod 25) (ua : IsUnit a) : lowerCap ≤ (tail a L).card

/-- The common logarithmic integral is normalized as in the chosen paper.
Its difference across each suffix is the ordinary integral of 1/log. -/
structure EndpointEstimates (error li : ℕ → ℝ) : Prop where
  integral (z : ℕ) (lo : X≤z) (hi : z≤B) : li B = li z + increment z (B-z)
  pointwise (a : ZMod 25) (ua : IsUnit a) (z : ℕ) (lo : X≤z) (hi : z≤B) :
    |((through 25 a.val z).card:ℝ) - li z/20| ≤ error z

/-- All integer endpoints used satisfy the published size thresholds at modulus 25. -/
theorem source_domain {z : ℕ} (lo : X≤z) : 25≤z ∧ 8000000000≤z ∧ 25≤(10000:ℕ) :=
  ⟨(by decide : 25≤X).trans lo,(by decide : 8000000000≤X).trans lo,by decide⟩

private theorem tail_add (a : ZMod 25) {z : ℕ} (hi : z≤B) :
    (tail a z).card+(through 25 a.val z).card=(through 25 a.val B).card := by
  have add := Nat.add_sub_of_le hi
  have same : tail a z = inBand 25 a.val z (B-z) := by
    ext p
    rw [mem_tail,mem_band,add]
    tauto
  rw [same,PrimeFactors.WideResiduePrimeSupply.count_add,add]

private theorem upper_integral :
    increment X (B-X) ≤ ((B-X:ℕ):ℝ)/700 := by
  have ord : (X:ℝ)≤((X+(B-X):ℕ):ℝ) := by exact_mod_cast Nat.le_add_right X (B-X)
  have logX : (700:ℝ)≤log (X:ℝ) := by
    simp only [X,Nat.cast_pow,Nat.cast_ofNat,log_pow]
    linarith only [log_two_gt_d9]
  have pos : (0:ℝ)<X := by norm_num [X]
  have cont : ContinuousOn (fun x : ℝ => 1/log x) (Set.Icc (X:ℝ) ((X+(B-X):ℕ):ℝ)) := by
    apply continuousOn_const.div
    · exact continuousOn_log.mono (fun x hx => (pos.trans_le hx.1).ne')
    · intro x hx
      exact (lt_of_lt_of_le (by norm_num : (0:ℝ)<700) (logX.trans (log_le_log pos hx.1))).ne'
  have bound := intervalIntegral.integral_mono_on (μ:=volume) (f:=fun x : ℝ => 1/log x)
    (g:=fun _ : ℝ => (1:ℝ)/700) ord (cont.intervalIntegrable_of_Icc ord) intervalIntegrable_const
    (fun x hx => one_div_le_one_div_of_le (by norm_num) (logX.trans (log_le_log pos hx.1)))
  rw [intervalIntegral.integral_const,smul_eq_mul] at bound
  simpa only [increment,Nat.cast_add,add_sub_cancel_left,div_eq_mul_inv,one_mul] using bound

private theorem center {error li : ℕ → ℝ} {e : ℝ} (h : EndpointEstimates error li)
    (cap : ∀ z, X≤z → z≤B → error z≤e) (a : ZMod 25) (ua : IsUnit a)
    {z : ℕ} (lo : X≤z) (hi : z≤B) :
    |((tail a z).card:ℝ) - increment z (B-z)/20| ≤ 2*e := by
  have atB : X≤B := by decide
  have left := abs_le.mp ((h.pointwise a ua z lo hi).trans (cap z lo hi))
  have right := abs_le.mp ((h.pointwise a ua B atB le_rfl).trans (cap B atB le_rfl))
  rw [h.integral z lo hi,add_div] at right
  have add : ((tail a z).card:ℝ)+(through 25 a.val z).card=(through 25 a.val B).card := by
    exact_mod_cast tail_add a hi
  have combine {a b d c t e : ℝ} (hl : -e≤a-c ∧ a-c≤e)
      (hr : -e≤b-(c+t) ∧ b-(c+t)≤e) (eq : d+a=b) : |d-t|≤2*e := by
    rw [abs_le]
    constructor <;> linarith
  exact combine left right add

private theorem of_error {D : ℕ} {e : ℝ} {error li : ℕ → ℝ} (h : EndpointEstimates error li)
    (cap : ∀ z, X≤z → z≤B → error z≤e)
    (disc : 4*e < (D:ℝ)+1) (top : ((B-X:ℕ):ℝ)/700/20+2*e ≤ U)
    (bottom : (M:ℝ) ≤ ((B-L:ℕ):ℝ)/710/20-2*e) : Estimates D U M := by
  refine ⟨?_,?_,?_⟩
  · intro a b ua ub z lo hi
    have right := (abs_le.mp (center h cap a ua lo hi)).2
    have left := (abs_le.mp (center h cap b ub lo hi)).1
    have strict : ((tail a z).card:ℝ)<(tail b z).card+D+1 := by linarith only [disc,right,left]
    exact Nat.le_of_lt_succ (by exact_mod_cast strict)
  · intro a ua
    have right := (abs_le.mp (center h cap a ua (z:=X) le_rfl (by decide))).2
    have combine {v t w e u : ℝ} (integral : t≤w) (bound : v-t/20≤2*e)
        (margin : w/20+2*e≤u) : v≤u := by linarith
    exact_mod_cast combine upper_integral right top
  · intro a ua
    have left := (abs_le.mp (center h cap a ua (z:=L) (by decide) (by decide))).1
    have low := increment_lower (A:=L) (W:=B-L) (by decide) (by decide)
    have combine {v t w e m : ℝ} (integral : w≤t) (bound : -(2*e)≤v-t/20)
        (margin : m≤w/20-2*e) : m≤v := by linarith
    exact_mod_cast combine low left bottom

noncomputable abbrev ehpError25 (z : ℕ) : ℝ := ehpError 25 z
noncomputable abbrev bmorError25 (z : ℕ) : ℝ := (z:ℝ)/(840*(log z)^2)

/-- Bounds from EHP Corollary 2 applied throughout the range. -/
theorem ehp {li : ℕ → ℝ} (h : EndpointEstimates ehpError25 li) : Estimates ehpD U M := by
  apply of_error (e:=13200*(2:ℝ)^512) h
  · intro z lo hi
    exact error_cap (by decide) (by decide) (by exact_mod_cast lo) (by exact_mod_cast hi)
  all_goals norm_num [B,X,L,U,M,ehpD]

/-- Bounds from the unconditional BMOR Theorem 1.3 throughout the range. -/
theorem bmor {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) : Estimates bmorD U M := by
  apply of_error (e:=(B:ℝ)/(840*700^2)) h
  · intro z lo hi
    exact (PrimeFactors.UnconditionalPrimePairSumFrequency.endpoint_cap lo).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hi) (by norm_num))
  all_goals norm_num [B,X,L,U,M,bmorD]

theorem two_le_M : 2≤M := by decide +kernel

/-- Integer constants ready for a two-dimensional counting argument. -/
theorem ehp_precision : ehpF*(2*ehpD*U+U) ≤ M*(M-1) := by decide +kernel

theorem bmor_precision : bmorF*(2*bmorD*U+U) ≤ M*(M-1) := by decide +kernel

end PrimeFactors.FullRangeResidueEstimates
