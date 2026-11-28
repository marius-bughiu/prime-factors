import PrimeFactors.CircleMarkUnsignedVariance
import PrimeFactors.CircleMarkMidcutWithoutReplacement

/-! Exact sampling costs for estimating the prime sum by averaging the
unsigned changed-score indicator over uniform residues. -/

namespace PrimeFactors.CircleMarkUnsignedSampling

open Finset CircleMarkSharedOccurrence CircleMarkChangedPrimeSum CircleMarkUnsignedVariance
  CircleMarkStoppingPrecision CircleMarkMidcutWithoutReplacement
open scoped Classical BigOperators

/-- The unsigned change observed at a single residue. -/
noncomputable def flag (n : ℕ) [NeZero n] (d : ℕ) (t : ZMod n) : ℚ :=
  if t ∈ changed n {Icc 1 d} then 1 else 0

theorem flag_eq (n : ℕ) [NeZero n] (d : ℕ) (t : ZMod n) :
    flag n d t = if CircleMarkSharedScores.score n (Icc 1 d) t ≠ jacobiSym t.val n then 1 else 0 := by
  simp [flag,changed]

/-- The affine rescaling that estimates the prime sum from a prefix observation. -/
noncomputable def estimate (n : ℕ) [NeZero n] (d : ℕ) (t : ZMod n) : ℚ :=
  ((n : ℚ)/d) * flag n d t + d + 2

private noncomputable def target (n : ℕ) [NeZero n] (d : ℕ) : ℚ :=
  (tally n d : ℚ)/d + d + 2

theorem flag_mean (n : ℕ) [NeZero n] (d : ℕ) :
    (𝔼 t, flag n d t) = (tally n d : ℚ)/n := by
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  simp [flag,tally,sum_boole]

private theorem mean (n : ℕ) [NeZero n] {d : ℕ} (pos : 0 < d) :
    (𝔼 t, estimate n d t) = target n d := by
  have nn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have dn : (d : ℚ) ≠ 0 := by exact_mod_cast pos.ne'
  simp only [estimate,expect_add_distrib,←mul_expect,Fintype.expect_const,flag_mean,target]
  field_simp
  ring

private theorem centered (n : ℕ) [NeZero n] {d : ℕ} (pos : 0 < d) :
    (𝔼 t, (estimate n d t - target n d)^2) = variance n d := by
  let h : ℚ := tally n d
  have nn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have dn : (d : ℚ) ≠ 0 := by exact_mod_cast pos.ne'
  have expand (t : ZMod n) : (estimate n d t - target n d)^2 =
      flag n d t * (((n : ℚ)^2-2*n*h)/d^2) + h^2/d^2 := by
    simp only [estimate,target,flag,h]
    split <;> field_simp <;> ring
  simp only [expand,expect_add_distrib,←expect_mul,Fintype.expect_const,flag_mean,variance,h]
  field_simp
  ring

private theorem target_eq {p q d : ℕ} [hp : Fact p.Prime] [Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (pos : 0 < d) (cap : d ≤ (p-1)/2) :
    target (p*q) d = (p : ℚ)+q := by
  have room : 2+d ≤ p+q := by have := hp.out.two_le; omega
  have dn : (d:ℚ) ≠ 0 := by exact_mod_cast pos.ne'
  rw [target,tally_eq order op oq cap,show p+q-2-d=p+q-(2+d) by omega]
  push_cast [Nat.cast_sub room]
  field_simp
  ring

theorem unbiased {p q d : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (pos : 0 < d) (cap : d ≤ (p-1)/2) :
    (𝔼 t, estimate (p*q) d t) = (p : ℚ)+q :=
  (mean (p*q) pos).trans (target_eq order op oq pos cap)

theorem one_draw {p q d : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (pos : 0 < d) (cap : d ≤ (p-1)/2) :
    (𝔼 t, (estimate (p*q) d t - ((p : ℚ)+q))^2) = variance (p*q) d := by
  rw [←target_eq order op oq pos cap, centered _ pos]

/-- Exact mean squared error for the uniform sample mean with replacement. -/
theorem iid_error {p q d k : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (pos : 0 < d) (cap : d ≤ (p-1)/2) (kp : 0 < k) :
    meanSquare (estimate (p*q) d) ((p : ℚ)+q) k = variance (p*q) d/k := by
  rw [sample_variance _ (unbiased order op oq pos cap) kp, one_draw order op oq pos cap]

/-- Exact mean squared error for uniformly sampling a fixed number of distinct residues. -/
theorem distinct_error {p q d : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (pos : 0 < d) (cap : d ≤ (p-1)/2)
    (S : Finset (ZMod (p*q))) (sp : 0 < S.card) :
    distinctError (estimate (p*q) d) ((p : ℚ)+q) S =
      variance (p*q) d * (((p*q : ℕ) : ℚ)-S.card) / ((S.card : ℚ)*(((p*q : ℕ) : ℚ)-1)) := by
  have big := hp.out.one_lt.trans_le (Nat.le_mul_of_pos_right p hq.out.pos)
  rw [correction _ (unbiased order op oq pos cap) S sp (by rwa [ZMod.card]),
    ZMod.card, one_draw order op oq pos cap]

private theorem mse {x : ℚ} (rms : Real.sqrt (x:ℝ) < 1) : x < 1 := by
  have h := (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mp rms
  exact_mod_cast (by simpa using h : (x:ℝ)<1)

/-- For the product-only prefix, prime-sum RMS below one needs strictly
more than 15N/8 independent uniform residues. -/
theorem independent_budget {p q k : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p < q)
    (bal : q < 2*p) (op : p ≠ 2) (oq : q ≠ 2) (kp : 0 < k)
    (rms : Real.sqrt (meanSquare (estimate (p*q) (publicLength (p*q))) ((p:ℚ)+q) k : ℝ) < 1) :
    15*(p*q) < 8*k := by
  obtain ⟨pos,cap⟩ := public_safe order bal op
  have err := mse rms
  rw [iid_error order op oq pos cap kp] at err
  have K : (0:ℚ)<k := by exact_mod_cast kp
  have exactBound := (div_lt_one K).mp err
  have low := public_lower order bal op oq
  exact_mod_cast (by linarith only [low,exactBound] : 15*((p*q : ℕ) : ℚ) < 8*(k:ℚ))

/-- Without replacement, the same accuracy needs T(23N−8)>15N², and
in particular strictly more than 15N/23 distinct uniform residues. -/
theorem distinct_budget {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (order : p < q)
    (bal : q < 2*p) (op : p ≠ 2) (oq : q ≠ 2) (S : Finset (ZMod (p*q))) (sp : 0 < S.card)
    (rms : Real.sqrt (distinctError (estimate (p*q) (publicLength (p*q))) ((p:ℚ)+q) S : ℝ) < 1) :
    15*(p*q)^2 < S.card*(23*(p*q)-8) ∧ 15*(p*q) < 23*S.card := by
  obtain ⟨pos,cap⟩ := public_safe order bal op
  have err := mse rms
  rw [distinct_error order op oq pos cap S sp] at err
  let n : ℚ := (p*q : ℕ)
  let k : ℚ := S.card
  have big := hp.out.one_lt.trans_le (Nat.le_mul_of_pos_right p hq.out.pos)
  have N : 1 < n := by dsimp only [n]; exact_mod_cast big
  have K : 0 < k := by dsimp only [k]; exact_mod_cast sp
  have lim : k ≤ n := by
    dsimp only [k,n]
    exact_mod_cast (S.card_le_univ.trans_eq (ZMod.card _))
  have exactBound := (div_lt_one (mul_pos K (sub_pos.mpr N))).mp err
  have low : 15*n/8 < variance (p*q) (publicLength (p*q)) := public_lower order bal op oq
  have lower := mul_le_mul_of_nonneg_right low.le (sub_nonneg.mpr lim)
  have sharp : 15*n^2 < k*(23*n-8) := by nlinarith only [lower,exactBound]
  have simpler : (15*n)*n < (23*k)*n := by nlinarith only [sharp,K]
  have reduced := lt_of_mul_lt_mul_right simpler (by linarith only [N])
  have natRoom : 8 ≤ 23*(p*q) := by omega
  dsimp only [k,n] at sharp reduced
  constructor
  · exact_mod_cast (by simpa only [Nat.cast_sub natRoom,Nat.cast_mul,Nat.cast_ofNat] using sharp :
      15*((p*q : ℕ) : ℚ)^2 < (S.card : ℚ)*((23*(p*q)-8 : ℕ) : ℚ))
  · exact_mod_cast reduced

/-- With N=2183 and public length 16, the exact sample-size thresholds
for prime-sum mean squared error below one use 4559 independent draws or
1477 distinct draws. -/
theorem example_2183 :
    publicLength 2183 = 16 ∧ variance 2183 16 = 36465/8 ∧
    (∀ k : ℕ, 0 < k → (meanSquare (estimate 2183 16) 96 k < 1 ↔ 4559 ≤ k)) ∧
    (∀ S : Finset (ZMod 2183), 0 < S.card →
      (distinctError (estimate 2183 16) 96 S < 1 ↔ 1477 ≤ S.card)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 59) := ⟨by decide⟩
  have count := tally_eq (p:=37) (q:=59) (d:=16) (by decide) (by decide) (by decide) (by decide)
  norm_num at count
  have V : variance 2183 16 = 36465/8 := by rw [variance,count]; norm_num
  refine ⟨by norm_num [publicLength], V, ?_, ?_⟩
  · intro k kp
    have K : (0:ℚ)<k := by exact_mod_cast kp
    have err := iid_error (p:=37) (q:=59) (d:=16) (by decide) (by decide) (by decide)
      (by decide) (by decide) kp
    norm_num at err
    rw [err,V,div_lt_one K]
    constructor
    · intro h
      have a : (4558:ℚ)<k := by linarith only [h]
      exact_mod_cast a
    · intro h
      have a : (4559:ℚ)≤k := by exact_mod_cast h
      linarith only [a]
  · intro S sp
    have K : (0:ℚ)<S.card := by exact_mod_cast sp
    have err := distinct_error (p:=37) (q:=59) (d:=16) (by decide) (by decide) (by decide)
      (by decide) (by decide) S sp
    norm_num at err
    have den : 0 < (S.card:ℚ)*2182 := mul_pos K (by norm_num)
    rw [err,V,div_lt_one den]
    constructor
    · intro h
      have a : (1476:ℚ)<S.card := by linarith only [h]
      exact_mod_cast a
    · intro h
      have a : (1477:ℚ)≤S.card := by exact_mod_cast h
      linarith only [a]

end PrimeFactors.CircleMarkUnsignedSampling
