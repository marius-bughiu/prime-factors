import PrimeFactors.CircleMarkDigitQueryValue
import PrimeFactors.CircleMarkSharedScores
import PrimeFactors.CircleMarkMidcutWithoutReplacement

/-! Sampling the raw Jacobi summand in a sparse square-mask query. The sample
estimates the complete sum by multiplying the average score by the population
size. All error bounds refer to that empirical estimator. -/
namespace PrimeFactors.CircleMarkDigitSampling

open Finset CircleMarkJacobiMask CircleMarkTargetFrequency CircleMarkStoppingPrecision
  CircleMarkMidcutWithoutReplacement CircleMarkSharedScores
open scoped BigOperators Classical

set_option exponentiation.threshold 8192

private theorem sparse_local {r a d : ℕ} (lo : 2^1023 ≤ r) (ad : a≤d) (cap : d≤2^513) :
    3*(r:ℚ)/4 < ((r-1-a : ℕ):ℚ) ∧ (a:ℚ) < r/2 := by
  have plenty : 4*((2:ℕ)^513+1)<2^1023 := by decide +kernel
  have room : 4*(a+1)<r := by omega
  have room' : 4*((a:ℚ)+1)<r := by exact_mod_cast room
  rw [Nat.cast_sub (by omega : a≤r-1),Nat.cast_sub (by omega : 1≤r),Nat.cast_one]
  constructor <;> linarith

private theorem variance_arithmetic {p q a b d : ℕ} (pl : 2^1023≤p) (ql : 2^1023≤q)
    (ad : a≤d) (bd : b≤d) (cap : d≤2^513) :
    (((p*q:ℕ):ℚ)^2)/2 <
      ((p*q:ℕ):ℚ)*(((p-1-a)*(q-1-b):ℕ):ℚ) - ((a*b:ℕ):ℚ)^2 := by
  obtain ⟨pa,ap⟩ := sparse_local pl ad cap
  obtain ⟨qb,bq⟩ := sparse_local ql bd cap
  have pp : 0<(p:ℚ) := by exact_mod_cast (by omega : 0<p)
  have qp : 0<(q:ℚ) := by exact_mod_cast (by omega : 0<q)
  have gc := mul_lt_mul_of_pos_right pa (by positivity : (0:ℚ)<3*q/4)
  have gc' := mul_lt_mul_of_pos_left qb ((by positivity : (0:ℚ)<3*p/4).trans pa)
  have high := mul_lt_mul_of_pos_left (gc.trans gc') (mul_pos pp qp)
  have low : (a:ℚ)*b < (p:ℚ)/2*(q:ℚ)/2 := by
    calc _ ≤ ((p:ℚ)/2)*b := mul_le_mul_of_nonneg_right ap.le (Nat.cast_nonneg _)
         _ < ((p:ℚ)/2)*((q:ℚ)/2) := mul_lt_mul_of_pos_left bq (by positivity)
         _ = _ := by ring
  have square := mul_self_lt_mul_self (mul_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)) low
  push_cast
  nlinarith only [high,square]

private theorem square_error {v : ℚ} {d : ℕ} (dp : 0<d)
    (rms : Real.sqrt (v:ℝ)<(d:ℝ)/2) : v<((d:ℚ)/2)^2 := by
  have dpos : (0:ℝ)<(d:ℝ)/2 := by positivity
  apply (Rat.cast_lt (K:=ℝ)).mp
  push_cast
  exact (Real.sqrt_lt' dpos).mp rms

private theorem iid_arithmetic {n d k : ℕ} {v : ℚ} (kp : 0<k)
    (big : (n:ℚ)^2/2<v) (precise : v/k<((d:ℚ)/2)^2) : 2*n^2<k*d^2 := by
  have work := (div_lt_iff₀ (by exact_mod_cast kp : 0<(k:ℚ))).mp precise
  exact_mod_cast (by nlinarith only [big,work] : 2*(n:ℚ)^2 < (k:ℚ)*d^2)

private theorem omitted_arithmetic {n d k : ℕ} {v : ℚ} (bigN : 1<n) (kp : 0<k) (kn : k≤n)
    (big : (n:ℚ)^2/2<v)
    (precise : v*((n:ℚ)-k)/((k:ℚ)*(n-1)) < ((d:ℚ)/2)^2) : 2*(n-k)<d^2 := by
  have N : 1 < (n:ℚ) := by exact_mod_cast bigN
  have K : 0 < (k:ℚ) := by exact_mod_cast kp
  have lim : (k:ℚ) ≤ n := by exact_mod_cast kn
  have obs := (div_lt_iff₀ (mul_pos K (sub_pos.mpr N))).mp precise
  have l := mul_le_mul_of_nonneg_right big.le (sub_nonneg.mpr lim)
  have count : (k:ℚ)*(n-1)≤(n:ℚ)^2 :=
    (mul_le_mul lim (by linarith : (n:ℚ)-1≤n) (by linarith) (by linarith)).trans_eq (sq _).symm
  have u := mul_le_mul_of_nonneg_left count (sq_nonneg ((d:ℚ)/2))
  have h : 2*((n:ℚ)-k)*(n:ℚ)^2 < (d:ℚ)^2*(n:ℚ)^2 := by
    nlinarith only [l,obs,u]
  have out := lt_of_mul_lt_mul_right h (sq_nonneg (n:ℚ))
  rw [←Nat.cast_sub kn] at out
  exact_mod_cast out

private theorem power_budget {N d k w : ℕ} (lo : 2^w≤N) (cap : d≤2^513)
    (work : 2*N^2 < k*d^2) {e : ℕ} (split : e+1026=2*w+1) : 2^e<k := by
  have bound : 2^e*2^1026<k*2^1026 := calc
    _ = 2*(2^w)^2 := by rw [←pow_add,split,pow_succ,←pow_mul,Nat.mul_comm w 2,Nat.mul_comm]
    _ ≤ 2*N^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left lo _)
    _ < _ := work
    _ ≤ _ := Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left cap 2).trans_eq (by decide +kernel))
  exact Nat.lt_of_mul_lt_mul_right bound


/-- Complete sum being estimated. -/
noncomputable def total (n : ℕ) [NeZero n] (C : Finset ℕ) : ℚ := globalSum n (squareMask C)

/-- One uniform residue supplies this unbiased estimate of the complete sum. -/
noncomputable def estimate (n : ℕ) [NeZero n] (C : Finset ℕ) (t : ZMod n) : ℚ :=
  n*(score n C t:ℚ)

theorem raw_mean (n : ℕ) [NeZero n] (C : Finset ℕ) :
    (𝔼 t, (score n C t:ℚ)) = total n C/n := by
  rw [Fintype.expect_eq_sum_div_card,ZMod.card,←Int.cast_sum,sum_score,total]

theorem raw_cross {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (C D : Finset ℕ) :
    (𝔼 t, (score (p*q) C t:ℚ)*(score (p*q) D t:ℚ)) = (live p q (C∪D):ℚ)/(p*q:ℕ) := by
  rw [Fintype.expect_eq_sum_div_card,ZMod.card]
  congr 1
  simp only [←Int.cast_mul,←Int.cast_sum,sum_product diff,Int.cast_natCast]

theorem raw_second {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (C : Finset ℕ) :
    (𝔼 t, (score (p*q) C t:ℚ)^2) = (live p q C:ℚ)/(p*q:ℕ) := by
  simpa only [sq,union_self] using raw_cross diff C C

theorem unbiased (n : ℕ) [NeZero n] (C : Finset ℕ) :
    (𝔼 t, estimate n C t)=total n C := by
  have nz : (n:ℚ)≠0 := by exact_mod_cast NeZero.ne n
  simp only [estimate,←mul_expect,raw_mean]
  field_simp

/-- Population variance of one scaled observation on all N residue classes. -/
noncomputable def variance (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (C : Finset ℕ) : ℚ :=
  ((p*q:ℕ):ℚ)*live p q C-(total (p*q) C)^2

theorem single_variance {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (C : Finset ℕ) :
    (𝔼 t, (estimate (p*q) C t-total (p*q) C)^2)=variance p q C := by
  let n := p*q
  let m := total n C
  have nz : (n:ℚ)≠0 := by exact_mod_cast (NeZero.ne (p*q))
  have second : (𝔼 t, (estimate n C t)^2)=(n:ℚ)*live p q C := by
    change (𝔼 t, ((n:ℚ)*(score n C t:ℚ))^2)=_
    simp only [mul_pow,←mul_expect]
    rw [raw_second diff C]
    change (n:ℚ)^2*((live p q C:ℚ)/n)=(n:ℚ)*live p q C
    field_simp
    ring
  have expand (t : ZMod n) : (estimate n C t-m)^2=(estimate n C t)^2-2*m*estimate n C t+m^2 := by ring
  change (𝔼 t, (estimate n C t-m)^2)=(n:ℚ)*live p q C-m^2
  simp only [expand,expect_add_distrib,expect_sub_distrib,Fintype.expect_const,←mul_expect,unbiased,second,m]
  ring

theorem total_local {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (op : p≠2) (oq : q≠2)
    (C : Finset ℕ) : total (p*q) C = (((covered p C).card*(covered q C).card:ℕ):ℚ) := by
  rw [total,factorization diff,square_sum p op,square_sum q oq,neg_mul_neg]
  push_cast
  rfl

/-- For a sparse mask the variance of the scaled draw exceeds N²/2, or
equivalently the variance of the unscaled Jacobi score exceeds one half. -/
theorem variance_lower {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (C : Finset ℕ) (cap : C.card≤2^513) :
    ((p*q:ℕ):ℚ)^2/2 < variance p q C := by
  have op : p≠2 := by have := (by decide +kernel : 2<2^1023).trans_le pl; omega
  have oq : q≠2 := by have := (by decide +kernel : 2<2^1023).trans_le ql; omega
  have size (r : ℕ) : (covered r C).card≤C.card := (card_le_card (erase_subset ..)).trans card_image_le
  rw [variance,total_local diff op oq,live]
  exact variance_arithmetic pl ql (size p) (size q) cap

/-- Exact finite-IID mean squared error and its without-replacement counterpart. -/
theorem iid_error {p q k : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (C : Finset ℕ) (kp : 0<k) :
    meanSquare (estimate (p*q) C) (total (p*q) C) k = variance p q C/k := by
  rw [sample_variance _ (unbiased ..) kp,single_variance diff]

theorem distinct_error {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (diff : p≠q) (C : Finset ℕ)
    (S : Finset (ZMod (p*q))) (sp : 0<S.card) :
    distinctError (estimate (p*q) C) (total (p*q) C) S =
      variance p q C * (((p*q:ℕ):ℚ)-S.card)/((S.card:ℚ)*(((p*q:ℕ):ℚ)-1)) := by
  have big : 1<p*q := hp.out.one_lt.trans_le (Nat.le_mul_of_pos_right _ hq.out.pos)
  rw [correction _ (unbiased ..) S sp (by rwa [ZMod.card]),single_variance diff,ZMod.card]

/-- RMS precision below half the one-collision gap requires T·d² > 2N².
Two 1024-bit prime factors give the first power bound; the stronger exponent
uses the additional assumption that the product has 2048 bits. -/
theorem independent_budget {p q k : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (C : Finset ℕ) (dp : 0<C.card) (cap : C.card≤2^513) (kp : 0<k)
    (rms : Real.sqrt ((meanSquare (estimate (p*q) C) (total (p*q) C) k:ℚ):ℝ)<(C.card:ℝ)/2) :
    2*(p*q)^2 < k*C.card^2 ∧ 2^3067<k ∧ (2^2047≤p*q → 2^3069<k) := by
  have err := square_error dp rms
  rw [iid_error diff C kp] at err
  have work := iid_arithmetic kp (variance_lower diff pl ql C cap) err
  have lo : 2^2046≤p*q := (by decide +kernel : 2^2046=(2:ℕ)^1023*2^1023) ▸ Nat.mul_le_mul pl ql
  exact ⟨work,power_budget lo cap work (by decide),fun full => power_budget full cap work (by decide)⟩

/-- With uniform sampling without replacement, half-gap RMS accuracy leaves
fewer than d²/2 residues unexamined. -/
theorem distinct_budget {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (diff : p≠q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (C : Finset ℕ) (dp : 0<C.card) (cap : C.card≤2^513)
    (S : Finset (ZMod (p*q))) (sp : 0<S.card)
    (rms : Real.sqrt ((distinctError (estimate (p*q) C) (total (p*q) C) S:ℚ):ℝ)<(C.card:ℝ)/2) :
    2*(p*q-S.card)<C.card^2 ∧ p*q-S.card<2^1025 := by
  have err := square_error dp rms
  rw [distinct_error diff C S sp] at err
  have big := hp.out.one_lt.trans_le (Nat.le_mul_of_pos_right p hq.out.pos)
  have size : S.card≤p*q := S.card_le_univ.trans_eq (ZMod.card _)
  have few := omitted_arithmetic big sp size (variance_lower diff pl ql C cap) err
  have two := (Nat.pow_le_pow_left cap 2).trans_eq (by decide +kernel : ((2:ℕ)^513)^2=2*2^1025)
  exact ⟨few,by omega⟩

end PrimeFactors.CircleMarkDigitSampling
