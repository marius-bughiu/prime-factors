import PrimeFactors.CircleMarkDigitSampling

/-! Subtract the unmasked Jacobi character, of known complete sum zero.
A uniform draw contributes to the resulting estimate only when the mask
erases a nonzero score. We bound the sample sizes needed to estimate the
sparse digit queries to within half a collision gap in root mean square. -/
namespace PrimeFactors.CircleMarkDigitCenteredSampling

open Finset CircleMarkSharedScores CircleMarkStoppingPrecision CircleMarkMidcutWithoutReplacement
  CircleMarkTargetFrequency CircleMarkDigitSampling
open scoped Classical BigOperators
open private PrimeFactors.CircleMarkDigitSampling.square_error from PrimeFactors.CircleMarkDigitSampling
open private PrimeFactors.CircleMarkSparseMaskProbe.larger_count from PrimeFactors.CircleMarkSparseMaskProbe
open private PrimeFactors.CircleMarkMaskDigitReadout.safe from PrimeFactors.CircleMarkMaskDigitReadout

set_option exponentiation.threshold 8192

/-- Sampled contribution after subtracting the score with an empty mask. -/
noncomputable def centered (n : ℕ) [NeZero n] (C : Finset ℕ) (t : ZMod n) : ℚ :=
  (n:ℚ)*((score n C t:ℚ)-(score n ∅ t:ℚ))

private theorem total_empty {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (op : p≠2) (oq : q≠2) :
    total (p*q) ∅ = 0 := by
  rw [total_local diff op oq]
  simp [covered]

theorem centered_unbiased {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (op : p≠2) (oq : q≠2) (C : Finset ℕ) :
    (𝔼 t, centered (p*q) C t)=total (p*q) C := by
  have eqn (t) : centered (p*q) C t = estimate (p*q) C t - estimate (p*q) ∅ t := by
    simp only [centered,estimate,mul_sub]
  simp only [eqn,expect_sub_distrib,unbiased,total_empty diff op oq,sub_zero]

noncomputable def centeredVariance (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (C : Finset ℕ) : ℚ :=
  ((p*q:ℕ):ℚ)*((live p q ∅:ℚ)-live p q C)-(total (p*q) C)^2

/-- Exact population variance; the second moment counts unit residues erased
by the mask. -/
theorem single {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (op : p≠2) (oq : q≠2) (C : Finset ℕ) :
    (𝔼 t, (centered (p*q) C t-total (p*q) C)^2) = centeredVariance p q C := by
  let n := p*q
  let m := total n C
  have nz : (n:ℚ)≠0 := by exact_mod_cast (NeZero.ne (p*q))
  have expand (a b : ℚ) : (a-b)^2=a^2-2*(a*b)+b^2 := by ring
  have second : (𝔼 t, (centered n C t)^2) = (n:ℚ)*((live p q ∅:ℚ)-live p q C) := by
    simp only [centered,mul_pow,←mul_expect,expand,expect_add_distrib,expect_sub_distrib,
      raw_second diff,←mul_expect,raw_cross diff,union_empty,n]
    change (n:ℚ)^2*((live p q C:ℚ)/n-2*((live p q C:ℚ)/n)+(live p q ∅:ℚ)/n)=_
    field_simp
    dsimp only [n]
    push_cast
    ring
  have full (t : ZMod n) : (centered n C t-m)^2=(centered n C t)^2-2*m*centered n C t+m^2 := by ring
  change (𝔼 t, (centered n C t-m)^2)=(n:ℚ)*((live p q ∅:ℚ)-live p q C)-m^2
  simp only [full,expect_add_distrib,expect_sub_distrib,Fintype.expect_const,←mul_expect,
    centered_unbiased diff op oq,second,m,n]
  ring

private theorem surviving_cost {p q a d : ℕ} (pl : 2^1023≤p) (ql : 2^1023≤q)
    (dp : 0<d) (ad : a≤d) (cap : d≤2^513) :
    ((p*q:ℕ):ℚ)*p*d/2 < ((p*q:ℕ):ℚ)*
      ((((p-1)*(q-1):ℕ):ℚ)-(((p-1-a)*(q-1-d):ℕ):ℚ))-((a*d:ℕ):ℚ)^2 := by
  have room : 2*(2:ℕ)^513+4<2^1023 := by decide +kernel
  have hl : a≤p-1 := by omega
  have hr : d≤q-1 := by omega
  have d3 := (Nat.mul_le_mul (ad.trans cap) (Nat.pow_le_pow_left cap 2)).trans
    ((by decide +kernel : 2^513*((2:ℕ)^513)^2 ≤ 2^1023*2^1023).trans (Nat.mul_le_mul pl ql))
  have product : (a:ℚ)*d^2 ≤ (p:ℚ)*q := by exact_mod_cast d3
  have right : 1 ≤ (q:ℚ)-1-d := by
    have nat : d+2 ≤ q := by omega
    have cast : (d:ℚ)+2 ≤ q := by exact_mod_cast nat
    linarith
  have left : (p:ℚ)/2 < p-1 := by
    have nat : 3≤p := by omega
    have cast : (3:ℚ)≤p := by exact_mod_cast nat
    linarith
  have gap : (a:ℚ)*d^2 ≤ ((p:ℚ)*q)*((q:ℚ)-1-d) :=
    product.trans (by
      have z := mul_le_mul_of_nonneg_left right (mul_nonneg (show 0≤(p:ℚ) from Nat.cast_nonneg p) (Nat.cast_nonneg q))
      simpa only [mul_one] using z)
  have residual := mul_nonneg (Nat.cast_nonneg a) (sub_nonneg.mpr gap)
  have pos : 0<(p:ℚ)*q*d := by
    have P : 0<(p:ℚ) := by exact_mod_cast (by omega : 0<p)
    have Q : 0<(q:ℚ) := by exact_mod_cast (by omega : 0<q)
    positivity
  have bound := mul_lt_mul_of_pos_left left pos
  push_cast [Nat.cast_sub hl,Nat.cast_sub hr,Nat.cast_sub (by omega : 1≤p),Nat.cast_sub (by omega : 1≤q)]
  nlinarith only [bound,residual]

/-- The q-side distinctness condition holds for the positive digit menus. -/
theorem query_injective {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q) (bal : q<2*p)
    (op : p≠2) (oq : q≠2) (J I : Finset ℕ) :
    let C := CircleMarkMaskDigitReadout.coordinates (p*q) J I
    (covered q C).card = C.card := by
  obtain ⟨coords,short⟩ := PrimeFactors.CircleMarkMaskDigitReadout.safe order bal op oq J I
  exact PrimeFactors.CircleMarkSparseMaskProbe.larger_count _ (fun x hx => ⟨(coords x hx).1,(coords x hx).2.trans order⟩) short

theorem centered_lower {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (C : Finset ℕ) (dp : 0<C.card) (cap : C.card≤2^513)
    (distinct : (covered q C).card=C.card) :
    ((p*q:ℕ):ℚ)*p*C.card/2 < centeredVariance p q C := by
  have op : p≠2 := by have := (by decide +kernel : 2<2^1023).trans_le pl; omega
  have oq : q≠2 := by have := (by decide +kernel : 2<2^1023).trans_le ql; omega
  have ad : (covered p C).card≤C.card := (card_le_card (erase_subset ..)).trans card_image_le
  rw [centeredVariance,total_local diff op oq,live,live,distinct]
  simpa only [covered,image_empty,erase_empty,card_empty,Nat.sub_zero] using surviving_cost pl ql dp ad cap


/-- The centered empirical average still needs more than 2Np/d independent
draws for RMS error below d/2. At a 2048-bit product this exceeds 2^2558. -/
theorem independent_budget {p q k : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (C : Finset ℕ) (dp : 0<C.card) (cap : C.card≤2^513)
    (distinct : (covered q C).card=C.card) (kp : 0<k)
    (rms : Real.sqrt ((meanSquare (centered (p*q) C) (total (p*q) C) k:ℚ):ℝ)<(C.card:ℝ)/2) :
    2*(p*q)*p < k*C.card ∧ (2^2047≤p*q → 2^2558<k) := by
  have op : p≠2 := by have := (by decide +kernel : 2<2^1023).trans_le pl; omega
  have oq : q≠2 := by have := (by decide +kernel : 2<2^1023).trans_le ql; omega
  have err := PrimeFactors.CircleMarkDigitSampling.square_error dp rms
  rw [sample_variance _ (centered_unbiased diff op oq C) kp,single diff op oq] at err
  have obs := (div_lt_iff₀ (by exact_mod_cast kp : (0:ℚ)<k)).mp err
  have lower := centered_lower diff pl ql C dp cap distinct
  have work : 2*((p*q:ℕ):ℚ)*p < (k:ℚ)*C.card := by
    have prod : (2*((p*q:ℕ):ℚ)*p)*(C.card:ℚ)<((k:ℚ)*C.card)*C.card := by nlinarith only [obs,lower]
    exact lt_of_mul_lt_mul_right prod (Nat.cast_nonneg _)
  have nat : 2*(p*q)*p<k*C.card := by exact_mod_cast work
  refine ⟨nat,?_⟩
  intro full
  have b : 2^2558*2^513 < k*2^513 := calc
    _ = 2*2^2047*2^1023 := by decide +kernel
    _ ≤ 2*(p*q)*p := Nat.mul_le_mul (Nat.mul_le_mul_left 2 full) pl
    _ < k*C.card := nat
    _ ≤ k*2^513 := Nat.mul_le_mul_left k cap
  exact Nat.lt_of_mul_lt_mul_right b

/-- Sampling distinct residues can leave fewer than qd/2 unexamined when
the centered sample average attains the same RMS threshold. -/
theorem distinct_budget {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (diff : p≠q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (C : Finset ℕ) (dp : 0<C.card) (cap : C.card≤2^513)
    (distinct : (covered q C).card=C.card) (S : Finset (ZMod (p*q))) (sp : 0<S.card)
    (rms : Real.sqrt ((distinctError (centered (p*q) C) (total (p*q) C) S:ℚ):ℝ)<(C.card:ℝ)/2) :
    2*(p*q-S.card)<C.card*q ∧ (q<2^1024 → p*q-S.card<2^1536) := by
  let n : ℚ := (p*q:ℕ)
  let t : ℚ := S.card
  let d : ℚ := C.card
  have op : p≠2 := by have := (by decide +kernel : 2<2^1023).trans_le pl; omega
  have oq : q≠2 := by have := (by decide +kernel : 2<2^1023).trans_le ql; omega
  have N : 1<p*q := hp.out.one_lt.trans_le (Nat.le_mul_of_pos_right p hq.out.pos)
  have Nq : 1<n := by dsimp [n]; exact_mod_cast N
  have tp : 0<t := by dsimp [t]; exact_mod_cast sp
  have lim : S.card≤p*q := S.card_le_univ.trans_eq (ZMod.card _)
  have tn : t≤n := by dsimp [t,n]; exact_mod_cast lim
  have lower : n*p*d/2 < centeredVariance p q C := centered_lower diff pl ql C dp cap distinct
  have err := PrimeFactors.CircleMarkDigitSampling.square_error dp rms
  rw [correction _ (centered_unbiased diff op oq C) S sp (by rwa [ZMod.card]),ZMod.card,
    single diff op oq] at err
  have upper := (div_lt_iff₀ (mul_pos tp (sub_pos.mpr Nq))).mp err
  have low := mul_le_mul_of_nonneg_right lower.le (sub_nonneg.mpr tn)
  have count : t*(n-1)≤n^2 :=
    (mul_le_mul tn (by linarith : n-1≤n) (by linarith) (by linarith)).trans_eq (sq _).symm
  have U := mul_le_mul_of_nonneg_left count (sq_nonneg (d/2))
  change centeredVariance p q C*(n-t)<(d/2)^2*(t*(n-1)) at upper
  have rel : n=(p:ℚ)*q := by simp [n]
  have term : 2*(n-t)*(n*p*d)<d*q*(n*p*d) := by
    rw [show d*q*(n*p*d)=d^2*n^2 by rw [rel]; ring]
    nlinarith only [low,upper,U]
  have pp : 0≤(p:ℚ) := Nat.cast_nonneg _
  have factor : 0≤n*p*d := mul_nonneg (mul_nonneg (by linarith) pp) (Nat.cast_nonneg _)
  have lt := lt_of_mul_lt_mul_right term factor
  have nat : 2*(p*q-S.card)<C.card*q := by
    change 2*(((p*q:ℕ):ℚ)-S.card)<(C.card:ℚ)*q at lt
    rw [←Nat.cast_sub lim] at lt
    exact_mod_cast lt
  refine ⟨nat,?_⟩
  intro hi
  have bound := (Nat.mul_le_mul cap hi.le).trans_eq (by decide +kernel : (2:ℕ)^513*2^1024=2*2^1536)
  omega

end PrimeFactors.CircleMarkDigitCenteredSampling
