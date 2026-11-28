import PrimeFactors.PublicCyclotomicLogReading
import PrimeFactors.FiniteBinCollisionPopulation

/-! A scalar added to the truncated logarithm must be shared by every
product of the same word size and cutoff. The pairs may share their
larger prime. Dependence of the correction on the full product is outside
this statement. -/
namespace PrimeFactors.CyclotomicCommonTailCorrection

open Finset Real CyclotomicLogTail CyclotomicProductCurve MixedPrefixSample

noncomputable def remainder (B d K : ℕ) : ℝ := -log (1-radius B d)-branch B d K

noncomputable def corrected (B p q K : ℕ) (c : ℝ) : ℝ :=
  exp (-(branch B p K+branch B q K)-c)

private noncomputable def termAt (B d j : ℕ) : ℝ :=
  radius B d^(j+1)/((j:ℝ)+1)

private theorem tail_series {B d : ℕ} (bp : 0<B) (dp : 0<d) (K : ℕ) :
    HasSum (fun n : ℕ => termAt B d (n+K/d)) (remainder B d K) :=
  (hasSum_nat_add_iff' (K/d)).mpr (log_series bp dp)

private theorem exp_difference (u v : ℝ) : exp v*(u-v) ≤ exp u-exp v := by
  have m := mul_le_mul_of_nonneg_left (add_one_le_exp (u-v)) (exp_pos v).le
  rw [←exp_add, show v+(u-v)=u by ring] at m
  linarith

/-- On one quotient class the difference is at least the difference at the
first omitted coefficient. All later terms have the same sign. -/
theorem separation {B d e K : ℕ} (bp : 0<B) (dp : 0<d) (ord : d≤e) (top : e≤2*B)
    (same : K/d=K/e) :
    ((e:ℝ)-d)/(8*B)*exp (-(((K:ℝ)+2*B)/(8*B))) ≤ remainder B d K-remainder B e K := by
  let j := K/e
  let D := 8*(B:ℝ)
  have Dpos : 0<D := by dsimp only [D]; positivity
  have de : (d:ℝ)≤e := by exact_mod_cast ord
  have b2 : (e:ℝ)≤2*B := by exact_mod_cast top
  have jd : K/d=j := same
  have a : HasSum (fun n : ℕ => termAt B d (n+j)) (remainder B d K) := by
    simpa only [jd] using tail_series bp dp K
  have b := tail_series bp (dp.trans_le ord) K
  change HasSum (fun n : ℕ => termAt B e (n+j)) (remainder B e K) at b
  have base : radius B e≤radius B d := by
    apply exp_le_exp.mpr
    exact neg_le_neg (div_le_div_of_nonneg_right de Dpos.le)
  have cmp (i : ℕ) : termAt B e i≤termAt B d i := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (exp_pos _).le base _
  have first := le_hasSum (a.sub b) 0 (by intro i _; exact sub_nonneg.mpr (cmp _))
  simp only [Pi.sub_apply,zero_add] at first
  apply le_trans _ first
  let t : ℝ := (j:ℝ)+1
  have tp : 0<t := by dsimp only [t]; positivity
  have ind : (j:ℝ)*e ≤ K := by exact_mod_cast Nat.div_mul_le_self K e
  have xx : (-( ((K:ℝ)+2*B)/D)) ≤ -(t*e/D) := by
    apply neg_le_neg
    apply div_le_div_of_nonneg_right _ Dpos.le
    dsimp only [t]; nlinarith only [ind,b2]
  have epow (f : ℕ) : termAt B f j=exp (-(t*f/D))/t := by
    unfold termAt radius
    rw [←exp_nat_mul]
    push_cast
    dsimp only [t,D]
    ring_nf
  rw [epow,epow,←sub_div]
  apply (le_div_iff₀ tp).mpr
  change ((e:ℝ)-d)/D*exp (-((K+2*(B:ℝ))/D))*t ≤ _
  calc
    _ ≤ ((e:ℝ)-d)/D*exp (-(t*e/D))*t := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (exp_le_exp.mpr xx)
        (div_nonneg (sub_nonneg.mpr de) Dpos.le)) tp.le
    _ = exp (-(t*e/D))*(-(t*d/D)- -(t*e/D)) := by ring
    _ ≤ _ := exp_difference _ _

/-- Accuracy of the corrected positive reading bounds the size of its
logarithmic discrepancy to within 162 times the reading error. -/
private theorem log_close {a b ε : ℝ} (min : 1/81≤b) (small : ε≤1/162)
    (fit : |a-b|≤ε) : |log a-log b|≤162*ε := by
  obtain ⟨left,right⟩ := abs_le.mp fit
  have ep : 0≤ε := (abs_nonneg _).trans fit
  have alo : 1/162≤a := by linarith
  have blo : 1/162≤b := by linarith
  have once {v w : ℝ} (vp : 0<v) (wl : 1/162≤w) (close : v-w≤ε) :
      log v-log w≤162*ε := by
    have wp : 0<w := by linarith
    rw [←log_div vp.ne' wp.ne']
    apply (log_le_sub_one_of_pos (div_pos vp wp)).trans
    have id : v/w-1=(v-w)/w := by field_simp
    rw [id]
    apply (div_le_iff₀ wp).mpr
    nlinarith only [close,mul_le_mul_of_nonneg_right wl ep]
  exact abs_le.mpr ⟨by linarith only [once (by linarith : 0<b) alo (by linarith : b-a≤ε)],
    once (by linarith) blo right⟩

private theorem log_corrected {B p q K : ℕ} (bp : 0<B) (pl : B≤p) (ql : B≤q) (c : ℝ) :
    log (corrected B p q K c)-log (trial B p q) = remainder B p K+remainder B q K-c := by
  have small (d : ℕ) (pos : 0<d) : radius B d<1 :=
    exp_lt_one_iff.mpr (neg_neg_of_pos (div_pos (by exact_mod_cast pos) (by positivity)))
  rw [corrected,log_exp]
  change _-log ((1-radius B p)*(1-radius B q))=_
  rw [log_mul (sub_pos.mpr (small _ (bp.trans_le pl))).ne'
    (sub_pos.mpr (small _ (bp.trans_le ql))).ne']
  dsimp only [remainder]
  ring

private theorem fits {B p q K : ℕ} (bp : 0<B) (pl : B≤p) (ql : B≤q) {c ε : ℝ}
    (small : ε≤1/162) (fit : |corrected B p q K c-trial B p q|≤ε) :
    |remainder B p K+remainder B q K-c|≤162*ε := by
  have scale (d : ℕ) (low : B≤d) : (1:ℝ)/8≤d/(8*(B:ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have : (B:ℝ)≤d := by exact_mod_cast low
    linarith only [this]
  rw [←log_corrected bp pl ql]
  exact log_close (CyclotomicValueSlope.response_lower (scale p pl) (scale q ql)) small fit

theorem incompatible {B d e q K : ℕ} (bp : 0<B) (dp : B≤d) (de : d≤e) (top : e≤2*B)
    (ql : B≤q) (same : K/d=K/e) {ε : ℝ} (small : ε≤1/162)
    (apart : 324*ε < ((e:ℝ)-d)/(8*B)*exp (-(((K:ℝ)+2*B)/(8*B)))) (c : ℝ) :
    ε < |corrected B d q K c-trial B d q| ∨ ε < |corrected B e q K c-trial B e q| := by
  by_contra! h
  have first := abs_le.mp (fits bp dp ql small h.1)
  have second := abs_le.mp (fits bp (dp.trans de) ql small h.2)
  have diff := separation bp (bp.trans_le dp) de top same
  linarith only [first.2,second.1,diff,apart]

theorem pair_control (c : ℝ) :
    1/(8192*16:ℝ) < |corrected 16 19 29 31 c-reading 551 16| ∨
    1/(8192*16:ℝ) < |corrected 16 23 29 31 c-reading 667 16| := by
  rw [show (551:ℕ)=19*29 by decide,actual_value (by decide : Nat.Prime 19) (by decide : Nat.Prime 29) (by decide),
    show (667:ℕ)=23*29 by decide,actual_value (by decide : Nat.Prime 23) (by decide : Nat.Prime 29) (by decide)]
  apply incompatible (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num)
  norm_num
  linarith only [add_one_le_exp (-(63:ℝ)/128)]

open private PrimeFactors.MixedPrefixSample.mem_upper PrimeFactors.MixedPrefixSample.mem_primes
  from PrimeFactors.MixedPrefixSample
open private PrimeFactors.FiniteBinCollisionPopulation.upper_eligible from PrimeFactors.FiniteBinCollisionPopulation

attribute [local irreducible] upperPrimes primes eligible
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

/-- Pigeonhole on both the quotient and the remainder modulo a fixed spacing.
The maximum upper-band prime is kept outside the pigeonhole set. -/
private theorem witnesses {K : ℕ} (small : K≤5500*X) :
    ∃ p r q : ℕ, p∈upperPrimes ∧ r∈upperPrimes ∧ q∈upperPrimes ∧ p<r ∧ r<q ∧
      (p,q)∈eligible ∧ (r,q)∈eligible ∧ K/p=K/r ∧ 2^998≤r-p := by
  classical
  have count := ChebyshevPrimeSample.prime_count
  change 11*(2:ℕ)^1023<35500*(upperPrimes.card-1) at count
  have price : 35500*(5501*2^998)≤11*(2:ℕ)^1023 := by decide +kernel
  have many : 5501*2^998 < upperPrimes.card-1 := by omega
  have nonempty : upperPrimes.Nonempty := card_pos.mp (by omega)
  let q := upperPrimes.max' nonempty
  have qin : q∈upperPrimes := upperPrimes.max'_mem nonempty
  let labels := range 5501 ×ˢ range (2^998)
  have less : labels.card < (upperPrimes.erase q).card := by
    simpa only [labels,card_product,card_range,card_erase_of_mem qin] using many
  let label (z : ℕ) := (K/z,z%2^998)
  obtain ⟨a,am,b,bm,ne,eq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to less
    (f:=label) (by
      intro z zm
      have data := PrimeFactors.MixedPrefixSample.mem_primes.mp (PrimeFactors.MixedPrefixSample.mem_upper.mp
        (mem_of_mem_erase zm)).1
      have zp := data.2.pos
      have limit : K<5501*z := by
        have := Nat.mul_le_mul_left 5500 data.1.1
        omega
      simp only [label,labels,mem_product,mem_range]
      exact ⟨(Nat.div_lt_iff_lt_mul zp).mpr limit, Nat.mod_lt _ (pow_pos (by decide : 0<(2:ℕ)) _)⟩)
  have build {d e : ℕ} (dm : d∈upperPrimes.erase q) (em : e∈upperPrimes.erase q)
      (ord : d<e) (same : label d=label e) :
      ∃ p r q : ℕ, p∈upperPrimes ∧ r∈upperPrimes ∧ q∈upperPrimes ∧ p<r ∧ r<q ∧
        (p,q)∈eligible ∧ (r,q)∈eligible ∧ K/p=K/r ∧ 2^998≤r-p := by
    obtain ⟨en,eu⟩ := mem_erase.mp em
    have du := mem_of_mem_erase dm
    have high : e<q := lt_of_le_of_ne (upperPrimes.le_max' _ eu) en
    have cong : d ≡ e [MOD 2^998] := congrArg Prod.snd same
    exact ⟨d,e,q,du,eu,qin,ord,high,
      PrimeFactors.FiniteBinCollisionPopulation.upper_eligible du qin (ord.trans high),
      PrimeFactors.FiniteBinCollisionPopulation.upper_eligible eu qin high, congrArg Prod.fst same,
      Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' ord.le).mp cong)⟩
  rcases lt_or_gt_of_ne ne with ab|ba
  · exact build am bm ab eq
  · exact build bm am ba eq.symm

private theorem full_gap {K p r : ℕ} (cut : K≤5500*X) (pr : p≤r) (span : 2^998≤r-p) :
    324*(1/(8192*(X:ℝ))) < ((r:ℝ)-p)/(8*X)*exp (-(((K:ℝ)+2*X)/(8*X))) := by
  have xpos : (0:ℝ)<X := by exact_mod_cast (by decide +kernel : 0<X)
  have upper : (K:ℝ)≤5500*X := by exact_mod_cast cut
  have bound : ((K:ℝ)+2*X)/(8*X) ≤ 996*log 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [upper,mul_lt_mul_of_pos_right log_two_gt_d9 xpos]
  have lower : (1:ℝ)/(2:ℝ)^996 ≤ exp (-(((K:ℝ)+2*X)/(8*X))) := by
    rw [one_div, show (2:ℝ)^996=exp (996*log 2) by
      rw [←show ((996:ℕ):ℝ) = 996 by norm_num,exp_nat_mul,exp_log (by norm_num)], ←exp_neg]
    exact exp_le_exp.mpr (neg_le_neg bound)
  have gap : (2:ℝ)^998≤(r:ℝ)-p := by
    have h : (2:ℝ)^998≤((r-p:ℕ):ℝ) := by exact_mod_cast span
    rwa [Nat.cast_sub pr] at h
  have num : 324*(1/(8192*(X:ℝ))) < (2:ℝ)^998/(8*X)*(1/2^996) := by
    rw [show (2:ℝ)^998=(2:ℝ)^996*4 by rw [show 998=996+2 by decide,pow_add]; norm_num1]
    field_simp
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_pos (pow_pos (by norm_num : (0:ℝ)<2) 996) xpos]
  exact num.trans_le (mul_le_mul (div_le_div_of_nonneg_right gap (by positivity)) lower
    (by positivity) (div_nonneg (sub_nonneg.mpr (by exact_mod_cast pr)) (by positivity)))

/-- At any of these cutoffs there exist two eligible full-width products
sharing their larger prime such that *every* common real correction misses
on at least one. The witness products may depend on the cutoff. -/
theorem full_width {K : ℕ} (cut : K≤5500*X) :
    ∃ p r q : ℕ, p<r ∧ r<q ∧ (p,q)∈eligible ∧ (r,q)∈eligible ∧ ∀ c : ℝ,
      1/(8192*(X:ℝ)) < |corrected X p q K c-reading (p*q) X| ∨
      1/(8192*(X:ℝ)) < |corrected X r q K c-reading (r*q) X| := by
  obtain ⟨p,r,q,pm,rm,qm,pr,rq,pqOK,rqOK,same,span⟩ := witnesses cut
  have pu := PrimeFactors.MixedPrefixSample.mem_primes.mp (PrimeFactors.MixedPrefixSample.mem_upper.mp pm).1
  have ru := PrimeFactors.MixedPrefixSample.mem_primes.mp (PrimeFactors.MixedPrefixSample.mem_upper.mp rm).1
  have qu := PrimeFactors.MixedPrefixSample.mem_primes.mp (PrimeFactors.MixedPrefixSample.mem_upper.mp qm).1
  refine ⟨p,r,q,pr,rq,pqOK,rqOK,?_⟩
  intro c
  rw [actual_value pu.2 qu.2 (pr.trans rq),actual_value ru.2 qu.2 rq]
  apply incompatible (by decide +kernel) pu.1.1 pr.le ru.1.2.le qu.1.1 same _ (full_gap cut pr.le span)
  exact one_div_le_one_div_of_le (by norm_num) (by
    have : (1:ℝ)≤X := by exact_mod_cast (by decide +kernel : 1≤X)
    linarith)

/-- Applying the additive correction to the retained logarithm scales the
uncorrected public gcd reading by a shared positive number. -/
theorem public_agrees {p q B K : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (before : K<p*q) (c : ℝ) :
    PublicCyclotomicLogReading.dense (p*q) B K*exp (-c) = corrected B p q K c := by
  rw [PublicCyclotomicLogReading.agrees hp hq ord before,approx,corrected,←exp_add]
  rfl

open private PrimeFactors.MixedPrefixSample.mem_sample from PrimeFactors.MixedPrefixSample

/-- For each cutoff there exist genuine eligible products on which no common
multiplicative scale of the public gcd reading fits both. -/
theorem public_full_width {K : ℕ} (cut : K≤5500*X) :
    ∃ p r q : ℕ, p<r ∧ r<q ∧ (p,q)∈eligible ∧ (r,q)∈eligible ∧ ∀ c : ℝ,
      1/(8192*(X:ℝ)) < |PublicCyclotomicLogReading.dense (p*q) X K*exp (-c)-reading (p*q) X| ∨
      1/(8192*(X:ℝ)) < |PublicCyclotomicLogReading.dense (r*q) X K*exp (-c)-reading (r*q) X| := by
  obtain ⟨p,r,q,pr,rq,pe,re,fail⟩ := full_width cut
  have data {d q : ℕ} (hit : (d,q) ∈ eligible) : d.Prime ∧ q.Prime ∧ K<d*q := by
    rw [eligible] at hit
    obtain ⟨dp,qp,_,low,_⟩ := mem_ordered.mp (PrimeFactors.MixedPrefixSample.mem_sample.mp hit).1
    have before := cut.trans_lt (by decide +kernel : 5500*X<2*X^2)
    exact ⟨(PrimeFactors.MixedPrefixSample.mem_primes.mp dp).2,
      (PrimeFactors.MixedPrefixSample.mem_primes.mp qp).2,before.trans_le low⟩
  obtain ⟨pp,qp,pbig⟩ := data pe
  obtain ⟨rp,_,rbig⟩ := data re
  refine ⟨p,r,q,pr,rq,pe,re,?_⟩
  intro c
  rw [public_agrees pp qp (pr.trans rq) pbig,public_agrees rp qp rq rbig]
  exact fail c

end PrimeFactors.CyclotomicCommonTailCorrection
