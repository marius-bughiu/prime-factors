import PrimeFactors.FractionalPrefixReadout
import PrimeFactors.CircleMarkMidcutWithoutReplacement

/-! Exact mean square error of the ordinary nonunit-frequency estimate on
the positive integers through floor(N/m). The uniform models either sample
independently with replacement or choose a fixed number of distinct positions. -/
namespace PrimeFactors.FractionalPrefixSampleCost

open Finset FractionalNonunitPrefix CircleMarkStoppingPrecision CircleMarkMidcutWithoutReplacement
open scoped Classical BigOperators

/-- Each population entry is an actual integer in the shortened prefix. -/
abbrev Entry (n m : ℕ) := ↥(Ioc 0 (n/m))

private theorem card_entry (n m : ℕ) : Fintype.card (Entry n m) = n/m := by
  rw [Fintype.card_coe, Nat.card_Ioc, Nat.sub_zero]

private theorem inhabited_entry {n m : ℕ} (h : 0 < n/m) : Nonempty (Entry n m) :=
  ⟨⟨1, mem_Ioc.mpr ⟨by decide, h⟩⟩⟩

private noncomputable def flag (n m : ℕ) (t : Entry n m) : ℚ :=
  if ¬ t.val.Coprime n then 1 else 0

/-- The sample average of these values equals m times one plus the
prefix length times the measured nonunit frequency. -/
noncomputable def estimate (n m : ℕ) (t : Entry n m) : ℚ :=
  m + ((m : ℚ)*(n/m : ℕ))*flag n m t

/-- The integer form of (p+q−m) times the totient of pq. -/
def variance (p q m : ℕ) := (p+q-m)*((p-1)*(q-1))

private theorem flag_mean (n m : ℕ) :
    (𝔼 t, flag n m t) = (prefixCount n m : ℚ)/(n/m : ℕ) := by
  rw [Fintype.expect_eq_sum_div_card, card_entry]
  congr 1
  change (∑ t ∈ (Ioc 0 (n/m)).attach, (if ¬t.val.Coprime n then (1:ℚ) else 0)) = _
  rw [sum_attach _ (fun x : ℕ => if ¬x.Coprime n then (1:ℚ) else 0), sum_boole]
  rfl

private theorem length_identity {n m : ℕ} (hm : 2 ≤ m) (divides : m ∣ n+1) :
    m*(n/m+1)=n+1 := by
  obtain ⟨k,e⟩ := divides
  cases k with
  | zero => simp at e
  | succ k =>
    rw [Nat.mul_succ] at e
    have decomp : n = m-1 + m*k := by omega
    have quotient : n/m=k := by
      rw [decomp,Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt (by omega),zero_add]
    rw [quotient,Nat.mul_add,Nat.mul_one,e]

/-- Each denominator at least two dividing gcd(24,N+1) has a constant
prime-sum correction. -/
structure Eligible (n m : ℕ) : Prop where
  two_le : 2 ≤ m
  divides_24 : m ∣ 24
  residue : m ∣ n+1

/-- On a nonempty prefix, the public observation is unbiased for the prime
sum and has one-draw variance (p+q−m)(p−1)(q−1). -/
theorem moments {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q)
    (h : Eligible (p*q) m) (pos : 0 < p*q/m) :
    (𝔼 t, estimate (p*q) m t) = (p:ℚ)+q ∧
    (𝔼 t, (estimate (p*q) m t-((p:ℚ)+q))^2) = (variance p q m : ℚ) := by
  let n := p*q
  let c : ℚ := prefixCount n m
  let l : ℚ := (n/m : ℕ)
  letI := inhabited_entry pos
  have ln : l ≠ 0 := by dsimp [l,n]; exact_mod_cast pos.ne'
  have S := FractionalPrefixReadout.sum_eq hp hq diff h.two_le h.divides_24 h.residue
  have T := length_identity h.two_le h.residue
  have eqS : (p:ℚ)+q=m*(c+1) := by dsimp [c,n]; exact_mod_cast S
  have eqL : (m:ℚ)*(l+1)=p*q+1 := by dsimp [l,n]; exact_mod_cast T
  have raw : (𝔼 t, flag n m t)=c/l := flag_mean n m
  have admissible : m ≤ p+q := by rw [S]; exact Nat.le_mul_of_pos_right _ (by omega)
  have centered (t : Entry n m) :
      (estimate n m t-((p:ℚ)+q))^2 =
      flag n m t * ((m*l)^2-2*m^2*l*c)+(m*c)^2 := by
    rw [eqS]
    change ((m:ℚ)+m*l*flag n m t-m*(c+1))^2=_
    unfold flag
    split <;> ring
  constructor
  · change (𝔼 t : Entry n m, ((m:ℚ)+(m*l)*flag n m t))=_
    rw [expect_add_distrib,Fintype.expect_const,←mul_expect,raw,eqS]
    field_simp
    ring
  · change (𝔼 t : Entry n m, (estimate n m t-((p:ℚ)+q))^2)=_
    simp only [centered,expect_add_distrib,←expect_mul,Fintype.expect_const,raw]
    have coeff : (m:ℚ)*(l-c)=(p-1)*(q-1) := by linarith only [eqS,eqL]
    have mc : (m:ℚ)*c=p+q-m := by linarith only [eqS]
    rw [variance, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub admissible, Nat.cast_add,
      Nat.cast_sub hp.one_lt.le, Nat.cast_sub hq.one_lt.le, Nat.cast_one, ←coeff, ←mc]
    field_simp
    ring

theorem iid_error {p q m k : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q)
    (h : Eligible (p*q) m) (pos : 0 < p*q/m) (kp : 0<k) :
    meanSquare (estimate (p*q) m) ((p:ℚ)+q) k = (variance p q m : ℚ)/k := by
  letI := inhabited_entry pos
  obtain ⟨mean,var⟩ := moments hp hq diff h pos
  rw [sample_variance _ mean kp,var]

theorem distinct_error {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q)
    (h : Eligible (p*q) m) (big : 1 < p*q/m) (s : Finset (Entry (p*q) m)) (sp : 0<s.card) :
    distinctError (estimate (p*q) m) ((p:ℚ)+q) s =
      (variance p q m : ℚ)*((p*q/m : ℕ)- (s.card : ℚ))/
        ((s.card:ℚ)*((p*q/m : ℕ)-(1:ℚ))) := by
  letI := inhabited_entry (by omega : 0<p*q/m)
  obtain ⟨mean,var⟩ := moments hp hq diff h (by omega)
  rw [correction _ mean s sp (by rwa [card_entry]), var, card_entry]

/-- Exact integer criterion for mean square error below a/b with replacement. -/
theorem iid_criterion {p q m k a b : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q)
    (h : Eligible (p*q) m) (pos : 0 < p*q/m) (kp : 0 < k) (bp : 0 < b) :
    meanSquare (estimate (p*q) m) ((p:ℚ)+q) k < (a:ℚ)/b ↔
      b*variance p q m < a*k := by
  rw [iid_error hp hq diff h pos kp, div_lt_div_iff₀ (by exact_mod_cast kp) (by exact_mod_cast bp)]
  rw [mul_comm b]
  exact_mod_cast Iff.rfl

/-- Exact integer criterion for mean square error below a/b without replacement. -/
theorem distinct_criterion {p q m a b : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q)
    (h : Eligible (p*q) m) (big : 1 < p*q/m) (s : Finset (Entry (p*q) m)) (sp : 0<s.card)
    (bp : 0 < b) :
    distinctError (estimate (p*q) m) ((p:ℚ)+q) s < (a:ℚ)/b ↔
      b*variance p q m*(p*q/m-s.card) < a*s.card*(p*q/m-1) := by
  have cap := s.card_le_univ.trans_eq (card_entry ..)
  have zp : (0:ℚ)<s.card := by exact_mod_cast sp
  have zb : (1:ℚ)<(p*q/m : ℕ) := by exact_mod_cast big
  rw [distinct_error hp hq diff h big s sp,
    div_lt_div_iff₀ (mul_pos zp (sub_pos.mpr zb)) (by exact_mod_cast bp)]
  rw [show b*variance p q m*(p*q/m-s.card)=variance p q m*(p*q/m-s.card)*b by ring,
    Nat.mul_assoc a]
  rw [←Nat.cast_sub cap, ←Nat.cast_one (R:=ℚ), ←Nat.cast_sub big.le]
  exact_mod_cast Iff.rfl

/-- The one-draw variance exceeds the smaller prime times the product when
the primes are at least 48. This uses only the universal denominator bound. -/
theorem variance_lower {p q m : ℕ} (lo : 48≤p) (order : p≤q) (hm : m≤24) :
    p*(p*q)<variance p q m := by
  have a : 3*p≤2*(p+q-m) := by omega
  have b : 5*p≤6*(p-1) := by omega
  have c : 5*q≤6*(q-1) := by omega
  have h := Nat.mul_le_mul a (Nat.mul_le_mul b c)
  have pos := Nat.mul_pos (by omega : 0<p) (Nat.mul_pos (by omega : 0<p) (by omega : 0<q))
  unfold variance
  nlinarith only [h,pos]

private theorem omissions {p q m k a b : ℕ} (lo : 48≤p) (order : p≤q) (hm : m≤24)
    (mp : 0<m) (cap : k≤p*q/m)
    (precise : b*variance p q m*(p*q/m-k)<a*k*(p*q/m-1)) :
    b*m^2*(p*q/m-k)<a*q := by
  let l := p*q/m
  have v := (variance_lower lo order hm).le
  have hl : m*l ≤ p*q := Nat.mul_div_le ..
  have first : p*(p*q)*(b*m^2*(l-k)) ≤ b*variance p q m*(l-k)*m^2 := by
    calc _ = b*(p*(p*q))*(l-k)*m^2 := by ring
         _ ≤ _ := by gcongr
  have second : a*k*(l-1)*m^2 ≤ p*(p*q)*(a*q) := by
    calc _ ≤ a*l*l*m^2 := by gcongr; exact Nat.sub_le ..
         _ = a*((m*l)*(m*l)) := by ring
         _ ≤ a*((p*q)*(p*q)) := by gcongr
         _ = _ := by ring
  exact Nat.lt_of_mul_lt_mul_left ((first.trans_lt
    (Nat.mul_lt_mul_of_pos_right precise (pow_pos mp _))).trans_le second)

private theorem rms_sq (x : ℚ) {a b : ℕ} (ap : 0<a) (bp : 0<b) :
    Real.sqrt (x:ℝ)<(a:ℝ)/b → x<(a^2:ℕ)/(b^2:ℕ) := by
  intro h
  have lt := (Real.sqrt_lt' (div_pos (by exact_mod_cast ap) (by exact_mod_cast bp))).mp h
  rw [div_pow] at lt
  apply (Rat.cast_lt (K:=ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Nat.cast_pow] using lt

private theorem length_large {p q m : ℕ} (lo : 48≤p) (order : p≤q) (h : Eligible (p*q) m) :
    1 < p*q/m := by
  have hm := Nat.le_of_dvd (by decide : 0<24) h.divides_24
  have two := h.two_le
  have pq := Nat.le_mul_of_pos_right p (by omega : 0<q)
  exact (Nat.le_div_iff_mul_le (by omega : 0<m)).mpr (by omega)

/-- At RMS below one, the number of omitted positions is strictly less than q/m². -/
theorem distinct_unit {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (h : Eligible (p*q) m) (lo : 48≤p) (s : Finset (Entry (p*q) m)) (sp : 0<s.card)
    (accuracy : Real.sqrt (distinctError (estimate (p*q) m) ((p:ℚ)+q) s : ℝ)<1) :
    m^2*(p*q/m-s.card)<q := by
  have precise := (distinct_criterion (a:=1) (b:=1) hp hq lt.ne h (length_large lo lt.le h) s sp (by decide)).mp
    (by simpa using rms_sq _ (a:=1) (b:=1) (by decide) (by decide) (by simpa using accuracy))
  simpa using omissions lo lt.le (Nat.le_of_dvd (by decide) h.divides_24)
    (by have := h.two_le; omega) (s.card_le_univ.trans_eq (card_entry ..)) precise

/-- Rounding a supplied prime-sum estimate to its known m-lattice has
half-spacing m/2. Reaching that RMS scale still leaves fewer than q/4
entries unexamined, including fewer than 2^1022 for a 1024-bit larger prime. -/
theorem distinct_lattice {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (h : Eligible (p*q) m) (lo : 48≤p) (s : Finset (Entry (p*q) m)) (sp : 0<s.card)
    (accuracy : Real.sqrt (distinctError (estimate (p*q) m) ((p:ℚ)+q) s : ℝ)<(m:ℝ)/2) :
    4*(p*q/m-s.card)<q ∧ (q<2^1024 → p*q/m-s.card<2^1022) := by
  have mp : 0<m := by have := h.two_le; omega
  have precise := (distinct_criterion (a:=m^2) (b:=2^2) hp hq lt.ne h (length_large lo lt.le h) s sp
    (by decide)).mp (rms_sq _ mp (by decide : 0<2) accuracy)
  have raw := omissions lo lt.le (Nat.le_of_dvd (by decide) h.divides_24) mp
    (s.card_le_univ.trans_eq (card_entry ..)) precise
  have lt' : m^2*(4*(p*q/m-s.card)) < m^2*q := by
    calc _ = 2^2*m^2*(p*q/m-s.card) := by ring
         _ < _ := raw
  have small := Nat.lt_of_mul_lt_mul_left lt'
  refine ⟨small,fun cap => ?_⟩
  have e : 2^1024=4*(2^1022:ℕ) := by decide +kernel
  exact Nat.lt_of_mul_lt_mul_left ((small.trans cap).trans_eq e)

/-- Ordinary independent draws at RMS below one need more than pN samples.
At the weaker lattice half-spacing they still need more than pN/144. -/
theorem iid_work {p q m k : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (h : Eligible (p*q) m) (lo : 48≤p) (kp : 0<k) :
    let e := Real.sqrt (meanSquare (estimate (p*q) m) ((p:ℚ)+q) k : ℝ)
    (e<1 → p*(p*q)<k) ∧ (e<(m:ℝ)/2 → p*(p*q)<144*k) := by
  have mp := h.two_le
  have mc := Nat.le_of_dvd (by decide : 0<24) h.divides_24
  have pos := (length_large lo lt.le h)
  have lower := variance_lower lo lt.le mc
  constructor
  · intro acc
    have precise := (iid_criterion (a:=1) (b:=1) hp hq lt.ne h (by omega) kp (by decide)).mp
      (by simpa using rms_sq _ (a:=1) (b:=1) (by decide) (by decide) (by simpa using acc))
    simpa using lower.trans (show variance p q m<k by simpa using precise)
  · intro acc
    have precise := (iid_criterion (a:=m^2) (b:=2^2) hp hq lt.ne h (by omega) kp (by decide)).mp
      (rms_sq _ (by omega : 0<m) (by decide : 0<2) acc)
    have cap : m^2 ≤ 576 := Nat.pow_le_pow_left mc 2
    have upper := precise.trans_le (Nat.mul_le_mul_right k cap)
    omega

/-- With two 1024-bit prime factors these two RMS targets exceed 2^3069
and 2^3061 draws. Both exponents increase by one for a 2048-bit product. -/
theorem iid_full_width {p q m k : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (h : Eligible (p*q) m) (width : 2^1023≤p) (kp : 0<k) :
    let e := Real.sqrt (meanSquare (estimate (p*q) m) ((p:ℚ)+q) k : ℝ)
    (e<1 → 2^3069<k ∧ (2^2047≤p*q → 2^3070<k)) ∧
    (e<(m:ℝ)/2 → 2^3061<k ∧ (2^2047≤p*q → 2^3062<k)) := by
  obtain ⟨unit,lattice⟩ := iid_work hp hq lt h ((by decide +kernel : 48≤2^1023).trans width) kp
  have small : 2^3069≤p*(p*q) := by
    calc (2:ℕ)^3069 = 2^1023*(2^1023*2^1023) := by decide +kernel
         _ ≤ _ := Nat.mul_le_mul width (Nat.mul_le_mul width (width.trans lt.le))
  have large (prod : 2^2047≤p*q) : 2^3070≤p*(p*q) := by
    calc (2:ℕ)^3070 = 2^1023*2^2047 := by decide +kernel
         _ ≤ _ := Nat.mul_le_mul width prod
  refine ⟨fun acc => ⟨small.trans_lt (unit acc),fun prod => (large prod).trans_lt (unit acc)⟩,?_⟩
  intro acc
  have a := small.trans_lt (lattice acc)
  constructor
  · have scale : 144*(2:ℕ)^3061≤2^3069 := by decide +kernel
    exact Nat.lt_of_mul_lt_mul_left (scale.trans_lt a)
  · intro prod
    have scale : 144*(2:ℕ)^3062≤2^3070 := by decide +kernel
    exact Nat.lt_of_mul_lt_mul_left (scale.trans_lt ((large prod).trans_lt (lattice acc)))

private theorem eligible_two : Eligible (37*59) 2 := ⟨by decide,by decide,by decide⟩
private theorem eligible_24 : Eligible (37*59) 24 := ⟨by decide,by decide,by decide⟩

/-- At 2183 the exact variances are 196272 for m=2 and 150336 for m=24.
The first two thresholds target RMS below one. The last uses RMS below 12. -/
theorem example_iid :
    variance 37 59 2=196272 ∧ variance 37 59 24=150336 ∧
    ∀ k : ℕ, 0<k →
    (meanSquare (estimate 2183 2) 96 k<1 ↔ 196273≤k) ∧
    (meanSquare (estimate 2183 24) 96 k<1 ↔ 150337≤k) ∧
    (meanSquare (estimate 2183 24) 96 k<144 ↔ 1045≤k) := by
  refine ⟨by decide, by decide, fun k pos => ?_⟩
  have f {m a : ℕ} (h : Eligible (37*59) m) (lp : 0<37*59/m) :
      meanSquare (estimate 2183 m) 96 k<(a:ℚ) ↔ variance 37 59 m<a*k := by
    simpa only [Nat.cast_ofNat,show (37:ℚ)+59=96 by norm_num, Nat.cast_one, div_one, one_mul] using
      (iid_criterion (a:=a) (b:=1) (by decide) (by decide) (by decide) h lp pos (by decide))
  rw [←Nat.cast_one (R:=ℚ), ←show ((144:ℕ):ℚ)=144 by norm_num, f eligible_two (by decide),
    f eligible_24 (by decide), f eligible_24 (by decide)]
  norm_num [variance]
  omega

/-- The matching distinct-sample thresholds are 1085 of 1091, 90 of 90,
and 83 of 90, respectively. -/
theorem example_distinct :
    (∀ s : Finset (Entry 2183 2), 0<s.card →
      (distinctError (estimate 2183 2) 96 s<1 ↔ 1085≤s.card)) ∧
    (∀ s : Finset (Entry 2183 24), 0<s.card →
      (distinctError (estimate 2183 24) 96 s<1 ↔ 90≤s.card) ∧
      (distinctError (estimate 2183 24) 96 s<144 ↔ 83≤s.card)) := by
  have f {m a : ℕ} (h : Eligible (37*59) m) (lp : 1<37*59/m)
      (s : Finset (Entry 2183 m)) (pos : 0<s.card) :
      distinctError (estimate 2183 m) 96 s<(a:ℚ) ↔
        variance 37 59 m*(2183/m-s.card)<a*s.card*(2183/m-1) := by
    simpa only [Nat.cast_ofNat,show (37:ℚ)+59=96 by norm_num, Nat.cast_one, div_one, one_mul] using
      (distinct_criterion (a:=a) (b:=1) (by decide) (by decide) (by decide) h lp s pos (by decide))
  constructor
  · intro s pos
    rw [←Nat.cast_one (R:=ℚ),f eligible_two (by decide) s pos]
    norm_num [variance]
    omega
  · intro s pos
    rw [←Nat.cast_one (R:=ℚ),←show ((144:ℕ):ℚ)=144 by norm_num,f eligible_24 (by decide) s pos,
      f eligible_24 (by decide) s pos]
    norm_num [variance]
    omega

end PrimeFactors.FractionalPrefixSampleCost
