import PrimeFactors.BlockProbePopulation
import PrimeFactors.ChebyshevPrimeSample

/-! The base is the public integer square root of the product. Small local
orders bound the possible square-root residues. Large orders force the two
prime predecessors onto the same arithmetic progression. -/
namespace PrimeFactors.ProductExponentPopulation

open Finset MixedPrefixSample

/-- The exponent of this single gcd query depends on the product. -/
def reading (n : ℕ) : ℤ := (n.sqrt : ℤ)^(n-1)-1

noncomputable def flagged : Finset (ℕ × ℕ) :=
  eligible.filter fun z => 1 < Int.gcd (reading (z.1*z.2)) (z.1*z.2 : ℕ)

def signedReading (n d : ℕ) (plus : Bool) : ℤ :=
  if plus then (n.sqrt : ℤ)^d+1 else (n.sqrt : ℤ)^d-1

/-- For any chosen divisor exponent, including all eligible stages of a
square chain, the signed query divides the final integer reading itself. -/
theorem signed_dvd {n d : ℕ} (plus : Bool)
    (allowed : (if plus then 2*d else d) ∣ n-1) : signedReading n d plus ∣ reading n := by
  obtain ⟨k,exp⟩ := allowed
  cases plus
  · simpa only [signedReading, Bool.false_eq_true, ↓reduceIte, reading,exp] using
      pow_one_sub_dvd_pow_mul_sub_one (n.sqrt : ℤ) d k
  · let t : ℤ := n.sqrt
    have factor : t^d+1 ∣ t^(2*d)-1 :=
      ⟨t^d-1,by rw [Nat.mul_comm 2 d, pow_mul]; ring⟩
    exact factor.trans (by
      simpa only [reading, exp, ↓reduceIte, t] using
        pow_one_sub_dvd_pow_mul_sub_one t (2*d) k)

theorem signed_gcd_dvd {n d : ℕ} (plus : Bool)
    (allowed : (if plus then 2*d else d) ∣ n-1) :
    Int.gcd (signedReading n d plus) n ∣ Int.gcd (reading n) n :=
  Int.gcd_dvd_gcd_of_dvd_left _ (signed_dvd plus allowed)

private noncomputable def partners (B p e : ℕ) : Finset ℕ := by
  classical
  exact (Ico B (2*B)).filter fun q => q%2=1 ∧ ((p*q).sqrt : ZMod p)^e=1

private theorem partners_card {B p e : ℕ} (hp : p.Prime) (bp : B ≤ p)
    (pu : p < 2*B) (ep : 0 < e) : (partners B p e).card ≤ 2*e := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let F : Polynomial (ZMod p) := Polynomial.X^e - Polynomial.C 1
  have bound := SquareRootShiftPartners.polynomial bp pu (partners B p e) F
    (Polynomial.X_pow_sub_C_ne_zero ep 1) 0 (by
      intro q hq
      obtain ⟨h,odd,_⟩ := mem_filter.mp hq
      exact ⟨(mem_Ico.mp h).1,(mem_Ico.mp h).2,odd⟩) (by
      intro q hq
      simp [F,(mem_filter.mp hq).2.2])
  simpa only [F,Polynomial.natDegree_X_pow_sub_C] using bound

private noncomputable def anchors (B e : ℕ) : Finset ℕ :=
  (Icc 1 (2*B/e)).filter fun a => B ≤ e*a+1 ∧ e*a+1 < 2*B ∧ (e*a+1).Prime

private noncomputable def small (B e : ℕ) : Finset (ℕ × ℕ) :=
  (anchors B e).biUnion fun a =>
    let p := e*a+1
    (partners B p e).image fun q => (min p q,max p q)

private theorem small_card (B e : ℕ) (ep : 0 < e) : (small B e).card ≤ 4*B := by
  have each : (small B e).card ≤ (anchors B e).card*(2*e) := by
    apply card_biUnion_le_card_mul
    intro a ha
    obtain ⟨_,bp,pt,prime⟩ := mem_filter.mp ha
    exact card_image_le.trans (partners_card prime bp pt ep)
  have cnt : (anchors B e).card ≤ 2*B/e := by
    exact (card_filter_le ..).trans (by simp)
  calc
    _ ≤ _ := each
    _ ≤ (2*B/e)*(2*e) := Nat.mul_le_mul_right _ cnt
    _ = 2*((2*B/e)*e) := by ring
    _ ≤ 2*(2*B) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self ..)
    _ = _ := by ring

/-- When both predecessors are multiples of e, c denotes the larger
cofactor and a the smaller. The direction of the local hit is immaterial. -/
private noncomputable def large (B c : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (2*B/c)) ×ˢ (Icc 1 c)).image fun x => (x.1*x.2+1,x.1*c+1)

private theorem large_card (B c : ℕ) : (large B c).card ≤ 2*B := by
  refine card_image_le.trans ?_
  simpa [Finset.card_product] using Nat.div_mul_le_self (2*B) c

private noncomputable def cover (B K : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 K).biUnion (small B)) ∪ ((Icc 1 K).biUnion (large B))

private theorem cover_card (B K : ℕ) : (cover B K).card ≤ 6*B*K := by
  have tiny := card_biUnion_le_card_mul (Icc 1 K) (small B) (4*B)
    (fun e he => small_card B e (mem_Icc.mp he).1)
  have big := card_biUnion_le_card_mul (Icc 1 K) (large B) (2*B)
    (fun c _ => large_card B c)
  have bound := (card_union_le _ _).trans (Nat.add_le_add tiny big)
  change _ ≤ 6*B*K
  calc
    _ ≤ _ := bound
    _ = 6*B*K := by simp; ring

/-- A hit has a positive local order dividing both predecessors. -/
theorem order_of_hit {p q : ℕ} (pp : p.Prime) (qp : 1 < q)
    (hit : (p : ℤ) ∣ reading (p*q)) :
    ∃ e : ℕ, 0 < e ∧ e ∣ p-1 ∧ e ∣ q-1 ∧ ((p*q).sqrt : ZMod p)^e=1 := by
  letI : Fact p.Prime := ⟨pp⟩
  let t : ZMod p := (p*q).sqrt
  have eq : t^(p*q-1)=1 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr hit
    simpa [reading,t,sub_eq_zero] using h
  have pn := pp.one_lt
  have pq : p*q > 1 := by nlinarith
  have tn : t ≠ 0 := by
    intro zero
    simp [zero,zero_pow (by omega : p*q-1≠0)] at eq
  let e := orderOf t
  have dp := ZMod.orderOf_dvd_card_sub_one tn
  have dn := orderOf_dvd_of_pow_eq_one eq
  have exp : p*q-1 = (p-1)*q+(q-1) := by
    have hp1 : p-1+1=p := by omega
    have hq1 : q-1+1=q := by omega
    have eqmul := congrArg (· * q) hp1
    simp only [Nat.add_mul,Nat.one_mul] at eqmul
    omega
  rw [exp] at dn
  have dq : e ∣ q-1 := (Nat.dvd_add_right (dvd_mul_of_dvd_left dp q)).mp dn
  exact ⟨e,Nat.pos_of_dvd_of_pos dp (by omega),dp,dq,pow_orderOf_eq_one _⟩

private theorem large_member {B K e a c : ℕ} (scale : 2*B = K^2)
    (ep : K < e) (ap : 0 < a) (ac : a ≤ c) (cap : e*c+1 < 2*B) :
    (e*a+1,e*c+1) ∈ (Icc 1 K).biUnion (large B) := by
  have cp : 0 < c := by omega
  have ck : c ≤ K := by
    by_contra! h
    have big := Nat.mul_lt_mul_of_lt_of_lt ep h
    rw [←sq,←scale] at big
    omega
  exact mem_biUnion.mpr ⟨c,mem_Icc.mpr ⟨cp,ck⟩,mem_image.mpr ⟨(e,a),
    mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,(Nat.le_div_iff_mul_le cp).mpr (by change e*c ≤ 2*B; omega)⟩,
      mem_Icc.mpr ⟨ap,ac⟩⟩,rfl⟩⟩

private theorem included {B K p q : ℕ} (scale : 2*B = K^2)
    (pp : p.Prime) (qp : 1 < q) (pB : B≤p) (pU : p<2*B)
    (qB : B≤q) (qU : q<2*B) (qo : q%2=1) (hit : (p : ℤ) ∣ reading (p*q)) :
    (min p q,max p q) ∈ cover B K := by
  obtain ⟨e,ep,⟨a,pa⟩,⟨b,qb⟩,root⟩ := order_of_hit pp qp hit
  have pn := pp.one_lt
  have P : e*a+1=p := by omega
  have Q : e*b+1=q := by omega
  have ap : 0 < a := by by_contra! h; obtain rfl := Nat.eq_zero_of_le_zero h; simp at pa; omega
  have bp : 0 < b := by by_contra! h; obtain rfl := Nat.eq_zero_of_le_zero h; simp at qb; omega
  rw [cover,mem_union]
  by_cases low : e ≤ K
  · left
    apply mem_biUnion.mpr
    refine ⟨e,mem_Icc.mpr ⟨ep,low⟩,mem_biUnion.mpr ⟨a,?_,?_⟩⟩
    · apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨ap,(Nat.le_div_iff_mul_le ep).mpr ?_⟩,by simpa [P] using And.intro pB (And.intro pU pp)⟩
      rw [Nat.mul_comm]; omega
    · simp only [P]
      exact mem_image.mpr ⟨q,mem_filter.mpr ⟨mem_Ico.mpr ⟨qB,qU⟩,qo,root⟩,rfl⟩
  · right
    rcases le_total a b with ab | ba
    · have pq : p ≤ q := by rw [←P,←Q]; exact Nat.add_le_add_right (Nat.mul_le_mul_left e ab) 1
      simpa [min_eq_left pq,max_eq_right pq,P,Q] using
        large_member scale (lt_of_not_ge low) ap ab (Q ▸ qU)
    · have pq : q ≤ p := by rw [←P,←Q]; exact Nat.add_le_add_right (Nat.mul_le_mul_left e ba) 1
      simpa [min_eq_right pq,max_eq_left pq,P,Q] using
        large_member scale (lt_of_not_ge low) bp ba (P ▸ pU)

attribute [local irreducible] MixedPrefixSample.X eligible

set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

/-- The exponent and sign may depend on the input. A nonunit from any
allowed query, including the entire modulus, places the pair in flagged. -/
theorem signed_in_flagged {p q d : ℕ} (mem : (p,q) ∈ eligible) (plus : Bool)
    (allowed : (if plus then 2*d else d) ∣ p*q-1)
    (hit : 1 < Int.gcd (signedReading (p*q) d plus) (p*q : ℕ)) : (p,q) ∈ flagged := by
  apply mem_filter.mpr
  refine ⟨mem, ?_⟩
  have div := signed_gcd_dvd plus allowed
  have ord := mem
  rw [eligible,sample] at ord
  obtain ⟨_,_,_,size,_⟩ := mem_ordered.mp (mem_filter.mp ord).1
  have pos : 0 < p*q := (show 0 < 2*X^2 by unfold MixedPrefixSample.X; positivity).trans_le size
  have ng : 0 < Int.gcd (reading (p*q)) (p*q : ℕ) :=
    Nat.pos_of_dvd_of_pos (Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..)) pos
  exact hit.trans_le (Nat.le_of_dvd ng div)

private theorem prime_info {p : ℕ} (mem : p ∈ primes) :
    X ≤ p ∧ p < 2*X ∧ p%2=1 ∧ p.Prime := by
  obtain ⟨bounds,prime⟩ := mem_filter.mp mem
  obtain ⟨lo,hi⟩ := mem_Ico.mp bounds
  have big : 3 ≤ X := by unfold MixedPrefixSample.X; decide +kernel
  obtain ⟨k,h⟩ := prime.odd_of_ne_two (by omega)
  exact ⟨lo,hi,by omega,prime⟩

/-- Uniform sorted distinct pairs of 1024-bit primes with a full 2048-bit
product. This includes whole-modulus gcds in the numerator, so the same
strict bound holds for proper splits. No randomness of the base is assumed. -/
theorem flagged_bound : flagged.card ≤ 6*X*2^512 := by
  classical
  let K : ℕ := 2^512
  have scale : 2*X = K^2 := by unfold MixedPrefixSample.X; dsimp only [K]; decide +kernel
  have subset : flagged ⊆ cover X K := by
    rintro ⟨p,q⟩ mem
    obtain ⟨ok,hit⟩ := mem_filter.mp mem
    rw [eligible,sample] at ok
    obtain ⟨ord,lt⟩ := mem_filter.mp ok
    obtain ⟨pm,qm,_⟩ := mem_ordered.mp ord
    obtain ⟨pl,pu,po,pp⟩ := prime_info pm
    obtain ⟨ql,qu,qo,qp⟩ := prime_info qm
    rcases BlockProbePopulation.prime_dvd_reading pp qp _ hit with localHit | localHit
    · simpa [min_eq_left lt.le,max_eq_right lt.le] using
        included scale pp qp.one_lt pl pu ql qu qo localHit
    · rw [Nat.mul_comm p q] at localHit
      simpa [min_eq_right lt.le,max_eq_left lt.le] using
        included scale qp pp.one_lt ql qu pl pu po localHit
  exact (card_le_card subset).trans (cover_card X K)

private theorem normalize {C : ℕ} (size : C ≤ 6*X*2^512+X) : 2^484*C < eligible.card := by
  have arithmetic : 21000000*(2^484*(6*X*2^512+X)) < 2^2046 := by
    unfold MixedPrefixSample.X; decide +kernel
  exact Nat.lt_of_mul_lt_mul_left <| (Nat.mul_le_mul_left 21000000
    (Nat.mul_le_mul_left (2^484) size)).trans_lt (arithmetic.trans ChebyshevPrimeSample.eligible_count)

theorem population : 2^484 * flagged.card < eligible.card :=
  normalize (flagged_bound.trans (Nat.le_add_right ..))

/-- The optional direct gcd with the base detects precisely the twin
primes in this range. Their public square root is the smaller prime. -/
theorem precheck_iff {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (odd : 2 < p)
    (lt : p < q) (balanced : q < 2*p) :
    1 < (p*q).sqrt.gcd (p*q) ↔ q=p+2 := by
  let t := (p*q).sqrt
  have bot : p ≤ t := Nat.le_sqrt.mpr (Nat.mul_le_mul_left _ lt.le)
  have top : t < q := Nat.sqrt_lt.mpr (Nat.mul_lt_mul_of_pos_right lt qp.pos)
  constructor
  · intro hit
    have sides := BlockProbePopulation.prime_dvd_reading pp qp (t : ℤ) (by exact_mod_cast hit)
    have dv : p ∣ t := by
      rcases sides with ph|qh
      · exact Int.natCast_dvd_natCast.mp ph
      · have contra := Nat.le_of_dvd (pp.pos.trans_le bot) (Int.natCast_dvd_natCast.mp qh)
        omega
    obtain ⟨s,ss⟩ := dv
    have unit : s=1 := by
      rcases le_or_gt s 1 with low|high
      · by_contra! hn
        have : s=0 := by omega
        simp [this] at ss
        omega
      · have h := Nat.mul_le_mul_left p (show 2≤s by omega)
        omega
    have same : t=p := by simpa [unit] using ss
    have cap := Nat.lt_succ_sqrt' (p*q)
    change p*q < (t+1)^2 at cap
    rw [same] at cap
    have close : q ≤ p+2 := by
      by_contra far
      have h := Nat.mul_le_mul_left p (Nat.succ_le_of_lt (Nat.lt_of_not_ge far))
      nlinarith
    obtain ⟨i,oi⟩ := pp.odd_of_ne_two (by omega)
    obtain ⟨j,oj⟩ := qp.odd_of_ne_two (by omega)
    omega
  · rintro rfl
    have same : t=p := le_antisymm (Nat.le_of_lt_succ (Nat.sqrt_lt.mpr (by nlinarith))) bot
    change 1 < t.gcd _
    rw [same,Nat.gcd_eq_left (dvd_mul_right ..)]
    exact pp.one_lt

noncomputable def withPrecheck : Finset (ℕ × ℕ) :=
  eligible.filter fun z => 1 < (z.1*z.2).sqrt.gcd (z.1*z.2) ∨
    1 < Int.gcd (reading (z.1*z.2)) (z.1*z.2 : ℕ)

theorem population_with_precheck : 2^484 * withPrecheck.card < eligible.card := by
  classical
  let twins := (Ico X (2*X)).image fun p => (p,p+2)
  have sub : withPrecheck ⊆ flagged ∪ twins := by
    rintro ⟨p,q⟩ mem
    obtain ⟨ok,pre | exp⟩ := mem_filter.mp mem
    · apply mem_union_right
      rw [eligible,sample] at ok
      obtain ⟨ord,lt⟩ := mem_filter.mp ok
      obtain ⟨pm,qm,_⟩ := mem_ordered.mp ord
      obtain ⟨pl,pu,_,pp⟩ := prime_info pm
      obtain ⟨_,qu,_,qp⟩ := prime_info qm
      have low : 3 ≤ X := by unfold MixedPrefixSample.X; decide +kernel
      have twin := (precheck_iff pp qp (by omega) lt (by omega)).mp pre
      exact mem_image.mpr ⟨p,mem_Ico.mpr ⟨pl,pu⟩,Prod.ext rfl twin.symm⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨ok,exp⟩)
  have tc : twins.card ≤ X := card_image_le.trans (by simp; omega)
  exact normalize <| (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add flagged_bound tc))

end PrimeFactors.ProductExponentPopulation
