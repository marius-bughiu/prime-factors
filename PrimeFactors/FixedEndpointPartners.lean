import PrimeFactors.EndpointOffsetProduct
import PrimeFactors.InteriorBatchPopulation
import PrimeFactors.FactorSum
import PrimeFactors.NearEndpointPrimes

/-! Prime partners for an arbitrary prime close to the upper bit boundary.
All the algebra and ordinary-search exclusions are unconditional. The count
of primes in a short interval uses the stated Schoenfeld interval bound. -/
namespace PrimeFactors.FixedEndpointPartners
open Finset

set_option exponentiation.threshold 8192
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

abbrev U : ℕ := 2^1024
def lower (W : ℕ) := U-4*W+1
def upper (W : ℕ) := U-3*W
noncomputable def partners (W : ℕ) := InteriorBatchPopulation.firstPrimes (lower W) (upper W)
noncomputable def products (W q : ℕ) := (partners W).image (· * q)

/-- W is the partner-interval scale, K the number of ordinary midpoint tests. -/
structure Window (W K q : ℕ) : Prop where
  positive : 0<W
  width : 16*W≤U
  below : q<U
  closer : 8*(U-q)≤W
  area : W*(U-q)≤U
  distance : U*K≤W^2

private theorem partner_data {p W : ℕ} (hp : p∈partners W) :
    lower W≤p ∧ p≤upper W ∧ p.Prime := by
  obtain ⟨h,pr⟩ := mem_filter.mp (by simpa only [partners,InteriorBatchPopulation.firstPrimes] using hp)
  exact ⟨(mem_Icc.mp h).1,(mem_Icc.mp h).2,pr⟩

private theorem stride_floor {p q : ℕ} (op : Odd p) (oq : Odd q) :
    4 ≤ weightedStride (p*q) 1 1 := by
  obtain ⟨j,hj⟩ := op.mul oq
  have div : 4 ∣ weightedStride (p*q) 1 1 := by
    apply Nat.dvd_gcd (by decide)
    exact ⟨j+1,by rw [one_mul,hj]; ring⟩
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by decide : 0<24)) div

private theorem ordinary_miss {p q m a : ℕ} (pp : p.Prime) (qp : q.Prime)
    (proper : 2<p) (pq : p<q) (mid : p+q=2*m) (small : a<m) :
    ¬∃ d : ℕ, a^2=p*q+d^2 := by
  rintro ⟨d,sq⟩
  have le : d≤a := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (by omega : d^2≤a^2)
  have fac := fermat_split le sq
  have positive := Nat.mul_pos pp.pos qp.pos
  have plenty : p+q<p*q := by nlinarith only [Nat.mul_le_mul_right q (show 3≤p by omega),pq]
  have nontrivial : 1<a-d := by
    by_contra! h
    rcases (show a-d=0 ∨ a-d=1 by omega) with z|z
    · rw [z,zero_mul] at fac
      omega
    · rw [z,one_mul] at fac
      omega
  have pair := ordered_semiprime_pair_unique pp qp pq.le (show a-d≤a+d by omega) nontrivial fac.symm
  omega

/-- Every p in this interval gives two full-width factors and a full-width
product. The public endpoint probe recovers both in one square root, while
the first K ordinary Fermat discriminants are all nonsquares. -/
theorem comparison {W K p q : ℕ} (win : Window W K q) (qp : q.Prime) (hp : p∈partners W) :
    2^1023≤p ∧ p<q ∧ q<U ∧ 2^2047≤p*q ∧ p*q<2^2048 ∧
    EndpointOffsetProduct.probe U (p*q)=some (p,q) ∧
    ceilSqrt (p*q)+K≤(p+q)/2 ∧
    ∀ i<K, ¬∃ d : ℕ, (ceilSqrt (p*q)+i)^2=p*q+d^2 := by
  obtain ⟨wpos,wide,below,close,area,distance⟩ := win
  obtain ⟨lo,hi,pp⟩ := partner_data hp
  unfold lower at lo
  unfold upper at hi
  have scale : 4*(U/4)=U := by decide +kernel
  have lowerP : 3*(U/4)≤p := by omega
  have pq : p<q := by omega
  have proper : 6<p := (by decide +kernel : 6<3*(U/4)).trans_le lowerP
  have pbits : 2^1023≤p := (by decide +kernel : 2^1023≤3*(U/4)).trans lowerP
  have full : 2^2047≤p*q := (by decide +kernel : 2^2047≤3*(U/4)*(3*(U/4))).trans
    (Nat.mul_le_mul lowerP (lowerP.trans pq.le))
  have top : p*q<2^2048 := (Nat.mul_lt_mul_of_pos_right (pq.trans below) qp.pos).trans_le
    ((Nat.mul_le_mul_left U below.le).trans (by decide +kernel))
  have op := pp.odd_of_ne_two (by omega)
  have oq := qp.odd_of_ne_two (by omega)
  have cp : p.Coprime 6 := pp.coprime_iff_not_dvd.mpr (fun h => (not_le_of_gt proper) (Nat.le_of_dvd (by decide) h))
  have thin : (U-p)*(U-q)<4*U := calc
    _ < (4*W)*(U-q) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    _ = 4*(W*(U-q)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ area
  have split := (EndpointOffsetProduct.probe_iff cp pp.one_lt pq.le below.le).mpr
    (thin.trans_le (by simpa only [Nat.mul_comm U] using Nat.mul_le_mul_right U (stride_floor op oq)))
  let m := (p+q)/2
  let d := (q-p)/2
  have pmod := pp.eq_two_or_odd.resolve_left (by omega)
  have qmod := qp.eq_two_or_odd.resolve_left (by omega)
  have pm : p+d=m := by dsimp [d,m]; omega
  have qm : m+d=q := by dsimp [d,m]; omega
  have mid : p+q=2*m := by omega
  have double : 23*W≤16*d := by omega
  have dsq : 2*W^2 ≤ d^2 := by
    have sq := Nat.pow_le_pow_left double 2
    nlinarith only [sq,Nat.zero_le (W^2)]
  have cost : 2*K*m ≤ d^2 := calc
    _ ≤ 2*K*U := Nat.mul_le_mul_left _ (by omega)
    _ = 2*(U*K) := by ring
    _ ≤ 2*W^2 := Nat.mul_le_mul_left 2 distance
    _ ≤ _ := dsq
  have identity : m^2=p*q+d^2 := by
    calc
      m^2=(p+d)^2 := congrArg (·^2) pm.symm
      _ = p*((p+d)+d)+d^2 := by ring
      _ = _ := by rw [pm,qm]
  have wmul := Nat.mul_le_mul_right W (by omega : W≤U)
  have kbound : K≤W := Nat.le_of_mul_le_mul_left
    (distance.trans (by simpa only [pow_two,Nat.mul_comm] using wmul)) (by decide +kernel : 0<U)
  have lm : m-K+K=m := Nat.sub_add_cancel (by omega)
  have first : ceilSqrt (p*q) ≤ m-K := by
    apply ceilSqrt_le_iff.mpr
    rw [←lm] at identity cost
    nlinarith only [identity,cost,Nat.zero_le (K^2)]
  exact ⟨pbits,pq,below,full,top,split,by omega,
    fun _ hi => ordinary_miss pp qp (by omega) pq mid (by omega)⟩

/-- Distinct p give distinct product integers at each fixed prime q. -/
theorem count (W q : ℕ) (qp : q.Prime) : (products W q).card=(partners W).card := by
  unfold products
  exact card_image_of_injOn fun _ _ _ _ eq => Nat.eq_of_mul_eq_mul_right qp.pos eq

/-- Only the published lower bound on the one interval is used here. -/
theorem partner_count {W : ℕ} (big : 2^530≤W) (wide : 16*W≤U)
    (schoenfeld : upper W-lower W ≤ 710*((partners W).card+57*2^512)) :
    W < 1024*(partners W).card := by
  have width : upper W-lower W=W-1 := by unfold upper lower; omega
  rw [width] at schoenfeld
  omega

theorem estimate {W : ℕ} (C : InteriorBatchPopulation.Counts)
    (big : 2^530≤W) (wide : 16*W≤U) : W < 1024*(partners W).card := by
  apply partner_count big wide
  apply C.lower
  · change U/2≤lower W
    unfold lower
    have : U=2*(U/2) := by decide +kernel
    omega
  · unfold lower upper
    omega
  · change upper W≤U
    unfold upper
    omega

/-- All choices of smaller and larger prime are independent in this
Cartesian product, and unique factorization makes the map injective. -/
noncomputable def population (W : ℕ) (anchors : Finset ℕ) :=
  ((partners W) ×ˢ anchors).image fun z => z.1*z.2

theorem population_count {W K : ℕ} {anchors : Finset ℕ}
    (eligible : ∀ q∈anchors, q.Prime ∧ Window W K q) :
    (population W anchors).card=(partners W).card*anchors.card := by
  have injective : Set.InjOn (fun z : ℕ×ℕ => z.1*z.2) (((partners W) ×ˢ anchors : Finset _) : Set _) := by
    rintro ⟨p,q⟩ hz ⟨r,s⟩ hw eq
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hz
    obtain ⟨hr,hs⟩ := Finset.mem_product.mp hw
    obtain ⟨qp,wq⟩ := eligible q hq
    obtain ⟨sp,ws⟩ := eligible s hs
    have pq := (comparison wq qp hp).2.1
    have rs := (comparison ws sp hr).2.1
    have ordered := ordered_semiprime_pair_unique (partner_data hr).2.2 sp rs.le pq.le
      (partner_data hp).2.2.one_lt eq
    exact Prod.ext ordered.1 ordered.2
  unfold population
  rw [card_image_of_injOn injective, card_product]

private theorem eligible_window {W K b q : ℕ} (below : q<U) (close : U-q≤b)
    (wpos : 0<W) (wide : 16*W≤U) (near : 8*b≤W) (area : W*b≤U) (cost : U*K≤W^2) :
    Window W K q := ⟨wpos,wide,below,(Nat.mul_le_mul_left 8 close).trans near,
      (Nat.mul_le_mul_left W close).trans area,cost⟩

/-- For an upper-end offset of at most 55 bits, each individual product
splits while the ordinary search misses at least 2^914 midpoint tests. -/
theorem window55 {q : ℕ} (below : q<U) (close : U-q≤2^55) : Window (2^969) (2^914) q :=
  eligible_window below close (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- A common interval for all offsets up to 60 bits. -/
theorem window60 {q : ℕ} (below : q<U) (close : U-q≤2^60) : Window (2^964) (2^904) q :=
  eligible_window below close (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem partners55 (C : InteriorBatchPopulation.Counts) : 2^959 < (partners (2^969)).card := by
  have h := estimate (W:=2^969) C (by decide +kernel) (by decide +kernel)
  omega

theorem partners60 (C : InteriorBatchPopulation.Counts) : 2^954 < (partners (2^964)).card := by
  have h := estimate (W:=2^964) C (by decide +kernel) (by decide +kernel)
  omega

/-- Success of the actual probe on a balanced 2048-bit product, with the
first K ordinary Fermat discriminants all nonsquare. -/
def Recovered (n K : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2^1023≤p ∧ p<q ∧ q<U ∧
    2^2047≤n ∧ n<2^2048 ∧ p*q=n ∧ EndpointOffsetProduct.probe U n=some (p,q) ∧
    ∀ i<K, ¬∃ d : ℕ, (ceilSqrt n+i)^2=n+d^2

private theorem recover_partner {W K p q : ℕ} (win : Window W K q) (qp : q.Prime)
    (hp : p∈partners W) : Recovered (p*q) K := by
  obtain ⟨pw,lt,qu,full,bits,split,_,miss⟩ := comparison win qp hp
  exact ⟨p,q,(partner_data hp).2.2,qp,pw,lt,qu,full,bits,rfl,split,miss⟩

/-- More than 2^959 distinct inputs for the closer certified prime. -/
theorem certified_single (C : InteriorBatchPopulation.Counts) :
    let q := U-NearEndpointPrimes.smallerOffset
    2^959 < (products (2^969) q).card ∧ ∀ n∈products (2^969) q, Recovered n (2^914) := by
  let q := U-NearEndpointPrimes.smallerOffset
  have prime : q.Prime := NearEndpointPrimes.smallerOffset_prime
  have win : Window (2^969) (2^914) q := window55 (by decide +kernel) (by decide +kernel)
  change 2^959 < (products (2^969) q).card ∧ _
  refine ⟨(partners55 C).trans_eq (count _ q prime).symm,?_⟩
  rintro n hn
  change n∈products (2^969) q at hn
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hn
  exact recover_partner win prime hp

/-- Either certified large prime can be chosen for every smaller prime in
the common window. The distinct-input count includes both choices. -/
noncomputable def certifiedAnchors : Finset ℕ :=
  {U-NearEndpointPrimes.smallerOffset,U-NearEndpointPrimes.largerOffset}

attribute [local irreducible] partners population certifiedAnchors

theorem certified_double (C : InteriorBatchPopulation.Counts) :
    2^955 < (population (2^964) certifiedAnchors).card ∧
    ∀ n∈population (2^964) certifiedAnchors, Recovered n (2^904) := by
  have eligible (q : ℕ) (hq : q∈certifiedAnchors) : q.Prime ∧ Window (2^964) (2^904) q := by
    simp only [certifiedAnchors,mem_insert,mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact ⟨NearEndpointPrimes.smallerOffset_prime, window60 (by decide +kernel) (by decide +kernel)⟩
    · exact ⟨NearEndpointPrimes.largerOffset_prime, window60 (by decide +kernel) (by decide +kernel)⟩
  constructor
  · rw [population_count eligible,show certifiedAnchors.card=2 by rw [certifiedAnchors]; decide +kernel]
    calc
      2^955 = 2^954*2 := by decide +kernel
      _ < _ := Nat.mul_lt_mul_of_pos_right (partners60 C) (by decide)
  · intro n hn
    rw [population] at hn
    obtain ⟨⟨p,q⟩,members,rfl⟩ := mem_image.mp hn
    obtain ⟨hp,hq⟩ := mem_product.mp members
    obtain ⟨prime,win⟩ := eligible q hq
    exact recover_partner win prime hp

end PrimeFactors.FixedEndpointPartners
