import PrimeFactors.MonotoneClosePrimeLower

/-! An arbitrary assignment of full-width primes to a bounded number of
labels necessarily creates equal-label pairs among genuine full-width products. -/

namespace PrimeFactors.FiniteBinCollisionPopulation

open Finset MixedPrefixSample
open private PrimeFactors.FirstSumMenuPopulation.collision_count PrimeFactors.FirstSumMenuPopulation.prime_pairs
  from PrimeFactors.FirstSumMenuPopulation
open private PrimeFactors.MonotoneClosePrimeLower.prime_ratio
  PrimeFactors.MonotoneClosePrimeLower.many_bins from PrimeFactors.MonotoneClosePrimeLower
open private PrimeFactors.MixedPrefixSample.mem_upper PrimeFactors.MixedPrefixSample.product_lower
  PrimeFactors.MixedPrefixSample.mem_sample from PrimeFactors.MixedPrefixSample

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192
attribute [local irreducible] sample eligible primes upperPrimes

private theorem upper_eligible {p q : ℕ} (pU : p∈upperPrimes) (qU : q∈upperPrimes)
    (sort : p<q) : (p,q)∈eligible := by
  obtain ⟨pP,pl⟩ := PrimeFactors.MixedPrefixSample.mem_upper.mp pU
  obtain ⟨qP,ql⟩ := PrimeFactors.MixedPrefixSample.mem_upper.mp qU
  rw [eligible]
  exact PrimeFactors.MixedPrefixSample.mem_sample.mpr
    ⟨mem_ordered.mpr ⟨pP,qP,sort.ne,PrimeFactors.MixedPrefixSample.product_lower pl ql,trivial⟩,sort⟩

private theorem collision_bound (A E : Finset (ℕ×ℕ)) (P : Finset ℕ) (key : ℕ→ℕ)
    (source : A=(P ×ˢ P).filter (fun z => key z.1=key z.2))
    (covers : ∀ p∈P, ∀ q∈P, p<q → key p=key q → (p,q)∈E) :
    A.card≤2*E.card+P.card := by
  classical
  have sub : A⊆(E ∪ E.image Prod.swap) ∪ P.diag := by
    rintro ⟨p,q⟩ hm
    rw [source] at hm
    obtain ⟨members,same⟩ := mem_filter.mp hm
    obtain ⟨pP,qP⟩ := mem_product.mp members
    change key p=key q at same
    rcases lt_trichotomy p q with h|h|h
    · exact mem_union_left _ (mem_union_left _ (covers p pP q qP h same))
    · exact mem_union_right _ (mem_diag.mpr ⟨pP,h⟩)
    · exact mem_union_left _ (mem_union_right _
        (mem_image.mpr ⟨(q,p),covers q qP p pP h same.symm,rfl⟩))
  have outer := (card_le_card sub).trans (card_union_le ..)
  have inner := card_union_le E (E.image Prod.swap)
  have flipped : (E.image Prod.swap).card≤E.card := card_image_le
  rw [diag_card] at outer
  omega

private theorem price {H P C T b : ℕ} (collision : H^2≤b*(2*T+H)) (many : 1000*b≤H)
    (marginal : 100*P<631*H) (pairs : 2*C≤P^2) : C<40*b*T := by
  have diag := Nat.mul_le_mul_right H many
  have cap : 999*H^2 ≤ 2000*b*T := by nlinarith only [collision,diag]
  have sq := Nat.pow_lt_pow_left marginal (by decide : 2≠0)
  nlinarith only [pairs,sq,cap,Nat.zero_le (b*T)]

/-- Events containing all sorted equal-label pairs of upper-interval primes
cover strictly more than one in 40b eligible products, even if the labels
are assigned adversarially. -/
theorem fraction {b : ℕ} (key : ℕ→ℕ) (limit : b≤65536)
    (bounded : ∀ p∈upperPrimes, key p<b) (E : Finset (ℕ×ℕ))
    (covers : ∀ p∈upperPrimes, ∀ q∈upperPrimes, p<q → key p=key q → (p,q)∈E) :
    eligible.card < 40*b*E.card := by
  have coll := PrimeFactors.FirstSumMenuPopulation.collision_count upperPrimes key b bounded
  have cap := collision_bound _ E upperPrimes key rfl covers
  have many := (Nat.mul_le_mul_left 1000 limit).trans
    ((show 1000*65536 ≤ 1000*2^510 by decide +kernel).trans
      PrimeFactors.MonotoneClosePrimeLower.many_bins)
  exact price (coll.trans (Nat.mul_le_mul_left _ cap)) many
    PrimeFactors.MonotoneClosePrimeLower.prime_ratio PrimeFactors.FirstSumMenuPopulation.prime_pairs

private theorem encode_bins {α : Type*} (B : Finset α) (key : ℕ→α) (P : Finset ℕ)
    (bounded : ∀ p∈P, key p∈B) :
    ∃ index : ℕ→ℕ, (∀ p∈P, index p<B.card) ∧
      ∀ p∈P, ∀ q∈P, index p=index q → key p=key q := by
  classical
  let e : B ≃ Fin B.card := Fintype.equivFinOfCardEq (Fintype.card_coe _)
  let index (p : ℕ) : ℕ := if h : key p∈B then (e ⟨key p,h⟩).val else 0
  refine ⟨index,?_,?_⟩
  · intro p hp
    simpa only [index,dif_pos (bounded p hp)] using (e ⟨key p,bounded p hp⟩).isLt
  · intro p hp q hq eq
    simp only [index,dif_pos (bounded p hp),dif_pos (bounded q hq)] at eq
    exact congrArg Subtype.val (e.injective (Fin.ext eq))

/-- The same unconditional lower bound for a classifier into an explicit
finite set of labels, of any type. -/
theorem fraction_bins {α : Type*} (B : Finset α) (key : ℕ→α) (limit : B.card≤65536)
    (bounded : ∀ p∈upperPrimes, key p∈B) (E : Finset (ℕ×ℕ))
    (covers : ∀ p∈upperPrimes, ∀ q∈upperPrimes, p<q → key p=key q → (p,q)∈E) :
    eligible.card < 40*B.card*E.card := by
  obtain ⟨index,bound,same⟩ := encode_bins B key upperPrimes bounded
  exact fraction index limit bound E fun p hp q hq lt eq => covers p hp q hq lt (same p hp q hq eq)

/-- The guaranteed pairs themselves are eligible, even if the event set
also contains unrelated pairs. -/
theorem eligible_fraction {α : Type*} (B : Finset α) (key : ℕ→α) (limit : B.card≤65536)
    (bounded : ∀ p∈upperPrimes, key p∈B) (E : Finset (ℕ×ℕ))
    (covers : ∀ p∈upperPrimes, ∀ q∈upperPrimes, p<q → key p=key q → (p,q)∈E) :
    eligible.card < 40*B.card*(eligible ∩ E).card :=
  fraction_bins B key limit bounded _ fun p hp q hq h eq =>
    mem_inter.mpr ⟨upper_eligible hp hq h,covers p hp q hq h eq⟩

/-- Both factors in this band guarantee a full-width product. At least one
factor of any eligible product belongs to it. -/
noncomputable def upperBand := primes.filter fun p => 2*X^2≤p*p

theorem mem_band {p : ℕ} : p∈upperBand ↔ p∈primes ∧ 2*X^2≤p*p := mem_filter

theorem upper_subset : upperPrimes⊆upperBand := by
  intro p hp
  obtain ⟨pp,pl⟩ := PrimeFactors.MixedPrefixSample.mem_upper.mp hp
  exact mem_band.mpr ⟨pp,PrimeFactors.MixedPrefixSample.product_lower pl pl⟩

theorem band_pair_eligible {p q : ℕ} (pU : p∈upperBand) (qU : q∈upperBand)
    (order : p<q) : (p,q)∈eligible := by
  rw [eligible]
  exact PrimeFactors.MixedPrefixSample.mem_sample.mpr ⟨mem_ordered.mpr
    ⟨(mem_band.mp pU).1,(mem_band.mp qU).1,order.ne,
      (mem_band.mp pU).2.trans (Nat.mul_le_mul_left p order.le),trivial⟩,order⟩

attribute [local irreducible] upperBand

private theorem incident_count (A : Finset (ℕ×ℕ)) (P U : Finset ℕ) (sub : U⊆P)
    (row : ∀ z∈A, z.1∈P ∧ z.2∈P ∧ (z.1∈U ∨ z.2∈U)) :
    A.card+U.card^2≤2*P.card*U.card := by
  have cover : A⊆(P ×ˢ U) ∪ (U ×ˢ P) := by
    intro z hz
    obtain ⟨p,q,h|h⟩ := row z hz
    · exact mem_union_right _ (mem_product.mpr ⟨h,q⟩)
    · exact mem_union_left _ (mem_product.mpr ⟨p,h⟩)
  have overlap : (P ×ˢ U) ∩ (U ×ˢ P)=U ×ˢ U := by
    ext z
    simp only [mem_inter,mem_product]
    exact ⟨fun h => ⟨h.2.1,h.1.2⟩,fun h => ⟨⟨sub h.1,h.2⟩,⟨h.1,sub h.2⟩⟩⟩
  have identity := card_union_add_card_inter (P ×ˢ U) (U ×ˢ P)
  rw [overlap,card_product,card_product,card_product,Nat.mul_comm U.card P.card] at identity
  have small := card_le_card cover
  rw [pow_two, two_mul, Nat.add_mul]
  omega

private theorem eligible_incidence :
    2*eligible.card+upperBand.card^2≤2*primes.card*upperBand.card := by
  have h := incident_count (ordered fun _ => True) primes upperBand (fun _ hx => (mem_band.mp hx).1) (by
    intro z hz
    obtain ⟨p,q,_,big,_⟩ := mem_ordered.mp hz
    refine ⟨p,q,?_⟩
    rcases le_total z.1 z.2 with le|le
    · exact Or.inr (mem_band.mpr ⟨q,big.trans (Nat.mul_le_mul_right _ le)⟩)
    · exact Or.inl (mem_band.mpr ⟨p,big.trans (Nat.mul_le_mul_left _ le)⟩))
  rwa [two_orders,←eligible] at h

private theorem band_price {U P C T b : ℕ} (collision : U^2≤b*(2*T+U))
    (many : 1000*b≤U) (marginal : 100*P<631*U) (pairs : 2*C+U^2≤2*P*U) :
    C<12*b*T := by
  have diag := Nat.mul_le_mul_right U many
  have cap : 999*U^2 ≤ 2000*b*T := by nlinarith only [collision,diag]
  have weighted := Nat.mul_lt_mul_of_pos_right marginal (show 0<U by omega)
  nlinarith only [pairs,weighted,cap,Nat.zero_le (b*T)]

/-- A stronger lower bound for classifiers available throughout upperBand.
In counting all eligible pairs, the overlap between the two possible upper
endpoints is subtracted exactly. -/
theorem band_fraction_bins {α : Type*} (B : Finset α) (key : ℕ→α) (limit : B.card≤65536)
    (bounded : ∀ p∈upperBand, key p∈B) (E : Finset (ℕ×ℕ))
    (covers : ∀ p∈upperBand, ∀ q∈upperBand, p<q → key p=key q → (p,q)∈E) :
    eligible.card < 12*B.card*E.card := by
  obtain ⟨index,bound,same⟩ := encode_bins B key upperBand bounded
  have coll := PrimeFactors.FirstSumMenuPopulation.collision_count upperBand index B.card bound
  have cap := collision_bound _ E upperBand index rfl
    (fun p hp q hq lt eq => covers p hp q hq lt (same p hp q hq eq))
  have sub := card_le_card upper_subset
  have many := (Nat.mul_le_mul_left 1000 limit).trans
    ((show 1000*65536 ≤ 1000*2^510 by decide +kernel).trans
      (PrimeFactors.MonotoneClosePrimeLower.many_bins.trans sub))
  exact band_price (coll.trans (Nat.mul_le_mul_left _ cap)) many
    (PrimeFactors.MonotoneClosePrimeLower.prime_ratio.trans_le (Nat.mul_le_mul_left _ sub))
    eligible_incidence

theorem band_eligible_fraction {α : Type*} (B : Finset α) (key : ℕ→α) (limit : B.card≤65536)
    (bounded : ∀ p∈upperBand, key p∈B) (E : Finset (ℕ×ℕ))
    (covers : ∀ p∈upperBand, ∀ q∈upperBand, p<q → key p=key q → (p,q)∈E) :
    eligible.card < 12*B.card*(eligible ∩ E).card :=
  band_fraction_bins B key limit bounded _ fun p hp q hq h eq =>
    mem_inter.mpr ⟨band_pair_eligible hp hq h,covers p hp q hq h eq⟩

end PrimeFactors.FiniteBinCollisionPopulation
