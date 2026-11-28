import PrimeFactors.ArbitraryRadixTransposePopulation

/-! Count full-width prime pairs expressible as a two-block reversal followed
by an additive offset. Each pair may choose its own radix and offset. -/

namespace PrimeFactors.OffsetTransposePopulation

open Finset MixedPrefixSample
open scoped Classical
open private PrimeFactors.TransposedBlockPopulation.data from PrimeFactors.TransposedBlockPopulation
open private PrimeFactors.MixedPrefixSample.mem_primes from PrimeFactors.MixedPrefixSample
open private PrimeFactors.ArbitraryRadixTransposePopulation.upper_count
  PrimeFactors.ArbitraryRadixTransposePopulation.shell_bound
  from PrimeFactors.ArbitraryRadixTransposePopulation

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible primes

def pair (B t a b : ℕ) : ℕ×ℕ := (B*a+b,B*b+a+t)

noncomputable def family (B t : ℕ) := eligible.filter fun z =>
  ∃ a b, 0<a ∧ a≤b ∧ b<B ∧ z=pair B t a b

theorem mem_family {B t : ℕ} {z : ℕ×ℕ} : z∈family B t ↔
    z∈eligible ∧ ∃ a b, 0<a ∧ a≤b ∧ b<B ∧ z=pair B t a b := mem_filter

attribute [local irreducible] family

/-- The product description and the ordered prime-pair description agree. -/
theorem of_product {B t a b : ℕ} {z : ℕ×ℕ} (member : z∈eligible) (ap : 0<a)
    (ab : a≤b) (top : b<B) (prod : (B*a+b)*(B*b+a+t)=z.1*z.2) : z∈family B t := by
  obtain ⟨hp,hq,pq⟩ := PrimeFactors.TransposedBlockPopulation.data member
  have diff : b-a≤B*(b-a) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (b-a) (by omega : 1≤B)
  have mul_sub := Nat.mul_sub B b a
  have ord := Nat.mul_le_mul_left B ab
  have small := Nat.mul_le_mul_left B (show 1≤a from ap)
  simp only [Nat.mul_one] at small
  have same := ordered_semiprime_pair_unique (PrimeFactors.MixedPrefixSample.mem_primes.mp hp).2
    (PrimeFactors.MixedPrefixSample.mem_primes.mp hq).2 pq.le (by omega : B*a+b≤B*b+a+t)
    (by omega : 1<B*a+b) prod
  exact mem_family.mpr ⟨member,a,b,ap,ab,top,(Prod.ext same.1 same.2).symm⟩

private theorem graph_count (A : Finset (ℕ×ℕ)) (f : ℕ → ℕ)
    (rows : ∀ z∈A, z.1∈primes ∧ z.2=f z.1) : A.card≤primes.card := by
  apply card_le_card_of_injOn Prod.fst (fun z h => (rows z h).1)
  intro x hx y hy eq
  exact Prod.ext eq ((rows x hx).2.trans ((congrArg f eq).trans (rows y hy).2.symm))

/-- For each fixed radix and offset the smaller prime determines the larger. -/
theorem count (B t : ℕ) : (family B t).card≤primes.card := by
  apply graph_count _ (fun p => TransposedBlockPopulation.partner B p+t)
  intro z hz
  obtain ⟨member,a,b,ap,ab,top,rfl⟩ := mem_family.mp hz
  refine ⟨(PrimeFactors.TransposedBlockPopulation.data member).1,?_⟩
  change B*b+a+t=TransposedBlockPopulation.partner B (B*a+b)+t
  rw [TransposedBlockPopulation.partner_word (by omega) top]

/-- A radix at least 2^k forces both leading blocks below the factor-width
quotient, including when the two blocks coincide. -/
theorem digits {B t a b k : ℕ} (hk : k≤1024) (lo : 2^k≤B) (ab : a≤b)
    (hi : B*b+a+t<2^1024) : a<2^(1024-k) ∧ b<2^(1024-k) := by
  suffices small : b<2^(1024-k) from ⟨ab.trans_lt small,small⟩
  by_contra! large
  have bound := Nat.mul_le_mul lo large
  rw [←pow_add,show k+(1024-k)=1024 by omega] at bound
  omega

/-- For b below L there are at most 1+2+⋯+(L−1) choices of positive a≤b. -/
private theorem digit_box {B t L : ℕ}
    (within : ∀ z∈family B t, ∃ a b, 0<a ∧ a≤b ∧ b<L ∧ z=pair B t a b) :
    2*(family B t).card ≤ L*L := by
  let row (b : ℕ) := (range b).image fun i => pair B t (i+1) b
  have cover : family B t⊆(range L).biUnion row := by
    intro z hz
    obtain ⟨a,b,ap,ab,bl,rfl⟩ := within z hz
    exact mem_biUnion.mpr ⟨b,mem_range.mpr bl,mem_image.mpr
      ⟨a-1,mem_range.mpr (by omega),by rw [show a-1+1=a by omega]⟩⟩
  have one : (family B t).card ≤ ∑ b∈range L,b :=
    ((card_le_card cover).trans card_biUnion_le).trans
      (sum_le_sum fun b _ => card_image_le.trans_eq (card_range b))
  calc
    _ ≤ 2*∑ b∈range L,b := Nat.mul_le_mul_left _ one
    _ = L*(L-1) := (Nat.mul_comm ..).trans (sum_range_id_mul_two L)
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.sub_le ..)

theorem digit_count {B t k : ℕ} (hk : k≤1024) (lo : 2^k≤B) :
    2*(family B t).card≤2^(1024-k)*2^(1024-k) := by
  apply digit_box
  intro z hz
  obtain ⟨member,a,b,ap,ab,_,rfl⟩ := mem_family.mp hz
  have hi := (PrimeFactors.MixedPrefixSample.mem_primes.mp
    (PrimeFactors.TransposedBlockPopulation.data member).2.1).1.2
  exact ⟨a,b,ap,ab,(digits hk lo ab hi).2,rfl⟩

noncomputable def allRadices (t : ℕ) := eligible.filter fun z => ∃ B, z∈family B t

theorem mem_all {t : ℕ} {z : ℕ×ℕ} : z∈allRadices t ↔ ∃ B, z∈family B t := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · rintro ⟨B,h⟩
    exact mem_filter.mpr ⟨(mem_family.mp h).1,B,h⟩

attribute [local irreducible] allRadices

/-- The largest radices force both positive digits to be one. Taken together
they add at most one partner for each first prime. -/
theorem large_radix {B t : ℕ} {z : ℕ×ℕ} (wide : 2^1023≤B) (member : z∈family B t) :
    z.2=z.1+t := by
  obtain ⟨eligible',a,b,ap,ab,_,rfl⟩ := mem_family.mp member
  have hi := (PrimeFactors.MixedPrefixSample.mem_primes.mp
    (PrimeFactors.TransposedBlockPopulation.data eligible').2.1).1.2
  have small := (digits (by decide : 1023≤1024) wide ab hi).2
  have bb : b=1 := by change b<2 at small; omega
  have aa : a=1 := by omega
  simp only [pair,aa,bb]

private theorem all_count (t : ℕ) :
    2*(allRadices t).card≤(2^517+1)*(2*primes.card)+2^1532 := by
  let small := (allRadices t).filter fun z => ∃ B<2^1023, z∈family B t
  let diagonal := eligible.filter fun z => z.2=z.1+t
  have head : 2*small.card≤2^517*(2*primes.card)+2^1532 := by
    refine PrimeFactors.ArbitraryRadixTransposePopulation.upper_count small (fun B => family B t)
      (2*primes.card) ?_ (fun B => Nat.mul_le_mul_left _ (count B t)) ?_
    · intro z hz
      obtain ⟨B,top,mem⟩ := (mem_filter.mp hz).2
      obtain ⟨_,a,b,ap,ab,bl,_⟩ := mem_family.mp mem
      exact ⟨B,by omega,top,mem⟩
    · intro i hi
      apply PrimeFactors.ArbitraryRadixTransposePopulation.shell_bound _ _ (by omega)
      intro B lower
      have b := digit_count (t:=t) (by omega : 1023-i≤1024) lower
      rwa [show 1024-(1023-i)=i+1 by omega] at b
  have diag : diagonal.card≤primes.card := by
    apply graph_count _ (fun p => p+t)
    intro z hz
    obtain ⟨ok,hz⟩ := mem_filter.mp hz
    exact ⟨(PrimeFactors.TransposedBlockPopulation.data ok).1,hz⟩
  have sub : allRadices t⊆small∪diagonal := by
    intro z hz
    obtain ⟨B,h⟩ := mem_all.mp hz
    by_cases below : B<2^1023
    · exact mem_union_left _ (mem_filter.mpr ⟨hz,B,below,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨(mem_family.mp h).1,large_radix (by omega) h⟩)
  have full := (card_le_card sub).trans (card_union_le small diagonal)
  omega

private theorem price {A P U : ℕ} (size : 2*A≤(2^517+1)*(2*P)+2^1532)
    (marginal : X*P<41056*U) (population : 2^2046<21000000*U) : 3*2^488*A<U := by
  change 2^1023*P<41056*U at marginal
  omega

/-- Each fixed offset covers less than one in 3·2^488 of all eligible products,
even when the radix may depend on the product. -/
theorem fraction (t : ℕ) : 3*2^488*(allRadices t).card<eligible.card :=
  price (A:=(allRadices t).card) (P:=primes.card) (U:=eligible.card) (all_count t)
    SquareRootPhasePopulation.marginal ChebyshevPrimeSample.eligible_count

noncomputable def bounded (T : ℕ) := (range (T+1)).biUnion allRadices

theorem mem_bounded {T : ℕ} {z : ℕ×ℕ} :
    z∈bounded T ↔ ∃ t≤T, ∃ B, z∈family B t := by
  simp only [bounded,mem_biUnion,mem_range,Nat.lt_succ_iff,mem_all]

/-- Offsets 0 through T and all radices are allowed together. -/
theorem bounded_fraction (T : ℕ) : 3*2^488*(bounded T).card<(T+1)*eligible.card := calc
  _ ≤ 3*2^488*∑ t∈range (T+1),(allRadices t).card := Nat.mul_le_mul_left _ card_biUnion_le
  _ = ∑ t∈range (T+1),3*2^488*(allRadices t).card := Finset.mul_sum ..
  _ < ∑ _t∈range (T+1),eligible.card := sum_lt_sum_of_nonempty
    ⟨0,mem_range.mpr (by omega)⟩ (fun t _ => fraction t)
  _ = _ := by simp

/-- More than 2^128 offset choices still cover fewer than one in 2^361. -/
theorem offsets128 : 2^361*(bounded (2^128)).card<eligible.card := by
  apply Nat.lt_of_mul_lt_mul_left (a:=2^128+1)
  calc
    _ = ((2^128+1)*2^361)*(bounded (2^128)).card := (Nat.mul_assoc ..).symm
    _ ≤ 3*2^488*(bounded (2^128)).card := Nat.mul_le_mul_right _ (by decide +kernel)
    _ < _ := bounded_fraction _

end PrimeFactors.OffsetTransposePopulation
