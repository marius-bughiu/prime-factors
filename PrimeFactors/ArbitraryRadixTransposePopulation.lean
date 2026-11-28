import PrimeFactors.TransposedBlockPopulation

/-! Coverage by all transpositions of two positive, distinct digits in an
integer radix. Both the radix and digits may be chosen for each product. -/

namespace PrimeFactors.ArbitraryRadixTransposePopulation

open Finset MixedPrefixSample TransposedRadixProducts
open scoped Classical
open private PrimeFactors.TransposedBlockPopulation.data PrimeFactors.TransposedBlockPopulation.matching
  from PrimeFactors.TransposedBlockPopulation
open private PrimeFactors.MixedPrefixSample.mem_primes from PrimeFactors.MixedPrefixSample

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible primes

noncomputable def family (B : ℕ) := eligible.filter fun z =>
  ∃ a b, 0<a ∧ a<b ∧ b<B ∧ z=factors B a b

theorem mem_family {B : ℕ} {z : ℕ×ℕ} : z∈family B ↔
    z∈eligible ∧ ∃ a b, 0<a ∧ a<b ∧ b<B ∧ z=factors B a b := mem_filter

attribute [local irreducible] family

/-- The full population of successes also allows a different radix at each product. -/
noncomputable def allRadices := eligible.filter fun z => ∃ B, z∈family B

theorem mem_all {z : ℕ×ℕ} : z∈allRadices ↔ ∃ B, z∈family B := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · rintro ⟨B,h⟩
    exact mem_filter.mpr ⟨(mem_family.mp h).1,B,h⟩

attribute [local irreducible] allRadices

theorem of_product {B a b : ℕ} {z : ℕ×ℕ} (ok : z∈eligible) (pos : 0<a)
    (lt : a<b) (digit : b<B) (eq : (B*a+b)*(B*b+a)=z.1*z.2) : z∈family B := by
  obtain ⟨hp,hq,pq⟩ := PrimeFactors.TransposedBlockPopulation.data ok
  have pp := (PrimeFactors.MixedPrefixSample.mem_primes.mp hp).2
  have qp := (PrimeFactors.MixedPrefixSample.mem_primes.mp hq).2
  have order : B*a+b≤B*b+a := by
    have delta : b-a≤B*(b-a) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (b-a) (by omega : 1≤B)
    have := Nat.mul_sub B b a
    have := Nat.mul_le_mul_left B lt.le
    omega
  have same := ordered_semiprime_pair_unique pp qp pq.le order (by omega) eq
  exact mem_family.mpr ⟨ok,a,b,pos,lt,digit,(Prod.ext same.1 same.2).symm⟩

theorem includes_even (B : ℕ) : TransposedBlockPopulation.family B ⊆ family B := by
  intro z hz
  obtain ⟨member,a,b,h,rfl⟩ := TransposedBlockPopulation.mem_family.mp hz
  obtain ⟨_,_,⟨i,ai⟩,_,lt,top⟩ := h
  exact mem_family.mpr ⟨member,a,b,by omega,lt,top,rfl⟩

/-- The prime inequalities imply 2^511 ≤ B < 2^1023. The lower endpoint
for the dyadic index is 511 when B itself need not be a power of two. -/
theorem radix_range {B : ℕ} {z : ℕ×ℕ} (hz : z∈family B) :
    2^511≤B ∧ B<2^1023 := by
  obtain ⟨m,a,b,pos,ab,top,rfl⟩ := mem_family.mp hz
  obtain ⟨l,r,_⟩ := PrimeFactors.TransposedBlockPopulation.data m
  have lo := (PrimeFactors.MixedPrefixSample.mem_primes.mp l).1.1
  have hi := (PrimeFactors.MixedPrefixSample.mem_primes.mp r).1.2
  change 2^1023≤B*a+b at lo
  change B*b+a<2*2^1023 at hi
  have sq : 2^1023<B*B := calc
    _ ≤ B*a+b := lo
    _ < B*(a+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
    _ ≤ B*B := Nat.mul_le_mul_left _ (by omega)
  constructor
  · by_contra! small
    have bound := Nat.mul_le_mul small.le small.le
    omega
  · have := Nat.mul_le_mul_left B (by omega : 2≤b)
    omega

theorem dyadic_index {B : ℕ} {z : ℕ×ℕ} (hz : z∈family B) : 511≤B.log2 ∧ B.log2≤1022 := by
  obtain ⟨lo,hi⟩ := radix_range hz
  have pos : B≠0 := by omega
  exact ⟨Nat.le_of_not_lt (fun h => (not_lt_of_ge lo) ((Nat.log2_lt pos).mp h)),
    Nat.le_of_lt_succ ((Nat.log2_lt pos).mpr hi)⟩

theorem matching_count (B : ℕ) : 2*(family B).card≤primes.card := by
  apply PrimeFactors.TransposedBlockPopulation.matching _ _ (TransposedBlockPopulation.partner B)
  intro z hz
  obtain ⟨member,a,b,ap,lt,up,rfl⟩ := mem_family.mp hz
  obtain ⟨l,r,ord⟩ := PrimeFactors.TransposedBlockPopulation.data member
  exact ⟨l,r,ord,TransposedBlockPopulation.partner_word (by omega) up,
    TransposedBlockPopulation.partner_word (by omega) (lt.trans up)⟩

private theorem digit_box (A : Finset (ℕ×ℕ)) (B L : ℕ)
    (code : ∀ z∈A, ∃ a b, a<b ∧ b<L ∧ z=factors B a b) : 2*A.card≤L*L := by
  let row (b : ℕ) := (range b).image (fun a => factors B a b)
  have cover : A⊆(range L).biUnion row := by
    intro z hz
    obtain ⟨a,b,ab,bl,rfl⟩ := code z hz
    exact mem_biUnion.mpr ⟨b,mem_range.mpr bl,mem_image.mpr ⟨a,mem_range.mpr ab,rfl⟩⟩
  have one : A.card ≤ ∑ b∈range L,b :=
    ((card_le_card cover).trans card_biUnion_le).trans
      (sum_le_sum fun b _ => card_image_le.trans_eq (card_range b))
  calc
    _ ≤ 2*∑ b∈range L,b := Nat.mul_le_mul_left _ one
    _ = L*(L-1) := (Nat.mul_comm ..).trans (sum_range_id_mul_two L)
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.sub_le ..)

/-- If 2^(1023-i)≤B then the larger digit must be below 2^(i+1), because
it is the leading digit of the larger 1,024-bit prime. -/
theorem digit_count {B i : ℕ} (range : i≤1023) (lower : 2^(1023-i)≤B) :
    2*(family B).card≤2^(i+1)*2^(i+1) := by
  apply digit_box _ B
  intro z hz
  obtain ⟨member,a,b,ap,ab,top,rfl⟩ := mem_family.mp hz
  refine ⟨a,b,ab,?_,rfl⟩
  have hi := (PrimeFactors.MixedPrefixSample.mem_primes.mp
    (PrimeFactors.TransposedBlockPopulation.data member).2.1).1.2
  change B*b+a<2*2^1023 at hi
  by_contra! le
  have bound := Nat.mul_le_mul lower le
  rw [←pow_add,show 1023-i+(i+1)=1024 by omega] at bound
  omega

private noncomputable def menu {α : Type*} [DecidableEq α] (I : Finset ℕ) (f : ℕ → Finset α) :=
  I.biUnion f

private theorem include_row {α : Type*} [DecidableEq α] (I : Finset ℕ) (f : ℕ → Finset α)
    {z : α} {B : ℕ} (row : B∈I) (hz : z∈f B) : z∈menu I f :=
  mem_biUnion.mpr ⟨B,row,hz⟩

private theorem menu_bound {α : Type*} [DecidableEq α] (I : Finset ℕ) (f : ℕ → Finset α)
    (C : ℕ) (bound : ∀ B∈I, 2*(f B).card≤C) : 2*(menu I f).card≤I.card*C := by
  calc
    _ ≤ 2*∑ B∈I,(f B).card := Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ B∈I,2*(f B).card := Finset.mul_sum ..
    _ ≤ ∑ _B∈I,C := sum_le_sum bound
    _ = _ := by simp

private def radices (k : ℕ) := Ico (2^k) (2^(k+1))

private theorem shell_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (i : ℕ)
    (small : i≤1023) (cost : ∀ B, 2^(1023-i)≤B → 2*(f B).card≤2^(i+1)*2^(i+1)) :
    2*(menu (radices (1023-i)) f).card ≤ 2^1025*2^i := by
  have rows := menu_bound (radices (1023-i)) f (2^(i+1)*2^(i+1))
    (fun B h => cost B (mem_Ico.mp h).1)
  have size (k : ℕ) : (radices k).card=2^k := by
    rw [radices,Nat.card_Ico,pow_succ]
    omega
  rw [size,←pow_add,←pow_add,show 1023-i+((i+1)+(i+1))=1025+i by omega] at rows
  rwa [pow_add] at rows

private theorem shell_cover {α : Type*} [DecidableEq α] (A : Finset α) (f : ℕ → Finset α)
    (H T : ℕ) (shell : ℕ → Finset ℕ)
    (hit : ∀ z∈A, ∃ B, z∈f B ∧ (B<H ∨ ∃ i<T, B∈shell i)) :
    A⊆menu (range H) f ∪ menu (range T) (fun i => menu (shell i) f) := by
  intro z hz
  obtain ⟨B,member,small|⟨i,il,within⟩⟩ := hit z hz
  · exact mem_union_left _ (include_row _ f (mem_range.mpr small) member)
  · exact mem_union_right _ (include_row _ _ (mem_range.mpr il) (include_row _ f within member))

private theorem index_cases {B : ℕ} (pos : 0<B) (top : B<2^1023) :
    B<2^517 ∨ ∃ i<507, B∈radices (1023-i) := by
  by_cases small : B<2^517
  · exact Or.inl small
  · have ktop := (Nat.log2_lt pos.ne').mpr top
    have klo : 517≤B.log2 := Nat.le_of_not_lt fun lt => small ((Nat.log2_lt pos.ne').mp lt)
    refine Or.inr ⟨1023-B.log2,by omega,?_⟩
    rw [show 1023-(1023-B.log2)=B.log2 by omega]
    exact mem_Ico.mpr ⟨Nat.log2_self_le pos.ne',Nat.lt_log2_self⟩

private theorem upper_count {α : Type*} [DecidableEq α] (A : Finset α) (f : ℕ → Finset α) (P : ℕ)
    (inside : ∀ z∈A, ∃ B, 0<B ∧ B<2^1023 ∧ z∈f B) (per : ∀ B, 2*(f B).card≤P)
    (tail : ∀ i≤506, 2*(menu (radices (1023-i)) f).card≤2^1025*2^i) :
    2*A.card≤2^517*P+2^1532 := by
  let H := menu (range (2^517)) f
  let T := menu (range 507) fun i => menu (radices (1023-i)) f
  have sub := shell_cover A f (2^517) 507 (fun i => radices (1023-i)) (by
    intro z hz
    obtain ⟨B,pos,top,member⟩ := inside z hz
    exact ⟨B,member,index_cases pos top⟩)
  have hcount : 2*H.card≤2^517*P := by
    simpa only [H,card_range] using menu_bound (range (2^517)) f P (fun B _ => per B)
  have geom (k : ℕ) : (∑ i∈range k,(2:ℕ)^i)+1=2^k := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ,pow_succ]; omega
  have tcount : 2*T.card≤2^1532 := calc
    _ ≤ 2*∑ i∈range 507,(menu (radices (1023-i)) f).card := Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ i∈range 507,2*(menu (radices (1023-i)) f).card := Finset.mul_sum ..
    _ ≤ ∑ i∈range 507,2^1025*2^i := sum_le_sum fun i hi => tail i (by have := mem_range.mp hi; omega)
    _ = 2^1025*∑ i∈range 507,2^i := (Finset.mul_sum ..).symm
    _ ≤ 2^1025*2^507 := Nat.mul_le_mul_left _ (by have := geom 507; omega)
    _ = _ := by decide +kernel
  have combined := (card_le_card sub).trans (card_union_le H T)
  omega

private theorem all_count : 2*allRadices.card ≤ 2^517*primes.card+2^1532 := by
  apply upper_count allRadices family primes.card _ matching_count
    (fun i hi => shell_bound family i (by omega) (fun B h => digit_count (by omega) h))
  intro z hz
  obtain ⟨B,hB⟩ := mem_all.mp hz
  obtain ⟨lo,hi⟩ := radix_range hB
  exact ⟨B,by omega,hi,hB⟩

private theorem price {A P U : ℕ} (size : 2*A≤2^517*P+2^1532)
    (marginal : X*P<41056*U) (population : 2^2046<21000000*U) : 2^490*A<U := by
  change 2^1023*P<41056*U at marginal
  omega

/-- Strict full-population bound, allowing every integer radix and both digit parities. -/
theorem fraction : 2^490*allRadices.card<eligible.card :=
  price (A:=allRadices.card) (P:=primes.card) (U:=eligible.card) all_count
    SquareRootPhasePopulation.marginal ChebyshevPrimeSample.eligible_count

end PrimeFactors.ArbitraryRadixTransposePopulation
