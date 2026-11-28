import PrimeFactors.TransposedRadixProducts
import PrimeFactors.SquareRootPhasePopulation
import PrimeFactors.FactorSum

/-! Population bounds for two primes whose two digits are transposed
in a supplied radix. Each radix pairs off primes without reusing either endpoint. -/

namespace PrimeFactors.TransposedBlockPopulation

open Finset MixedPrefixSample TransposedRadixProducts
open scoped Classical
open private PrimeFactors.MixedPrefixSample.mem_sample PrimeFactors.MixedPrefixSample.mem_primes
  from PrimeFactors.MixedPrefixSample

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible primes ordered sample

noncomputable def family (B : ℕ) := eligible.filter fun z =>
  ∃ a b, Valid B a b ∧ z=factors B a b

theorem mem_family {B : ℕ} {z : ℕ×ℕ} : z∈family B ↔
    z∈eligible ∧ ∃ a b, Valid B a b ∧ z=factors B a b := mem_filter

attribute [local irreducible] family

private theorem data {z : ℕ×ℕ} (hz : z∈eligible) :
    z.1∈primes ∧ z.2∈primes ∧ z.1<z.2 := by
  rw [eligible] at hz
  obtain ⟨base,order⟩ := PrimeFactors.MixedPrefixSample.mem_sample.mp hz
  exact ⟨(mem_ordered.mp base).1,(mem_ordered.mp base).2.1,order⟩

/-- On eligible semiprimes the recognizer succeeds exactly on this family. -/
theorem recognition {B : ℕ} {z : ℕ×ℕ} (member : z∈eligible) :
    (recognize B (z.1*z.2)).isSome=true ↔ z∈family B := by
  rw [recognizes_iff,mem_family]
  constructor
  · rintro ⟨a,b,ok,prod⟩
    obtain ⟨hp,hq,sorted⟩ := data member
    have pp := (PrimeFactors.MixedPrefixSample.mem_primes.mp hp).2
    have qp := (PrimeFactors.MixedPrefixSample.mem_primes.mp hq).2
    have br := ok.1
    have ab := ok.2.2.2.2.1
    obtain ⟨i,ai⟩ := ok.2.2.1
    have ba : 1≤a := by omega
    have nontriv : 1<B*a+b := by
      have := Nat.mul_le_mul_left B ba
      simp only [Nat.mul_one] at this
      omega
    have order : B*a+b≤B*b+a := by
      have diff : b-a≤B*(b-a) := by
        simpa only [one_mul] using Nat.mul_le_mul_right (b-a) (by omega : 1≤B)
      have linear := Nat.mul_sub B b a
      have mult := Nat.mul_le_mul_left B ab.le
      omega
    have same := ordered_semiprime_pair_unique pp qp sorted.le order nontriv prod
    exact ⟨member,a,b,ok,(Prod.ext same.1 same.2).symm⟩
  · rintro ⟨_,a,b,ok,rfl⟩
    exact ⟨a,b,ok,rfl⟩

/-- Interchanging the two base-B digits of a factor determines its partner. -/
def partner (B x : ℕ) := B*(x%B)+x/B

theorem partner_word {B a b : ℕ} (pos : 0<B) (digit : b<B) :
    partner B (B*a+b)=B*b+a := by
  simp [partner,Nat.mul_add_div pos,Nat.mul_add_mod,Nat.div_eq_of_lt digit,Nat.mod_eq_of_lt digit]

private theorem rows {B : ℕ} {z : ℕ×ℕ} (hz : z∈family B) :
    z.1∈primes ∧ z.2∈primes ∧ z.1<z.2 ∧ partner B z.1=z.2 ∧ partner B z.2=z.1 := by
  obtain ⟨eligible',a,b,h,rfl⟩ := mem_family.mp hz
  obtain ⟨l,r,order⟩ := data eligible'
  obtain ⟨radix,_,_,_,lt,up⟩ := h
  exact ⟨l,r,order,partner_word (by omega) up,partner_word (by omega) (lt.trans up)⟩

private theorem matching (S : Finset (ℕ×ℕ)) (P : Finset ℕ) (f : ℕ → ℕ)
    (row : ∀ z∈S, z.1∈P ∧ z.2∈P ∧ z.1<z.2 ∧ f z.1=z.2 ∧ f z.2=z.1) :
    2*S.card≤P.card := by
  have left : (S:Set (ℕ×ℕ)).InjOn Prod.fst := by
    intro x hx y hy eq
    exact Prod.ext eq (((row x hx).2.2.2.1).symm.trans ((congrArg f eq).trans (row y hy).2.2.2.1))
  have right : (S:Set (ℕ×ℕ)).InjOn Prod.snd := by
    intro x hx y hy eq
    exact Prod.ext (((row x hx).2.2.2.2).symm.trans ((congrArg f eq).trans (row y hy).2.2.2.2)) eq
  have dis : Disjoint (S.image Prod.fst) (S.image Prod.snd) := by
    apply disjoint_left.mpr
    intro t h₁ h₂
    obtain ⟨x,hx,xval⟩ := mem_image.mp h₁
    obtain ⟨y,hy,yval⟩ := mem_image.mp h₂
    have same : x.1=y.2 := xval.trans yval.symm
    have other := ((row x hx).2.2.2.1).symm.trans ((congrArg f same).trans (row y hy).2.2.2.2)
    have := (row x hx).2.2.1
    have := (row y hy).2.2.1
    omega
  have sub : S.image Prod.fst ∪ S.image Prod.snd ⊆ P := by
    intro t ht
    rcases mem_union.mp ht with l|r
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp l
      exact (row x hx).1
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp r
      exact (row x hx).2.1
  simpa only [card_union_of_disjoint dis,card_image_of_injOn left,card_image_of_injOn right,
    two_mul] using card_le_card sub

theorem count (B : ℕ) : 2*(family B).card≤primes.card :=
  matching (family B) primes (partner B) fun _ h => rows h

private theorem triangular (S : Finset (ℕ×ℕ)) (B start L : ℕ)
    (codes : ∀ z∈S, ∃ i j, i<j ∧ j<L ∧
      z=factors B (2*(start+i)+1) (2*(start+j)+1)) :
    S.card≤L.choose 2 := by
  let row (j : ℕ) := (range j).image (fun i => factors B (2*(start+i)+1) (2*(start+j)+1))
  have cover : S⊆(range L).biUnion row := by
    intro z hz
    obtain ⟨i,j,ij,jl,rfl⟩ := codes z hz
    exact mem_biUnion.mpr ⟨j,mem_range.mpr jl,mem_image.mpr ⟨i,mem_range.mpr ij,rfl⟩⟩
  calc
    S.card ≤ ∑ j∈range L,(row j).card := (card_le_card cover).trans card_biUnion_le
    _ ≤ ∑ j∈range L,j := sum_le_sum fun j _ => card_image_le.trans_eq (card_range j)
    _ = _ := by rw [Finset.sum_range_id,Nat.choose_two_right]

/-- There are exactly floor(B/2) positive odd digits below B, of which
two must be selected in increasing order. -/
theorem digit_count (B : ℕ) : (family B).card≤(B/2).choose 2 := by
  apply triangular _ B 0
  intro z hz
  obtain ⟨_,a,b,ok,rfl⟩ := mem_family.mp hz
  obtain ⟨_,_,⟨i,ai⟩,⟨j,bj⟩,ord,top⟩ := ok
  exact ⟨i,j,by omega,by omega,by simp [ai,bj]⟩

/-- At the half-width radix both leading digits are in the upper half of
the digit range, leaving exactly 2^510 possible odd values for each. -/
theorem half_width_digits : (family (2^512)).card≤((2:ℕ)^510).choose 2 := by
  apply triangular _ (2^512) (2^510)
  intro z hz
  obtain ⟨member,a,b,ok,rfl⟩ := mem_family.mp hz
  have lo := (PrimeFactors.MixedPrefixSample.mem_primes.mp (data member).1).1.1
  change 2^1023≤2^512*a+b at lo
  obtain ⟨_,_,⟨i,ai⟩,⟨j,bj⟩,ord,top⟩ := ok
  have ar : 2^511≤a := by
    by_contra! small
    have h := Nat.mul_le_mul_left (2^512) (Nat.succ_le_of_lt small)
    rw [Nat.mul_succ,show 2^512*2^511=(2:ℕ)^1023 by decide +kernel] at h
    omega
  refine ⟨i-2^510,j-2^510,by omega,by omega,?_⟩
  exact congrArg₂ (factors (2^512)) (by omega) (by omega)

private theorem prime_price : 2^1007*primes.card<eligible.card := by
  apply Nat.lt_of_mul_lt_mul_left (a:=41056)
  calc
    _ = (41056*2^1007)*primes.card := (Nat.mul_assoc ..).symm
    _ ≤ X*primes.card := Nat.mul_le_mul_right _ (by decide +kernel)
    _ < _ := SquareRootPhasePopulation.marginal

theorem fraction (B : ℕ) : 2^1008*(family B).card<eligible.card := by
  rw [show 2^1008=(2:ℕ)^1007*2 by decide +kernel,Nat.mul_assoc]
  exact (Nat.mul_le_mul_left _ (count B)).trans_lt prime_price

/-- Bound a finite menu even when its entry can be chosen after seeing the product. -/
theorem menu_count {ι : Type*} (I : Finset ι) (radix : ι → ℕ) :
    2*(I.biUnion (fun i => family (radix i))).card≤I.card*primes.card := by
  calc
    _ ≤ 2*∑ i∈I,(family (radix i)).card := Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ i∈I,2*(family (radix i)).card := Finset.mul_sum ..
    _ ≤ ∑ _i∈I,primes.card := sum_le_sum fun i _ => count _
    _ = _ := by simp

/-- The two digits are positive odd integers and the larger one is at least
three. Full-width prime factors consequently rule out both extreme split sizes. -/
theorem width {k : ℕ} {z : ℕ×ℕ} (mem : z∈family (2^k)) : 512≤k ∧ k≤1022 := by
  obtain ⟨h,a,b,ok,rfl⟩ := mem_family.mp mem
  obtain ⟨pa,qa,_⟩ := data h
  have pl := (PrimeFactors.MixedPrefixSample.mem_primes.mp pa).1.1
  have qu := (PrimeFactors.MixedPrefixSample.mem_primes.mp qa).1.2
  change 2^1023≤2^k*a+b at pl
  change 2^k*b+a<2*2^1023 at qu
  obtain ⟨_,_,⟨i,ai⟩,⟨j,bj⟩,lt,top⟩ := ok
  have lower : 2^1023 < (2^k)^2 := calc
    _ ≤ 2^k*a+b := pl
    _ < 2^k*(a+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
    _ ≤ (2^k)^2 := by rw [pow_two]; exact Nat.mul_le_mul_left _ (by omega)
  have upper : 2^(k+1)<(2:ℕ)^1024 := calc
    _ = 2^k*2 := pow_succ ..
    _ ≤ 2^k*b+a := (Nat.mul_le_mul_left _ (by omega : 2≤b)).trans (Nat.le_add_right ..)
    _ < 2*2^1023 := qu
    _ = _ := by decide +kernel
  rw [←pow_mul] at lower
  have le₁ := (pow_lt_pow_iff_right₀ (by decide : 1<(2:ℕ))).mp lower
  have le₂ := (pow_lt_pow_iff_right₀ (by decide : 1<(2:ℕ))).mp upper
  omega

noncomputable def binary := (Icc 512 1022).biUnion fun k => family (2^k)

theorem mem_binary {z : ℕ×ℕ} : z∈binary ↔ ∃ k : ℕ, z∈family (2^k) := by
  constructor
  · intro h
    obtain ⟨k,_,hk⟩ := mem_biUnion.mp h
    exact ⟨k,hk⟩
  · rintro ⟨k,hk⟩
    exact mem_biUnion.mpr ⟨k,mem_Icc.mpr (width hk),hk⟩

/-- At split width 1023-i, full-width primes force both odd block values
below 2^(i+1). The square of the number of possible odd values suffices. -/
theorem tail_count (i : ℕ) (small : i≤1023) : (family (2^(1023-i))).card≤4^i := by
  have cap : (family (2^(1023-i))).card≤((2:ℕ)^i).choose 2 := by
    apply triangular _ (2^(1023-i)) 0
    intro z hz
    obtain ⟨member,a,b,ok,rfl⟩ := mem_family.mp hz
    have high := (PrimeFactors.MixedPrefixSample.mem_primes.mp (data member).2.1).1.2
    change 2^(1023-i)*b+a<2*2^1023 at high
    obtain ⟨_,_,⟨u,au⟩,⟨v,bv⟩,ord,_⟩ := ok
    have top : b<2^(i+1) := by
      by_contra! le
      have prod := Nat.mul_le_mul_left (2^(1023-i)) le
      rw [←pow_add,show 1023-i+(i+1)=1024 by omega] at prod
      omega
    rw [pow_succ] at top
    exact ⟨u,v,by omega,by omega,by simp [au,bv]⟩
  calc
    _ ≤ ((2:ℕ)^i).choose 2 := cap
    _ ≤ 2^i*2^i := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le ..))
    _ = 4^i := (mul_pow (2:ℕ) 2 i).symm

private theorem geometric (i : ℕ) : (∑ j∈range (i+1),(4:ℕ)^j)≤2*4^i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ,pow_succ]
    omega

private theorem all_count {α : Type*} [DecidableEq α] (S : Finset α) (f : ℕ → Finset α) (P : ℕ)
    (inside : ∀ z∈S, ∃ k, 512≤k ∧ k≤1022 ∧ z∈f k)
    (per : ∀ k, 2*(f k).card≤P) (tail : ∀ i≤506, (f (1023-i)).card≤4^i) :
    2*S.card≤5*P+2*2^1013 := by
  let H := (Icc 512 516).biUnion f
  let T := (range 507).biUnion fun i => f (1023-i)
  have cover : S⊆H∪T := by
    intro z hz
    obtain ⟨k,lo,hi,hk⟩ := inside z hz
    by_cases small : k≤516
    · exact mem_union_left _ (mem_biUnion.mpr ⟨k,mem_Icc.mpr ⟨lo,small⟩,hk⟩)
    · apply mem_union_right H
      apply mem_biUnion.mpr
      exact ⟨1023-k,mem_range.mpr (by omega),by rwa [show 1023-(1023-k)=k by omega]⟩
  have hc : 2*H.card≤5*P := calc
    _ ≤ 2*∑ k∈Icc 512 516,(f k).card := Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ k∈Icc 512 516,2*(f k).card := Finset.mul_sum ..
    _ ≤ ∑ _k∈Icc 512 516,P := sum_le_sum fun k _ => per k
    _ = _ := by rw [sum_const,nsmul_eq_mul,Nat.card_Icc]; rfl
  have tc : T.card≤2^1013 := calc
    _ ≤ ∑ i∈range 507,(f (1023-i)).card := card_biUnion_le
    _ ≤ ∑ i∈range 507,4^i := sum_le_sum fun i hi => tail i (by have := mem_range.mp hi; omega)
    _ ≤ 2*4^506 := geometric 506
    _ = _ := by decide +kernel
  have total := (card_le_card cover).trans (card_union_le H T)
  omega

private theorem price_all {A P U : ℕ} (budget : 2*A≤5*P+2*2^1013)
    (marginal : X*P<41056*U) (population : 2^2046<21000000*U) : 2^1006*A<U := by
  change 2^1023*P<41056*U at marginal
  omega

attribute [local irreducible] binary

private theorem binary_inside (z : ℕ×ℕ) (hz : z∈binary) :
    ∃ k, 512≤k ∧ k≤1022 ∧ z∈family (2^k) := by
  obtain ⟨k,hk⟩ := mem_binary.mp hz
  exact ⟨k,(width hk).1,(width hk).2,hk⟩

private theorem binary_count : 2*binary.card≤5*primes.card+2*2^1013 :=
  all_count binary (fun k => family (2^k)) primes.card binary_inside
    (fun k => count _) (fun i hi => tail_count i (by omega))

/-- Allow every binary split, including a product-dependent choice. The first
five widths use the prime count, and the remaining digit counts fall geometrically. -/
theorem binary_fraction : 2^1006*binary.card<eligible.card :=
  price_all (A:=binary.card) (P:=primes.card) (U:=eligible.card) binary_count
    SquareRootPhasePopulation.marginal ChebyshevPrimeSample.eligible_count

end PrimeFactors.TransposedBlockPopulation
