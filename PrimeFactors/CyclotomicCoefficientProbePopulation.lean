import PrimeFactors.BlockProbePopulation
import PrimeFactors.BalancedCyclotomicPrefix

/-! Counting indices where a low cyclotomic coefficient or its inclusive
prefix can reveal a departure from baseline. Population bounds distinguish
fixed menus, bounded public tags, and shifts of the public square root. -/

namespace PrimeFactors.CyclotomicCoefficientProbePopulation

open Finset MixedPrefixSample
open scoped Classical
open private PrimeFactors.MixedPrefixSample.mem_sample PrimeFactors.MixedPrefixSample.mem_primes
  from PrimeFactors.MixedPrefixSample

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192
attribute [local irreducible] primes eligible sample ordered

/-- An index at an odd prime or its immediate successor singles out the
same candidate prime. -/
def anchor (k : ℕ) : ℕ := if k%2=1 then k else k-1

def Touches (p q k : ℕ) := k=p ∨ k=q ∨ k=p+1 ∨ k=q+1

private theorem prime_info {p : ℕ} (member : p∈primes) :
    X≤p ∧ p<2*X ∧ p.Prime ∧ p%2=1 := by
  obtain ⟨⟨lo,hi⟩,prime⟩ := PrimeFactors.MixedPrefixSample.mem_primes.mp member
  have high : 2<X := by decide +kernel
  have odd := prime.odd_of_ne_two (by omega)
  exact ⟨lo,hi,prime,Nat.odd_iff.mp odd⟩

private theorem pair_info {z : ℕ×ℕ} (member : z∈eligible) :
    z.1∈primes ∧ z.2∈primes ∧ z.1<z.2 := by
  rw [eligible] at member
  obtain ⟨base,order⟩ := PrimeFactors.MixedPrefixSample.mem_sample.mp member
  exact ⟨(mem_ordered.mp base).1,(mem_ordered.mp base).2.1,order⟩

theorem anchor_of_hit {p q k : ℕ} (po : p%2=1) (qo : q%2=1) (hit : Touches p q k) :
    anchor k=p ∨ anchor k=q := by
  unfold Touches at hit
  unfold anchor
  split <;> omega

noncomputable def hits (Q : Finset ℕ) := eligible.filter fun z => ∃ k∈Q, Touches z.1 z.2 k

theorem mem_hits {Q : Finset ℕ} {z : ℕ×ℕ} :
    z∈hits Q ↔ z∈eligible ∧ ∃ k∈Q, Touches z.1 z.2 k := by simp only [hits,mem_filter]

attribute [local irreducible] hits

private theorem count_rows (A : Finset (ℕ×ℕ)) (P Q : Finset ℕ)
    (row : ∀ z∈A, z.1∈P ∧ z.2∈P ∧ z.1≤z.2 ∧ ∃ k∈Q, anchor k=z.1 ∨ anchor k=z.2) :
    A.card≤Q.card*P.card := by
  let pair (v : ℕ×ℕ) := (min (anchor v.1) v.2, max (anchor v.1) v.2)
  have cover : A⊆(Q ×ˢ P).image pair := by
    intro z member
    obtain ⟨p,q,order,k,hk,eq|eq⟩ := row z member
    · exact mem_image.mpr ⟨(k,z.2),mem_product.mpr ⟨hk,q⟩,
        by simp [pair,eq,min_eq_left order,max_eq_right order]⟩
    · exact mem_image.mpr ⟨(k,z.1),mem_product.mpr ⟨hk,p⟩,
        by simp [pair,eq,min_eq_right order,max_eq_left order]⟩
  exact ((card_le_card cover).trans card_image_le).trans_eq (card_product ..)

/-- Any fixed finite menu touches at most one prime anchor per index. -/
theorem count (Q : Finset ℕ) : (hits Q).card≤Q.card*primes.card := by
  apply count_rows
  intro z member
  obtain ⟨eligible',k,hk,hit⟩ := mem_hits.mp member
  obtain ⟨p,q,order⟩ := pair_info eligible'
  exact ⟨p,q,order.le,k,hk,anchor_of_hit (prime_info p).2.2.2 (prime_info q).2.2.2 hit⟩

private theorem price {A P T D m : ℕ} (cost : A≤D*P)
    (marginal : X*P<41056*T) (fit : 41056*m*D≤X) : m*A<T := by
  apply Nat.lt_of_mul_lt_mul_left (a:=41056)
  calc
    41056*(m*A) ≤ 41056*(m*(D*P)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ cost)
    _ = (41056*m*D)*P := by ring
    _ ≤ X*P := Nat.mul_le_mul_right _ fit
    _ < _ := marginal

theorem fraction {Q : Finset ℕ} {m : ℕ} (fit : 41056*m*Q.card≤X) :
    m*(hits Q).card<eligible.card :=
  price (count Q) SquareRootPhasePopulation.marginal fit

theorem small64 {Q : Finset ℕ} (cap : Q.card≤2^64) : 2^943*(hits Q).card<eligible.card :=
  fraction ((Nat.mul_le_mul_left _ cap).trans (by decide +kernel))

theorem small128 {Q : Finset ℕ} (cap : Q.card≤2^128) : 2^879*(hits Q).card<eligible.card :=
  fraction ((Nat.mul_le_mul_left _ cap).trans (by decide +kernel))

/-- Reply histories are most recent first. A policy may ask its next question
about any index as a function of the entire history. -/
def history {Q A : Type*} (ask : List A→Q) (reply : Q→A) : ℕ→List A
  | 0 => []
  | k+1 => let previous := history ask reply k; reply (ask previous)::previous

private theorem history_eq {Q A : Type*} (ask : List A→Q) (actual base : Q→A) (k : ℕ)
    (agree : ∀ i<k, actual (ask (history ask base i))=base (ask (history ask base i))) :
    history ask actual k=history ask base k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [history]
    rw [ih (fun i hi => agree i (by omega)),agree k (by omega)]

/-- Bound any event that requires a changed reply in an adaptive transcript.
The policy may additionally depend on one of finitely many public tags.
The union of all baseline transcripts costs at most one index per step and tag. -/
theorem tagged_count {I Q A : Type*} (tags : Finset I) (tag : ℕ→I)
    (ask : I→List A→Q) (index : Q→ℕ) (base : I→Q→A) (actual : ℕ×ℕ→Q→A)
    (k : ℕ) (S : Finset (ℕ×ℕ))
    (support : ∀ z∈eligible, ∀ q, actual z q≠base (tag (z.1*z.2)) q →
      Touches z.1 z.2 (index q))
    (rows : ∀ z∈S, z∈eligible ∧ tag (z.1*z.2)∈tags ∧
      history (ask (tag (z.1*z.2))) (actual z) k ≠
        history (ask (tag (z.1*z.2))) (base (tag (z.1*z.2))) k) :
    S.card≤tags.card*k*primes.card := by
  classical
  let indices (t : I) := (range k).image (fun i => index (ask t (history (ask t) (base t) i)))
  let pool := tags.biUnion indices
  have capacity : pool.card≤tags.card*k := by
    apply card_biUnion_le_card_mul
    intro t _
    exact card_image_le.trans_eq (card_range k)
  have covered : S⊆hits pool := by
    intro z hz
    obtain ⟨member,tin,neq⟩ := rows z hz
    let t := tag (z.1*z.2)
    have bad : ∃ i<k, actual z (ask t (history (ask t) (base t) i)) ≠
        base t (ask t (history (ask t) (base t) i)) := by
      by_contra missing
      apply neq
      apply history_eq
      intro i bound
      by_contra changed
      exact missing ⟨i,bound,changed⟩
    obtain ⟨i,il,changed⟩ := bad
    exact mem_hits.mpr ⟨member,_,mem_biUnion.mpr ⟨t,tin,
      mem_image.mpr ⟨i,mem_range.mpr il,rfl⟩⟩,support z member _ changed⟩
  exact ((card_le_card covered).trans (count pool)).trans (Nat.mul_le_mul_right _ capacity)

theorem tagged_fraction {I Q A : Type*} (tags : Finset I) (tag : ℕ→I)
    (ask : I→List A→Q) (index : Q→ℕ) (base : I→Q→A) (actual : ℕ×ℕ→Q→A)
    (k m : ℕ) (S : Finset (ℕ×ℕ))
    (support : ∀ z∈eligible, ∀ q, actual z q≠base (tag (z.1*z.2)) q →
      Touches z.1 z.2 (index q))
    (rows : ∀ z∈S, z∈eligible ∧ tag (z.1*z.2)∈tags ∧
      history (ask (tag (z.1*z.2))) (actual z) k ≠
        history (ask (tag (z.1*z.2))) (base (tag (z.1*z.2))) k)
    (fit : 41056*m*(tags.card*k)≤X) : m*S.card<eligible.card :=
  price (tagged_count tags tag ask index base actual k S support rows)
    SquareRootPhasePopulation.marginal fit

/-- The Boolean flag distinguishes inclusive prefix sums (true) from single
coefficients (false). Every legal query lies in the full-width prime-word band. -/
abbrev Query := Bool × {k : ℕ // X≤k ∧ k<2*X}

noncomputable def reading (z : ℕ×ℕ) (q : Query) : ℤ :=
  let f := Polynomial.cyclotomic (z.1*z.2) ℤ
  if q.1 then ∑ j∈range (q.2.val+1),f.coeff j else f.coeff q.2.val

/-- The actual cyclotomic coefficient and inclusive prefix-sum oracles
share the zero baseline in the word band, away from the indicated positions. -/
theorem reading_support {z : ℕ×ℕ} (member : z∈eligible) (q : Query)
    (change' : reading z q ≠ 0) : Touches z.1 z.2 q.2.val := by
  obtain ⟨p,q',order⟩ := pair_info member
  obtain ⟨low,_,pp,_⟩ := prime_info p
  have qp := (prime_info q').2.2.1
  obtain ⟨flag,k,start,stop⟩ := q
  have large : 2≤X := by decide +kernel
  change Touches z.1 z.2 k
  cases flag with
  | false =>
    change (Polynomial.cyclotomic (z.1*z.2) ℤ).coeff k ≠ 0 at change'
    have hit := BalancedCyclotomicPrefix.support pp qp order low (large.trans start) stop change'
    unfold Touches
    tauto
  | true =>
    change (∑ j∈range (k+1),(Polynomial.cyclotomic (z.1*z.2) ℤ).coeff j) ≠ 0 at change'
    rw [BalancedCyclotomicPrefix.prefix_sum pp qp order low stop] at change'
    by_contra h
    have miss : k≠z.1 ∧ k≠z.2 := ⟨fun ep => h (Or.inl ep),fun eq => h (Or.inr (Or.inl eq))⟩
    simp only [if_neg (show k≠0 by omega),if_neg miss.1,if_neg miss.2,add_zero] at change'
    exact change' rfl

/-- A finite public tag can select an adaptive mixed coefficient/prefix policy.
The event records a nonzero reply at some point in its complete history. -/
noncomputable def departures {I : Type*} (tag : ℕ→I) (ask : I→List ℤ→Query) (k : ℕ) :=
  eligible.filter fun z => history (ask (tag (z.1*z.2))) (reading z) k ≠
    history (ask (tag (z.1*z.2))) (fun _ => 0) k

theorem low_tagged {I : Type*} (tags : Finset I) (tag : ℕ→I) (ask : I→List ℤ→Query)
    (k m : ℕ) (covers : ∀ z∈eligible, tag (z.1*z.2)∈tags)
    (fit : 41056*m*(tags.card*k)≤X) : m*(departures tag ask k).card<eligible.card := by
  apply tagged_fraction tags tag ask (fun q => q.2.val) (fun _ _ => 0) reading k m _
      (fun _ h q nonzero => reading_support h q nonzero) _ fit
  intro z hz
  obtain ⟨el,mismatch⟩ := mem_filter.mp hz
  exact ⟨el,covers z el,mismatch⟩

/-- Even a supplied 64-bit public tag and 2^64 subsequent adaptive queries
have fewer departures than one in 2^879 over the entire population. -/
theorem tagged_64_64 {I : Type*} (tags : Finset I) (tag : ℕ→I) (ask : I→List ℤ→Query)
    (k : ℕ) (covers : ∀ z∈eligible, tag (z.1*z.2)∈tags)
    (limited : tags.card≤2^64) (queries : k≤2^64) :
    2^879*(departures tag ask k).card<eligible.card :=
  low_tagged tags tag ask k _ covers ((Nat.mul_le_mul_left _ (Nat.mul_le_mul limited queries)).trans
    (by decide +kernel))

/-- Square-root offsets are fixed, but the actual probed indices depend on
the entire public product. Signed offsets cover both sides of the square root. -/
def AtOffset (p q : ℕ) (d : ℤ) : Prop :=
  let s := ((p*q).sqrt:ℤ)+d
  s=p ∨ s=q ∨ s=(p:ℤ)+1 ∨ s=(q:ℤ)+1

noncomputable def offsetHits (Q : Finset ℤ) := eligible.filter fun z => ∃ d∈Q, AtOffset z.1 z.2 d

theorem mem_offsetHits {Q : Finset ℤ} {z : ℕ×ℕ} :
    z∈offsetHits Q ↔ z∈eligible ∧ ∃ d∈Q, AtOffset z.1 z.2 d := by simp only [offsetHits,mem_filter]

attribute [local irreducible] offsetHits SquareRootShiftPartners.detected

private noncomputable def localOffsets (Q : Finset ℤ) (p : ℕ) : Finset (ZMod p) :=
  Q.image (fun d : ℤ => -(d:ZMod p)) ∪ Q.image (fun d : ℤ => 1-(d:ZMod p))

private theorem root_mod {p s : ℕ} {d : ℤ} (Q : Finset ℤ) (inside : d∈Q)
    (eq : (s:ℤ)+d=p ∨ (s:ℤ)+d=(p:ℤ)+1) : (s:ZMod p)∈localOffsets Q p := by
  rcases eq with h|h
  · apply mem_union_left
    apply mem_image.mpr
    refine ⟨d,inside,?_⟩
    have m := congrArg (fun z : ℤ => (z : ZMod p)) h
    dsimp only at m
    simp only [Int.cast_add,Int.cast_natCast,ZMod.natCast_self] at m
    linear_combination -m
  · apply mem_union_right
    apply mem_image.mpr
    refine ⟨d,inside,?_⟩
    have m := congrArg (fun z : ℤ => (z : ZMod p)) h
    dsimp only at m
    simp only [Int.cast_add,Int.cast_natCast,ZMod.natCast_self,Int.cast_one,
      zero_add] at m
    linear_combination -m

theorem offset_count (Q : Finset ℤ) : (offsetHits Q).card≤(4*Q.card)*primes.card := by
  classical
  have cover : offsetHits Q⊆SquareRootShiftPartners.detected (localOffsets Q) ∩ eligible := by
    intro z member
    obtain ⟨el,d,hd,h⟩ := mem_offsetHits.mp member
    refine mem_inter.mpr ⟨BlockProbePopulation.mem_detected _ el ?_,el⟩
    rcases h with h|h|h|h
    · exact Or.inl (root_mod Q hd (Or.inl h))
    · exact Or.inr (root_mod Q hd (Or.inl h))
    · exact Or.inl (root_mod Q hd (Or.inr h))
    · exact Or.inr (root_mod Q hd (Or.inr h))
  have cap (p : ℕ) : (localOffsets Q p).card≤2*Q.card := by
    unfold localOffsets
    exact (card_union_le ..).trans ((Nat.add_le_add card_image_le card_image_le).trans_eq (two_mul _).symm)
  have upper := (card_le_card cover).trans (BlockProbePopulation.residue_count _ (fun p _ => cap p))
  calc _ ≤ primes.card*(2*(2*Q.card)) := upper
       _ = _ := (show ∀ a b : ℕ, b*(2*(2*a))=4*a*b by intros; ring) _ _

theorem offset_fraction {Q : Finset ℤ} {m : ℕ} (fit : 41056*m*(4*Q.card)≤X) :
    m*(offsetHits Q).card<eligible.card :=
  price (offset_count Q) SquareRootPhasePopulation.marginal fit

theorem offset_small128 {Q : Finset ℤ} (cap : Q.card≤2^128) :
    2^877*(offsetHits Q).card<eligible.card :=
  offset_fraction ((Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 4 cap)).trans (by decide +kernel))

end PrimeFactors.CyclotomicCoefficientProbePopulation
