import PrimeFactors.ThresholdPairCount
import PrimeFactors.FullRangeResidueEstimates

/-! Exact cells for the full population of two distinct 1,024-bit primes
with a 2,048-bit product, at fixed product residue one modulo 25.
Every vertical or horizontal slice above the product threshold is a suffix. -/
namespace PrimeFactors.PrimeProductRegion

open Finset FullRangeResidueEstimates ThresholdPairCount
open WideResiduePrimeSupply (B L)
open ResiduePairWeights (cells)

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

abbrev K : ℕ := 2^2047

noncomputable def cell (v : ZMod 25 × ZMod 25) : ℕ :=
  (distinctRegion K (tail v.1 X) (tail v.2 X)).card

private theorem cutoff {p : ℕ} (lo : X<p) (hi : p≤B) : X≤K/p ∧ K/p≤B := by
  have pos := lt_trans (by decide +kernel : 0<X) lo
  have prod : X*B=K := by decide +kernel
  constructor
  · exact (Nat.le_div_iff_mul_le pos).mpr ((Nat.mul_le_mul_left X hi).trans_eq prod)
  · have strict : K < (B+1)*p := by
      calc K = B*X := by decide +kernel
           _ ≤ B*p := Nat.mul_le_mul_left _ lo.le
           _ < (B+1)*p := Nat.mul_lt_mul_of_pos_right (by omega) pos
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul pos).mpr strict)

private theorem slice (x : ZMod 25) {p : ℕ} (lo : X<p) (hi : p≤B) :
    (tail x X).filter (fun q => K<p*q) = tail x (K/p) := by
  have pos := lt_trans (by decide +kernel : 0<X) lo
  have left := (cutoff lo hi).1
  ext q
  rw [mem_filter,mem_tail,mem_tail]
  have equiv : K<p*q ↔ K/p<q := by
    rw [Nat.div_lt_iff_lt_mul pos,Nat.mul_comm q p]
  rw [equiv]
  exact ⟨fun ⟨⟨_,hi,P,r⟩,lt⟩ => ⟨lt,hi,P,r⟩,
    fun ⟨lt,hi,P,r⟩ => ⟨⟨left.trans_lt lt,hi,P,r⟩,lt⟩⟩

theorem cell_spread {D U M : ℕ} (h : Estimates D U M) {v w : ZMod 25 × ZMod 25}
    (ua : IsUnit v.1) (ub : IsUnit v.2) (uc : IsUnit w.1) (ue : IsUnit w.2) :
    cell v ≤ cell w+(2*D*U+U) := by
  apply spread _ _ _ _ (h.upper _ ua) (h.upper _ ue) (h.upper _ uc)
  · intro p hp
    obtain ⟨lo,hi,_,_⟩ := mem_tail.mp hp
    rw [slice _ lo hi,slice _ lo hi]
    exact h.suffix _ _ ub ue _ (cutoff lo hi).1 (cutoff lo hi).2
  · intro p hp
    obtain ⟨lo,hi,_,_⟩ := mem_tail.mp hp
    rw [slice _ lo hi,slice _ lo hi]
    exact h.suffix _ _ ua uc _ (cutoff lo hi).1 (cutoff lo hi).2

theorem cell_lower {D U M : ℕ} (h : Estimates D U M) {v : ZMod 25 × ZMod 25}
    (ua : IsUnit v.1) (ub : IsUnit v.2) : M*(M-1)≤cell v := by
  have sub (x : ZMod 25) : tail x L ⊆ tail x X := by
    intro p hp
    obtain ⟨lo,hi,P,res⟩ := mem_tail.mp hp
    exact mem_tail.mpr ⟨(by decide +kernel : X≤L).trans_lt lo,hi,P,res⟩
  apply ThresholdPairCount.lower (h.lower _ ua) (h.lower _ ub) (sub _) (sub _)
  intro p hp q hq
  exact (by decide +kernel : K<L*L).trans_le (Nat.mul_le_mul (mem_tail.mp hp).1.le (mem_tail.mp hq).1.le)

private noncomputable def pool := (Ioc X B).filter Nat.Prime
private noncomputable def whole := distinctRegion K pool pool
private def residues (v : ℕ×ℕ) : ZMod 25 × ZMod 25 := (v.1,v.2)
private noncomputable def ordered (A : Finset (ZMod 25)) :=
  whole.filter fun v => residues v∈cells 1 A
noncomputable def population (A : Finset (ZMod 25)) :=
  (ordered A).filter fun v => v.1<v.2

private theorem mem_pool {p : ℕ} : p∈pool ↔ X<p ∧ p≤B ∧ p.Prime := by
  simp only [pool,mem_filter,mem_Ioc,and_assoc]

attribute [local irreducible] pool whole ordered population tail

private theorem mem_whole {p q : ℕ} : (p,q)∈whole ↔ p∈pool ∧ q∈pool ∧ K<p*q ∧ p≠q := by
  simp only [whole,distinctRegion,region,mem_filter,mem_product,and_assoc]

private theorem mem_ordered {A : Finset (ZMod 25)} {p q : ℕ} :
    (p,q)∈ordered A ↔ (p,q)∈whole ∧ ((p*q:ℕ):ZMod 25)=1 ∧ ((p+q:ℕ):ZMod 25)∈A := by
  simp only [ordered,mem_filter,cells,mem_univ,true_and,residues,Nat.cast_mul,Nat.cast_add]

/-- All and only the target unordered prime pairs, with the usual inclusive
lower bit-width endpoint. The three width endpoints are powers of two. -/
theorem mem_population {A : Finset (ZMod 25)} {p q : ℕ} :
    (p,q)∈population A ↔ X≤p ∧ p<q ∧ q<B ∧ p.Prime ∧ q.Prime ∧
      K≤p*q ∧ ((p*q:ℕ):ZMod 25)=1 ∧ ((p+q:ℕ):ZMod 25)∈A := by
  rw [population,mem_filter,mem_ordered,mem_whole,mem_pool,mem_pool]
  constructor
  · rintro ⟨⟨⟨⟨pl,_,P⟩,⟨_,qh,Q⟩,prod,_⟩,res,sum⟩,order⟩
    have ne : q≠B := fun eq => (Nat.Prime.not_prime_pow (by decide : 2≤1024) (x:=2)) ((congrArg Nat.Prime eq).mp Q)
    exact ⟨pl.le,order,qh.lt_of_ne ne,P,Q,prod.le,res,sum⟩
  · rintro ⟨pl,order,qh,P,Q,prod,res,sum⟩
    have ne : X≠p := fun eq => (Nat.Prime.not_prime_pow (by decide : 2≤1023) (x:=2)) ((congrArg Nat.Prime eq).mpr P)
    have pl' := pl.lt_of_ne ne
    have po := P.odd_of_ne_two (lt_of_lt_of_le (by decide +kernel : 2<X) pl).ne'
    have qo := Q.odd_of_ne_two (lt_of_lt_of_le (by decide +kernel : 2<X) (pl.trans order.le)).ne'
    have rem := Nat.odd_iff.mp (po.mul qo)
    have neq : K≠p*q := fun eq => (by decide +kernel : K%2≠1) (eq ▸ rem)
    exact ⟨⟨⟨⟨pl',(order.trans qh).le,P⟩,⟨pl'.trans order,qh.le,Q⟩,prod.lt_of_ne neq,order.ne⟩,res,sum⟩,order⟩

private theorem ordered_twice (A : Finset (ZMod 25)) : (ordered A).card=2*(population A).card := by
  let S := ordered A
  let lt (z : ℕ×ℕ) := z.1<z.2
  have flip {z : ℕ×ℕ} (h : z∈S) : z.swap∈S := by
    obtain ⟨w,res,sum⟩ := mem_ordered.mp h
    obtain ⟨p,q,prod,ne⟩ := mem_whole.mp w
    exact mem_ordered.mpr ⟨mem_whole.mpr ⟨q,p,by simpa [Nat.mul_comm] using prod,ne.symm⟩,
      by simpa [Nat.mul_comm] using res,by simpa [Nat.add_comm] using sum⟩
  have equal : (S.filter lt).card=(S.filter fun z => ¬lt z).card := by
    apply card_nbij' Prod.swap Prod.swap
    · intro z hz
      obtain ⟨mem,h⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨flip mem,not_lt_of_ge h.le⟩
    · intro z hz
      obtain ⟨mem,h⟩ := mem_filter.mp hz
      have ne := (mem_whole.mp (mem_ordered.mp mem).1).2.2.2
      exact mem_filter.mpr ⟨flip mem,lt_of_le_of_ne (le_of_not_gt h) ne.symm⟩
    all_goals intro z _; rfl
  have split := filter_card_add_filter_neg_card_eq_card (s:=S) lt
  unfold population
  change S.card=2*(S.filter lt).card
  omega

private theorem fiber (v : ZMod 25 × ZMod 25) : (whole.filter fun z => residues z=v).card=cell v := by
  obtain ⟨a,b⟩ := v
  have eq {p : ℕ} {x : ZMod 25} : p%25=x.val ↔ (p:ZMod 25)=x := by
    rw [←ZMod.val_natCast]
    exact ⟨fun h => ZMod.val_injective 25 h,congrArg ZMod.val⟩
  apply congrArg Finset.card
  ext ⟨p,q⟩
  simp only [mem_filter,mem_whole,residues,Prod.mk.injEq,distinctRegion,region,
    mem_product,mem_pool,mem_tail,eq]
  tauto

theorem twice_count (A : Finset (ZMod 25)) :
    2*(population A).card = ∑ v∈cells (1:ZMod 25) A, cell v := by
  rw [←ordered_twice,ordered]
  exact (sum_card_fiberwise_eq_card_filter whole (cells 1 A) residues).symm.trans
    (sum_congr rfl fun v _ => fiber v)

end PrimeFactors.PrimeProductRegion
