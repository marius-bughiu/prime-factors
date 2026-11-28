import PrimeFactors.GaussianSquareRemainder
import PrimeFactors.SeparatedMonotonePopulation

/-! Bound the aggregate number of exact square tests that could be saved
on floor-remainder hits, even if every baseline test on each hit were free. -/
namespace PrimeFactors.GaussianGateAggregateCost

open Finset MixedPrefixSample SeparatedMonotonePopulation
open private PrimeFactors.MixedPrefixSample.mem_primes from PrimeFactors.MixedPrefixSample
open scoped Classical
set_option exponentiation.threshold 8192
attribute [local irreducible] sample eligible far primes

/-- Exact square tests made by the parity- and modulo-256-screened
midpoint scan through the prime midpoint, inclusive. -/
noncomputable def tests (v : ℕ×ℕ) : Finset ℕ :=
  (Icc (ceilSqrt (v.1*v.2)) ((v.1+v.2)/2)).filter fun m =>
    m%2=((v.1*v.2+1)/2)%2 ∧ ∃ b : ZMod 256, (m:ZMod 256)^2-(v.1*v.2:ℕ)=b^2

private theorem info {p q : ℕ} (h : (p,q)∈eligible) :
    2^1023≤p ∧ p<q ∧ q<2^1024 ∧ Odd p ∧ Odd q := by
  simp only [eligible,sample,mem_filter,mem_ordered] at h
  obtain ⟨⟨pm,qm,_,_,_⟩,ord⟩ := h
  obtain ⟨⟨pl,_⟩,pp⟩ := PrimeFactors.MixedPrefixSample.mem_primes.mp pm
  obtain ⟨⟨_,qh⟩,qp⟩ := PrimeFactors.MixedPrefixSample.mem_primes.mp qm
  change 2^1023≤p at pl
  change q<2*2^1023 at qh
  have lo : 2<p := (by decide +kernel : 2<2^1023).trans_le pl
  exact ⟨pl,ord,by omega,pp.odd_of_ne_two lo.ne',qp.odd_of_ne_two (lo.trans ord).ne'⟩

private theorem at_most {v : ℕ×ℕ} (h : v∈eligible) : (tests v).card≤2^1024 := by
  obtain ⟨_,ord,upper,_,_⟩ := info h
  apply (card_le_card (t:=range (2^1024)) ?_).trans_eq (card_range _)
  intro m hm
  have high := (mem_Icc.mp (mem_filter.mp hm).1).2
  exact mem_range.mpr (by omega)

/-- On the large-gap majority, even just the true midpoint's single
residue class modulo 256 supplies at least 2^977 exact square tests. -/
theorem far_cost {p q : ℕ} (large : (p,q)∈far) : 2^977≤(tests (p,q)).card := by
  obtain ⟨el,gap⟩ := mem_far.mp large
  obtain ⟨lo,ord,hi,op,oq⟩ := info el
  change 2^1006≤q-p at gap
  let m := (p+q)/2
  let d := (q-p)/2
  have sum : 2*m=p+q := by obtain ⟨a,h⟩ := op; obtain ⟨b,k⟩ := oq; dsimp [m]; omega
  have diff : 2*d+p=q := by obtain ⟨a,h⟩ := op; obtain ⟨b,k⟩ := oq; dsimp [d]; omega
  have ident : m^2=p*q+d^2 := by
    have lm : m=p+d := by omega
    rw [lm,←diff]; ring
  have parity : m%2=((p*q+1)/2)%2 := by
    obtain ⟨a,rfl⟩ := op
    obtain ⟨b,rfl⟩ := oq
    ring_nf at sum ⊢
    omega
  let back (i : ℕ) := m-256*i
  have visit (i : ℕ) (ok : i∈range (2^977)) : back i ∈ tests (p,q) := by
    have idx := mem_range.mp ok
    have fits : 256*i≤m := by omega
    have sub : back i+256*i=m := Nat.sub_add_cancel fits
    have small : 256*i≤2^985 := by omega
    have top : m≤2^1024 := by omega
    have loss := Nat.mul_le_mul top small
    have h2 := Nat.pow_le_pow_left (by omega : 2^1005≤d) 2
    have room : 2*(2^1024*2^985:ℕ)=(2^1005)^2 := by decide +kernel
    have room' : 2*(m*(256*i))≤d^2 := (Nat.mul_le_mul_left 2 loss).trans (room ▸ h2)
    have recover : p*q≤(back i)^2 := by
      have id2 : (back i)^2+2*(m*(256*i))=m^2+(256*i)^2 := by
        rw [←sub]; ring
      omega
    have modEq : (back i : ZMod 256)=(m:ZMod 256) := by
      simpa only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,add_zero] using
        congrArg (fun n : ℕ => (n : ZMod 256)) sub
    have idmod := congrArg (fun n : ℕ => (n:ZMod 256)) ident
    push_cast at idmod
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨ceilSqrt_le_iff.mpr recover,Nat.sub_le _ _⟩,?_, (d:ZMod 256),?_⟩
    · change back i%2=((p*q+1)/2)%2
      omega
    · change (back i : ZMod 256)^2-((p*q:ℕ):ZMod 256)=(d:ZMod 256)^2
      rw [modEq,Nat.cast_mul,idmod,add_sub_cancel_left]
  have inj : (range (2^977)).toSet.InjOn back := by
    intro i hi' j hj' equal
    have iSize := mem_range.mp hi'
    have jSize := mem_range.mp hj'
    change m-256*i=m-256*j at equal
    omega
  simpa only [card_range] using card_le_card_of_injOn (s:=range (2^977)) (t:=tests (p,q)) back visit inj

private theorem hits_eligible : sample GaussianSquareRemainder.Passes ⊆ eligible := by
  intro v hv
  simp only [sample,eligible,mem_filter,mem_ordered] at hv ⊢
  exact ⟨⟨hv.1.1,hv.1.2.1,hv.1.2.2.1,hv.1.2.2.2.1,trivial⟩,hv.2⟩

private theorem sum_cap {α : Type*} (s : Finset α) (f : α → ℕ) (c : ℕ)
    (bound : ∀ v∈s, f v≤c) : (∑ v∈s,f v)≤s.card*c := by
  simpa only [sum_const,nsmul_eq_mul] using sum_le_sum bound

private theorem sum_floor {α : Type*} (s t : Finset α) (f : α → ℕ) (c : ℕ)
    (sub : s ⊆ t) (bound : ∀ v∈s,c≤f v) : s.card*c ≤ ∑ v∈t,f v := by
  have count := sum_le_sum bound
  exact (by simpa only [sum_const,nsmul_eq_mul] using count :
    s.card*c ≤ ∑ v∈s,f v).trans (sum_le_sum_of_subset sub)

private theorem compare_counts {k hits population distant : ℕ}
    (rare : 2^(k+48)*hits < population) (large : 2*population < 3*distant) :
    2^k*(hits*2^1024) < distant*2^977 := by
  have coeff : 2*(2^1024:ℕ)=2^48*2^977 := by decide +kernel
  apply Nat.lt_of_mul_lt_mul_left (a:=2)
  calc
    2*(2^k*(hits*2^1024)) = (2*2^1024)*(2^k*hits) := by ac_rfl
    _ = (2^(k+48)*hits)*2^977 := by rw [coeff,pow_add]; ac_rfl
    _ < population*2^977 := Nat.mul_lt_mul_of_pos_right rare (by positivity)
    _ ≤ 2*(distant*2^977) := by
      have h : population≤2*distant := by omega
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (2^977) h

/-- Any family occupying less than a 2^(-(k+48)) fraction of eligible
pairs contributes less than a 2^(-k) fraction of their baseline tests. -/
theorem family_bound (family : Finset (ℕ×ℕ)) (k : ℕ) (sub : family ⊆ eligible)
    (rare : 2^(k+48)*family.card < eligible.card) :
    2^k*(∑ v∈family,(tests v).card) <
      ∑ v∈eligible,(tests v).card := by
  have hit_cap := sum_cap family (fun v => (tests v).card)
    (2^1024) (fun v h => at_most (sub h))
  have total_floor := sum_floor far eligible (fun v => (tests v).card) (2^977)
    (fun v h => (mem_far.mp h).1) (fun v h => far_cost h)
  exact (Nat.mul_le_mul_left _ hit_cap).trans_lt
    ((compare_counts rare two_thirds).trans_le total_floor)

/-- The total baseline work on every successful gate input is less than
2^-439 of the full baseline cost. It bounds even a hypothetical free
replacement for all exact square tests on every hit. -/
theorem aggregate :
    2^439*(∑ v∈sample GaussianSquareRemainder.Passes,(tests v).card) <
      ∑ v∈eligible,(tests v).card := by
  apply family_bound (sample GaussianSquareRemainder.Passes) 439 hits_eligible
  rw [show 439+48=487 by decide]
  exact GaussianSquareRemainder.frequency

end PrimeFactors.GaussianGateAggregateCost
