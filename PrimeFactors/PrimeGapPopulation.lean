import PrimeFactors.WeightedTracePrefix
import PrimeFactors.Fermat
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-! A finite reduction from missing first-trace prime partners to the total
length of the gaps larger than the square root of their lower prime. -/
namespace PrimeFactors.PrimeGapPopulation
open Finset

def center (p : ℕ) := 3*p/2
noncomputable def next (c : ℕ) := Nat.find (Nat.exists_infinite_primes (c+1))

private theorem next_data (c : ℕ) : c<next c ∧ (next c).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes (c+1))
private theorem next_le {c q : ℕ} (lt : c<q) (prime : q.Prime) : next c≤q :=
  Nat.find_min' _ ⟨lt,prime⟩

private theorem locate {c : ℕ} (large : 2≤c) :
    ∃ r, r.Prime ∧ r≤c ∧ c<next r ∧ next r=next c := by
  let r := Nat.findGreatest Nat.Prime c
  have rp : r.Prime := Nat.findGreatest_spec large Nat.prime_two
  have rc : r≤c := Nat.findGreatest_le c
  have above : c<next r := by
    by_contra! h
    exact (Nat.findGreatest_is_greatest (P:=Nat.Prime) ((next_data r).1) h) (next_data r).2
  exact ⟨r,rp,rc,above,le_antisymm (next_le (rc.trans_lt (next_data c).1) (next_data c).2)
    (next_le above (next_data r).2)⟩

noncomputable def missing (P : Finset ℕ) := P.filter fun p => center p+(center p).sqrt < next (center p)
noncomputable def longGaps (u : ℕ) := (range (u+1)).filter fun r => r.Prime ∧ r≤(next r-r)^2

/-- Distinct smaller primes give distinct integer centers. Every center
whose next prime is farther than floor(sqrt(center)) lies in a long gap. -/
theorem missing_bound (P : Finset ℕ) (u : ℕ) (bounds : ∀ p∈P, 2≤center p ∧ center p≤u) :
    (missing P).card ≤ ∑ r∈longGaps u, (next r-r) := by
  classical
  have inj : Function.Injective center := by intro p q eq; dsimp [center] at eq; omega
  rw [← card_image_of_injective (missing P) inj]
  apply (card_le_card (t:=(longGaps u).biUnion fun r => Ico r (next r)) ?_).trans
  · apply card_biUnion_le.trans_eq
    simp
  · intro c hc
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hc
    obtain ⟨pP,far⟩ := mem_filter.mp hp
    obtain ⟨cl,cu⟩ := bounds p pP
    obtain ⟨r,rp,rc,above,eq⟩ := locate cl
    have root : (center p).sqrt+1 ≤ next r-r := by rw [eq]; omega
    have long := (Nat.lt_succ_sqrt' (center p)).trans_le (Nat.pow_le_pow_left root 2)
    exact mem_biUnion.mpr ⟨r,mem_filter.mpr ⟨mem_range.mpr (by omega),rp,rc.trans long.le⟩,
      mem_Ico.mpr ⟨rc,above⟩⟩

/-- If the next prime is within one integer square root of floor(3p/2),
the first integer label, computed entirely from the product, gives a split. -/
theorem first_trace {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (big : 6<p)
    (lo : center p<q) (hi : q≤center p+(center p).sqrt) :
    let n := p*q
    let s := ceilSqrt (24*n)
    let z := (s^2-24*n).sqrt
    s=3*p+2*q ∧ s^2=24*n+z^2 ∧ (n.gcd ((s+z)/2)=p ∨ n.gcd ((s+z)/2)=q) := by
  let S := 3*p+2*q
  have two : 3*p≤2*q := by dsimp [center] at lo; omega
  have dist : (3*p).dist (2*q)=2*q-3*p := by rw [Nat.dist_eq_sub_of_le two]
  have small : 2*q-3*p≤2*(center p).sqrt := by dsimp [center] at hi ⊢; omega
  have ds : (2*q-3*p)^2≤6*p := by
    have h := Nat.pow_le_pow_left small 2
    rw [mul_pow] at h
    have cs := Nat.sqrt_le' (center p)
    have cp : 2*center p≤3*p := by dsimp [center]; omega
    omega
  have identity := multiplier_sum_square p q 3 2
  change S^2=24*(p*q)+(3*p).dist (2*q)^2 at identity
  have first : ceilSqrt (24*(p*q))=S := by
    apply le_antisymm (ceilSqrt_le_iff.mpr (by omega))
    by_contra! bad
    have lower : 24*(p*q)≤(ceilSqrt (24*(p*q)))^2 := ceilSqrt_le_iff.mp le_rfl
    obtain ⟨v,hv⟩ : ∃ v, S=v+1 := ⟨S-1,by dsimp [S]; omega⟩
    have below := lower.trans (Nat.pow_le_pow_left (show ceilSqrt (24*(p*q))≤v by omega) 2)
    rw [dist,hv] at identity
    have sz : 3*p+2*q=v+1 := hv
    nlinarith only [identity,below,ds,sz,qp.pos]
  dsimp only
  rw [first]
  have pq : p<q := by dsimp [center] at lo; omega
  have cop (a : ℕ) (pr : a.Prime) (gt : 6<a) : Nat.Coprime 6 a :=
    (pr.coprime_iff_not_dvd.mpr (fun d => (not_le_of_gt gt) (Nat.le_of_dvd (by decide) d))).symm
  have cn := Nat.Coprime.mul_right (cop p pp big) (cop q qp (big.trans pq))
  refine ⟨rfl,?_,?_⟩
  · rw [identity,Nat.add_sub_cancel_left,Nat.sqrt_eq']
  · exact WeightedTracePrefix.shared_gcd rfl (a:=3) (b:=2) (by decide) cn rfl

/-- The finite premise to which published asymptotic gap bounds apply.
Every prime in the good set has an actual larger prime partner, together
with the square and gcd produced at the first product-only trace. -/
theorem coverage (P : Finset ℕ) (u : ℕ)
    (data : ∀ p∈P, p.Prime ∧ 6<p ∧ center p≤u) :
    ∃ G⊆P, P.card ≤ G.card+∑ r∈longGaps u, (next r-r) ∧
      ∀ p∈G, ∃ q : ℕ, q.Prime ∧ p<q ∧ center p<q ∧ q≤center p+(center p).sqrt ∧
        let n := p*q
        let s := ceilSqrt (24*n)
        let z := (s^2-24*n).sqrt
        s=3*p+2*q ∧ s^2=24*n+z^2 ∧ (n.gcd ((s+z)/2)=p ∨ n.gcd ((s+z)/2)=q) := by
  classical
  have lower {p : ℕ} (hp : p∈P) : 2≤center p := by
    have big := (data p hp).2.1
    dsimp [center]
    omega
  refine ⟨P \ missing P,sdiff_subset,?_,?_⟩
  · have card : (P \ missing P).card+(missing P).card=P.card :=
      card_sdiff_add_card_eq_card (filter_subset _ P : missing P⊆P)
    have bound := missing_bound P u (fun p hp => ⟨lower hp,(data p hp).2.2⟩)
    omega
  · intro p good
    obtain ⟨hp,hit⟩ := mem_sdiff.mp good
    have near : next (center p)≤center p+(center p).sqrt := le_of_not_gt
      (fun bad => hit (mem_filter.mpr ⟨hp,bad⟩))
    obtain ⟨pp,big,_⟩ := data p hp
    obtain ⟨after,qp⟩ := next_data (center p)
    refine ⟨_,qp,?_,after,near,first_trace pp qp big after near⟩
    have pc : p≤center p := by dsimp [center]; omega
    exact pc.trans_lt after

end PrimeFactors.PrimeGapPopulation
