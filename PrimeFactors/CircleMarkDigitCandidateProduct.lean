import PrimeFactors.CircleMarkDigitQueryValue
import PrimeFactors.CircleMarkSparseMaskCapacity

/-! Each digit question groups ordinary candidate divisors. One product gcd
answers the question, and a positive answer already contains the prime. -/
namespace PrimeFactors.CircleMarkDigitCandidateProduct

open Finset CircleMarkMaskDigitReadout CircleMarkDigitCoordinates CircleMarkMidcutReadout
open CircleMarkSparseMaskCapacity CircleMarkSparseMaskProbe CircleMarkJacobiMask
open scoped Classical

/-- The part of the public coordinate interval consistent with p<q<2p. -/
noncomputable def candidates (n : ℕ) : Finset ℕ :=
  (Icc (cutoff n+2) (2*cutoff n+1)).filter fun r => Odd r ∧ r*r≤n ∧ n<2*(r*r)

noncomputable def selected (n : ℕ) (J I : Finset ℕ) : Finset ℕ :=
  (candidates n).filter fun r =>
    let s := (2*cutoff n+1-r)/2
    s/base n∈J ∧ s%base n∈I

/-- Group the selected divisors in one public gcd. -/
noncomputable def divisor (n : ℕ) (J I : Finset ℕ) : ℕ :=
  n.gcd (∏ r ∈ selected n J I, r)

theorem prime_mem {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2) : p∈candidates (p*q) := by
  obtain ⟨lo,hi,_⟩ := CircleMarkJacobiMaskEdge.bounds order bal op oq
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hi⟩,hp.out.odd_of_ne_two op,
    Nat.mul_le_mul_left _ order.le,?_⟩
  simpa only [Nat.mul_left_comm p 2 p] using Nat.mul_lt_mul_of_pos_left bal hp.out.pos

private theorem hasPair {r : ℕ} {C : Finset ℕ} :
    (pairs r C).Nonempty ↔ ∃x∈C, ∃y∈C, x<y ∧ x+y=r := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨mem,lt,sum⟩ := mem_filter.mp hz
    exact ⟨_,(mem_product.mp mem).1,_,(mem_product.mp mem).2,lt,sum⟩
  · rintro ⟨x,hx,y,hy,lt,sum⟩
    exact ⟨(x,y),mem_filter.mpr ⟨mem_product.mpr ⟨hx,hy⟩,lt,sum⟩⟩

/-- The selected numbers are precisely the odd coordinate sums in the
public candidate interval. This includes composite trial divisors. -/
theorem grouped (n : ℕ) (J I : Finset ℕ) (cap : I⊆range (base n)) :
    selected n J I = candidates n ∩ oddSums (coordinates n J I) := by
  ext r
  rw [selected,mem_filter,mem_inter]
  apply and_congr_right
  intro h
  obtain ⟨inside,odd,_,_⟩ := mem_filter.mp h
  obtain ⟨lo,hi⟩ := mem_Icc.mp inside
  have low : cutoff n+1<r := by omega
  obtain ⟨code,_,_⟩ := digits low hi odd
  rw [mem_oddSums,and_iff_right odd,hasPair]
  exact (pair_iff (Nat.succ_pos _) cap low code).symm

/-- Selecting every index recovers exactly the public trial interval. -/
theorem select_all (n : ℕ) :
    selected n (range (base n)) (range (base n))=candidates n := by
  ext r
  rw [selected,mem_filter,and_iff_left_iff_imp]
  intro h
  obtain ⟨inside,odd,_,_⟩ := mem_filter.mp h
  obtain ⟨lo,hi⟩ := mem_Icc.mp inside
  obtain ⟨_,a,b⟩ := digits (show cutoff n+1<r by omega) hi odd
  exact ⟨mem_range.mpr a,mem_range.mpr b⟩

theorem exact {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2) (J I : Finset ℕ)
    (cap : I⊆range (base (p*q))) :
    divisor (p*q) J I = if response (p*q) J I then p else 1 := by
  let A := selected (p*q) J I
  let v := ∏ r ∈ A, r
  have inA : p∈A ↔ response (p*q) J I=true := by
    exact (mem_filter.trans (and_iff_right (prime_mem order bal op oq))).trans
      (query order bal op oq J I cap).symm
  have bounds (r : ℕ) (h : r∈A) : 0<r ∧ r<q ∧ r<2*p := by
    have mem := (mem_filter.mp ((mem_filter.mp h).1)).1
    obtain ⟨a,b⟩ := mem_Icc.mp mem
    have limit := (CircleMarkJacobiMaskEdge.bounds order bal op oq).2.2
    omega
  have atP : p∣v ↔ p∈A := by
    constructor
    · intro hit
      obtain ⟨r,mem,dv⟩ := (hp.out.prime.dvd_finset_prod_iff _).mp hit
      have eqn := Nat.eq_of_dvd_of_lt_two_mul (bounds r mem).1.ne' dv (bounds r mem).2.2
      simpa only [eqn] using mem
    · intro mem
      exact dvd_prod_of_mem id mem
  have atQ : ¬q∣v := by
    intro hit
    obtain ⟨r,mem,dv⟩ := (hq.out.prime.dvd_finset_prod_iff _).mp hit
    exact Nat.not_dvd_of_pos_of_lt (bounds r mem).1 (bounds r mem).2.1 dv
  change (p*q).gcd v=_
  split_ifs with yes
  · exact (Nat.gcd_comm ..).trans (NormBatchGCD.one_batch hq.out (atP.mpr (inA.mpr yes)) atQ)
  · exact Nat.coprime_mul_iff_left.mpr
      ⟨hp.out.coprime_iff_not_dvd.mpr (fun h => yes (inA.mp (atP.mp h))),hq.out.coprime_iff_not_dvd.mpr atQ⟩

/-- One gcd suffices if the entire eligible product has been constructed. -/
theorem all_gcd {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2) :
    (p*q).gcd (∏ r ∈ candidates (p*q),r)=p := by
  let all := range (base (p*q))
  have mem : p∈selected (p*q) all all := (select_all (p*q)).symm ▸ prime_mem order bal op oq
  have yes := (query order bal op oq all all Subset.rfl).mpr (mem_filter.mp mem).2
  simpa only [divisor,all,select_all,yes,if_true] using exact order bal op oq all all Subset.rfl

end PrimeFactors.CircleMarkDigitCandidateProduct
