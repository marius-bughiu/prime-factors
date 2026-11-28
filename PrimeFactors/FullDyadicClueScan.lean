import PrimeFactors.DyadicClueFullSumClass
import PrimeFactors.WithinResidueSearchFloor
import PrimeFactors.LocalMidpointLanes

/-! Count the earlier false sums compatible with a true 160-bit factor
suffix at every binary modulus in the ordinary ascending sum scan. -/
namespace PrimeFactors.FullDyadicClueScan

open Finset DyadicClueFullSumClass
open WithinResidueSearchFloor (low target short)
open MixedPrefixSample (eligible)
open private PrimeFactors.DyadicClueFullSumClass.cop_two from PrimeFactors.DyadicClueFullSumClass
open private PrimeFactors.LocalMidpointLanes.odd_square from PrimeFactors.LocalMidpointLanes
open scoped Classical
set_option exponentiation.threshold 4096
attribute [local irreducible] eligible

def bits (n : ℕ) : ℕ := if n%8=5 then 162 else 161

private theorem possible_congr {k : ℕ} {n a b s : ℤ} (eq : a ≡ b [ZMOD (2:ℤ)^k]) :
    Possible k n a s ↔ Possible k n b s := by
  constructor <;> intro h e <;> obtain ⟨x,hx,hit⟩ := h e
  · exact ⟨x,hx.trans eq,hit⟩
  · exact ⟨x,hx.trans eq.symm,hit⟩

private theorem for_gap {k t : ℕ} {p q s g : ℤ} (le : t<k)
    (po : Odd p) (go : Odd g) (disc : p^2-p*q=2^t*g) :
    Possible k (p*q) p s ↔ s ≡ p+q [ZMOD (2:ℤ)^(k+t)] := by
  rw [full_class (by omega) le.le po go disc,if_neg le.ne,show p^2+p*q=p*(p+q) by ring]
  constructor
  · intro h
    have div := h.dvd
    rw [←mul_sub] at div
    exact Int.modEq_iff_dvd.mpr ((PrimeFactors.DyadicClueFullSumClass.cop_two po).pow_left.dvd_of_dvd_mul_left div)
  · exact fun eq => eq.mul_left p

/-- On these three product classes the supplied suffix leaves exactly one
arithmetic progression, even after all dyadic modular tests. -/
theorem class_160 {p q s : ℕ} (po : Odd p)
    (branch : (p*q)%8=3 ∨ (p*q)%8=5 ∨ (p*q)%8=7) :
    Possible 160 (p*q:ℕ) (p%2^160:ℕ) s ↔ s ≡ p+q [MOD 2^(bits (p*q))] := by
  have same : ((p%2^160:ℕ):ℤ) ≡ (p:ℤ) [ZMOD (2:ℤ)^160] := by
    exact_mod_cast Int.natCast_modEq_iff.mpr (Nat.mod_modEq p (2^160))
  rw [possible_congr same]
  have unit : Odd (p:ℤ) := by exact_mod_cast po
  have sq : (p:ℤ)^2%8=1 := Eq.symm (Int.modEq_iff_dvd.mpr
    (PrimeFactors.LocalMidpointLanes.odd_square unit))
  have cast : ((p:ℤ)*q)%8=3 ∨ ((p:ℤ)*q)%8=5 ∨ ((p:ℤ)*q)%8=7 := by exact_mod_cast branch
  let D := (p:ℤ)^2-p*q
  have normalize (t : ℕ) (small : t<160) (valuation : ∃ g : ℤ,Odd g ∧ D=2^t*g) :
      Possible 160 (p*q:ℕ) p s ↔ s ≡ p+q [MOD 2^(160+t)] := by
    obtain ⟨g,odd,eq⟩ := valuation
    rw [←Int.natCast_modEq_iff]
    push_cast
    exact for_gap small unit odd eq
  by_cases five : (p*q)%8=5
  · rw [bits,if_pos five]
    apply normalize 2 (by decide)
    have n5 : ((p:ℤ)*q)%8=5 := by exact_mod_cast five
    have residue : D%8=4 := by dsimp [D]; omega
    exact ⟨D/4,⟨D/8,by omega⟩,by omega⟩
  · rw [bits,if_neg five]
    apply normalize 1 (by decide)
    have ne5 : ((p:ℤ)*q)%8≠5 := by exact_mod_cast five
    have residue : D%4=2 := by dsimp [D]; omega
    exact ⟨D/2,⟨D/4,by omega⟩,by omega⟩

/-- The supplied suffix is always p modulo 2^160. The successful endpoint
is excluded from this set of earlier tests. -/
noncomputable def wrong (v : ℕ×ℕ) : Finset ℕ := (Ico (low v) (target v)).filter
  (fun s : ℕ => Possible 160 (v.1*v.2:ℕ) (v.1%2^160:ℕ) s)

private theorem count_class (lo s m : ℕ) :
    ((Ico lo s).filter (fun t => t ≡ s [MOD m])).card=(s-lo)/m := by
  rw [←Nat.Ioc_filter_dvd_card_eq_div]
  apply card_bij' (fun t _ => s-t) (fun z _ => s-z)
  · intro t ht
    obtain ⟨i,e⟩ := mem_filter.mp ht
    obtain ⟨l,r⟩ := mem_Ico.mp i
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,(Nat.modEq_iff_dvd' r.le).mp e⟩
  · intro z hz
    obtain ⟨i,dv⟩ := mem_filter.mp hz
    obtain ⟨pos,cap⟩ := mem_Ioc.mp i
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,
      (Nat.modEq_iff_dvd' (Nat.sub_le s z)).mpr ?_⟩
    rwa [show s-(s-z)=z by omega]
  · intro t ht
    have := (mem_Ico.mp (mem_filter.mp ht).1).2
    omega
  · intro z hz
    have := (mem_Ioc.mp (mem_filter.mp hz).1).2
    omega

theorem exact_count {p q : ℕ} (po : Odd p) (branch : (p*q)%8=3 ∨ (p*q)%8=5 ∨ (p*q)%8=7) :
    (wrong (p,q)).card=(p+q-ceilSqrt (4*(p*q)))/2^(bits (p*q)) := by
  have eq : wrong (p,q)=(Ico (low (p,q)) (p+q)).filter (fun s => s ≡ p+q [MOD 2^(bits (p*q))]) := by
    ext t
    simp only [wrong,target,mem_filter,class_160 po branch]
  rw [eq,count_class]
  rfl

theorem false_square {p q s : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p≤q)
    (earlier : s∈wrong (p,q)) : ¬IsSquare (s^2-4*(p*q)) := by
  obtain ⟨lo,hi⟩ := mem_Ico.mp (mem_filter.mp earlier).1
  change ceilSqrt (4*(p*q))≤s at lo
  change s<p+q at hi
  have twice := Nat.mul_le_mul_right q pp.two_le
  exact fun square => hi.ne (semiprime_sum_of_square_discriminant pp qp ord (ceilSqrt_le_iff.mp lo) (by omega) square)

/-- An unconditional absolute bound on the union of the two exceptional
sets. The denominator counts every eligible pair of full-width primes. -/
theorem population :
    2^35*(eligible.filter (fun v =>
      (((v.1*v.2)%8=3 ∨ (v.1*v.2)%8=7) ∧ (wrong v).card<2^739) ∨
      ((v.1*v.2)%8=5 ∧ (wrong v).card<2^738))).card<eligible.card := by
  refine (Nat.mul_le_mul_left _ (card_le_card (t:=short) ?_)).trans_lt WithinResidueSearchFloor.exceptional
  rintro ⟨p,q⟩ h
  obtain ⟨member,bad⟩ := mem_filter.mp h
  change (((p*q)%8=3 ∨ (p*q)%8=7) ∧ (wrong (p,q)).card<2^739) ∨
    ((p*q)%8=5 ∧ (wrong (p,q)).card<2^738) at bad
  obtain ⟨pl,_,_,pp,_⟩ := SumGridPopulation.eligible_data.mp member
  have odd := Nat.odd_iff.mpr (pp.eq_two_or_odd.resolve_left
    (ne_of_gt ((by decide +kernel : 2<FullRangeResidueEstimates.X).trans_le pl)))
  apply mem_filter.mpr
  refine ⟨member,?_⟩
  change p+q<ceilSqrt (4*(p*q))+2^900
  rcases bad with ⟨cls,small⟩|⟨five,small⟩
  · have branch : (p*q)%8=3 ∨ (p*q)%8=5 ∨ (p*q)%8=7 := by tauto
    have ne : (p*q)%8≠5 := by omega
    rw [exact_count odd branch,bits,if_neg ne] at small
    omega
  · rw [exact_count odd (Or.inr (Or.inl five)),bits,if_pos five] at small
    omega

end PrimeFactors.FullDyadicClueScan
