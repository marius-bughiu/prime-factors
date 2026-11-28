import PrimeFactors.QuarticLocalSumBits
import PrimeFactors.WithinResidueSearchFloor

/-! Count the earlier integer sums compatible with a supplied quartic-local
answer and all powers of two, in the ordinary increasing sum scan. -/
namespace PrimeFactors.QuarticSignedSumPrefix

open Finset QuarticLocalClassification QuarticLocalSumBits
open WithinResidueSearchFloor (low target short)
open MixedPrefixSample (eligible)
open scoped Classical

set_option exponentiation.threshold 4096
attribute [local irreducible] eligible

/-- The answer is supplied free of charge. At every dyadic modulus the
two modular factors must both have the sign it selects modulo four. -/
def Compatible (n s : ℕ) : Prop :=
  ∀ k : ℕ, Signed (if Tests n then 1 else 3) (2^k) n s

private theorem every_depth {r n s v : ℤ}
    (high : ∀ k : ℕ, Signed r (2^(k+5)) n s ↔ s%32=v) :
    (∀ k : ℕ, Signed r (2^k) n s) ↔ s%32=v := by
  refine ⟨fun h => (high 0).mp (h 5),?_⟩
  intro eq k
  obtain ⟨a,b,prod,sum,pa,pb⟩ := (high k).mpr eq
  have dv : ((2^k:ℕ):ℤ)∣((2^(k+5):ℕ):ℤ) := by
    exact_mod_cast pow_dvd_pow (2:ℕ) (show k≤k+5 by omega)
  exact ⟨a,b,prod.of_dvd dv,sum.of_dvd dv,pa,pb⟩

/-- On this product class the true sum determines the entire accepted
residue class for the supplied answer. -/
theorem compatible_iff {p q s : ℕ} (pp : p.Prime) (qp : q.Prime)
    (po : Odd p) (qo : Odd q) (five : (p*q)%16=5) :
    Compatible (p*q) s ↔ s%32=(p+q)%32 := by
  have good : ((p:ℤ)*q)%16=5 := by exact_mod_cast five
  have plus := fun k => (signed32 (s:=(s:ℤ)) good k).1
  have minus := fun k => (signed32 (s:=(s:ℤ)) good k).2
  obtain ⟨trueSign,falseSign⟩ := sign32 pp qp po qo five
  have cast : ((s:ℤ)%32=((p:ℤ)+q)%32) ↔ s%32=(p+q)%32 := by
    constructor <;> intro eq <;> exact_mod_cast eq
  unfold Compatible
  push_cast
  by_cases yes : Tests (p*q)
  · simpa only [if_pos yes,every_depth plus,←trueSign.mp yes] using cast
  · simpa only [if_neg yes,every_depth minus,←falseSign.mp yes] using cast

/-- Only sums strictly before the actual hit are counted. -/
noncomputable def wrong (v : ℕ×ℕ) : Finset ℕ :=
  (Ico (low v) (target v)).filter (fun s => Compatible (v.1*v.2) s)

private theorem residue_card (a b : ℕ) :
    ((Ico a b).filter (fun t => t%32=b%32)).card=(b-a)/32 := by
  trans (Icc 1 ((b-a)/32)).card
  · apply card_bij (fun t _ => (b-t)/32)
    · intro t ht
      obtain ⟨it,eq⟩ := mem_filter.mp ht
      obtain ⟨lo,hi⟩ := mem_Ico.mp it
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    · intro t ht u hu same
      obtain ⟨it,tmod⟩ := mem_filter.mp ht
      obtain ⟨iu,umod⟩ := mem_filter.mp hu
      have lt := (mem_Ico.mp it).2
      have lu := (mem_Ico.mp iu).2
      omega
    · intro j hj
      obtain ⟨jp,limit⟩ := mem_Icc.mp hj
      refine ⟨b-32*j,mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩,by omega⟩
  · rw [Nat.card_Icc]
    omega

/-- Exact count from the actual arithmetic lower endpoint to the true sum. -/
theorem exact_count {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (po : Odd p)
    (qo : Odd q) (five : (p*q)%16=5) :
    (wrong (p,q)).card=(p+q-ceilSqrt (4*(p*q)))/32 := by
  have eq : wrong (p,q) = (Ico (low (p,q)) (p+q)).filter (fun s => s%32=(p+q)%32) := by
    ext t
    simp only [wrong,mem_filter,target,compatible_iff pp qp po qo five]
  rw [eq,residue_card]
  rfl

/-- Every surviving sum counted here still fails the exact integer square test. -/
theorem false_square {p q t : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p≤q)
    (mem : t∈wrong (p,q)) : ¬IsSquare (t^2-4*(p*q)) := by
  obtain ⟨lo,hi⟩ := mem_Ico.mp (mem_filter.mp mem).1
  change ceilSqrt (4*(p*q))≤t at lo
  change t<p+q at hi
  have bound : p+q≤p*q := by
    have twice := Nat.mul_le_mul_right q pp.two_le
    omega
  exact fun hit => hi.ne (semiprime_sum_of_square_discriminant pp qp ord
    (ceilSqrt_le_iff.mp lo) (by omega) hit)

/-- The denominator is the full unconditioned population of sorted distinct
1,024-bit primes with 2,048-bit product. The numerator includes only products
equal to five modulo sixteen with fewer than the stated number of false sums. -/
theorem population :
    2^35*(eligible.filter (fun v => (v.1*v.2)%16=5 ∧ (wrong v).card<2^895)).card <
      eligible.card := by
  have sub : eligible.filter (fun v => (v.1*v.2)%16=5 ∧ (wrong v).card<2^895) ⊆ short := by
    rintro ⟨p,q⟩ inside
    obtain ⟨ok,five,small⟩ := mem_filter.mp inside
    obtain ⟨pl,ord,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp ok
    have lowPrime : 2<FullRangeResidueEstimates.X := by decide +kernel
    have po := pp.eq_two_or_odd.resolve_left (ne_of_gt (lowPrime.trans_le pl))
    have qo := qp.eq_two_or_odd.resolve_left (ne_of_gt ((lowPrime.trans_le pl).trans ord))
    rw [exact_count pp qp (Nat.odd_iff.mpr po) (Nat.odd_iff.mpr qo) five] at small
    apply mem_filter.mpr
    refine ⟨ok,?_⟩
    change p+q<ceilSqrt (4*(p*q))+2^900
    have scale : 32*2^895=2^900 := by decide +kernel
    omega
  exact (Nat.mul_le_mul_left _ (card_le_card sub)).trans_lt WithinResidueSearchFloor.exceptional

/-- Counts for the two 32-bit products differing at bit 26. -/
theorem one_bit_counts : (wrong (48541,59209)).card=16 ∧ (wrong (48487,60659)).card=21 := by
  have ceiling {n c : ℕ} (lo : (c-1)^2<n) (hi : n≤c^2) : ceilSqrt n=c := by
    have upper := ceilSqrt_le_iff.mpr hi
    have lower : ¬ceilSqrt n≤c-1 := fun h => (not_le_of_gt lo) (ceilSqrt_le_iff.mp h)
    omega
  have a : ceilSqrt (4*(48541*59209))=107221 := ceiling (by decide +kernel) (by decide +kernel)
  have b : ceilSqrt (4*(48487*60659))=108466 := ceiling (by decide +kernel) (by decide +kernel)
  constructor
  · apply (exact_count (p:=48541) (q:=59209) (by norm_num) (by norm_num)
      (by decide) (by decide) (by decide)).trans
    rw [a]
  · apply (exact_count (p:=48487) (q:=60659) (by norm_num) (by norm_num)
      (by decide) (by decide) (by decide)).trans
    rw [b]

end PrimeFactors.QuarticSignedSumPrefix
