import PrimeFactors.LargeQuarticDenominatorCoverage
import PrimeFactors.ReduceQuarticDenominator

/-! The full range of denominators for which the earlier size test guarantees
gcd recovery is contained in the interval through 2^512. -/
namespace PrimeFactors.AllSmallQuarticDenominatorCoverage

open Finset
open MixedPrefixSample (eligible)
open ScaledQuarticMenuBound (covered)
open LargeQuarticDenominatorCoverage (family)
open scoped Classical
set_option exponentiation.threshold 8192
set_option maxRecDepth 8192
attribute [local irreducible] eligible

/-- Cancellation preserves the same finite search interval. -/
theorem reduce (D : ℕ) :
    covered (Icc 1 D)=(Icc 1 D).biUnion family := by
  ext v
  simp only [covered,mem_biUnion]
  constructor
  · rintro ⟨d,hd,hit⟩
    obtain ⟨mem,raw⟩ := mem_filter.mp hit
    obtain ⟨_,ord,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp mem
    have sf := (Nat.squarefree_mul ((Nat.coprime_primes pp qp).mpr ord.ne)).mpr ⟨pp.squarefree,qp.squarefree⟩
    obtain ⟨t,_,tp,td,x,y,xp,yp,cop,form,gap⟩ :=
      ReduceQuarticDenominator.primitive_choice (mem_Icc.mp hd).1 sf raw
    exact ⟨t,mem_Icc.mpr ⟨tp,td.trans (mem_Icc.mp hd).2⟩,
      LargeQuarticDenominatorCoverage.mem_family.mpr ⟨mem,x,y,xp,yp,cop,form,gap⟩⟩
  · rintro ⟨d,hd,hit⟩
    obtain ⟨mem,x,y,xp,yp,_,form,gap⟩ := LargeQuarticDenominatorCoverage.mem_family.mp hit
    exact ⟨d,hd,mem_filter.mpr ⟨mem,RecognizingQuarticProducts.factors x y,
      ComplementaryQuarticProducts.mem_choices.mpr ⟨x,y,xp,yp,form,gap,rfl⟩⟩⟩

theorem count : (covered (Icc 1 (2^512))).card≤2^1794 := by
  rw [reduce]
  have sumBound := Finset.sum_le_sum (s:=Icc 1 (2^512)) (fun d hd =>
    LargeQuarticDenominatorCoverage.one (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)
  apply (card_biUnion_le.trans sumBound).trans
  rw [sum_const,Nat.card_Icc,smul_eq_mul]
  decide +kernel

theorem rare : 2^227*(covered (Icc 1 (2^512))).card<eligible.card := by
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ count)).trans_lt
    ((by decide +kernel : 21000000*(2^227*2^1794)<2^2046).trans
      (MixedPrefixSample.denominator ChebyshevPrimeSample.prime_count))

/-- Every denominator satisfying the known sufficient condition for automatic
factor recovery is covered by the population theorem. -/
theorem extraction_range {n d : ℕ} (width : n<2^2048) (budget : 6*d^4≤n) : d<2^512 := by
  apply (Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp
  rw [show ((2:ℕ)^512)^4=2^2048 by decide +kernel]
  omega

end PrimeFactors.AllSmallQuarticDenominatorCoverage
