import PrimeFactors.ShiftedSquareSumReadout
import PrimeFactors.CyclotomicDigitPeriod
import PrimeFactors.ShiftedSquareSumCoverage
import PrimeFactors.SumGridPopulation

/-! A previously certified full-width product where the shifted-square
criterion fails despite passing the product's gate modulo eight. -/
namespace PrimeFactors.ShiftedSquareSumFullSize

open GroupedNormExamples

set_option exponentiation.threshold 2048
set_option maxRecDepth 4096
attribute [local irreducible] MixedPrefixSample.eligible ShiftedSquareSumCoverage.successes

/-- The gap of the two known comparison primes has exactly 540 trailing
zero bits. The 1,025-bit protocol would require exactly 512. -/
theorem adjacent_gap :
    ∃ z : ℤ, Odd z ∧ (adjacentLarge:ℤ)-adjacentSmall=2^540*z := by
  refine ⟨((adjacentLarge:ℤ)-adjacentSmall)/2^540,Int.odd_iff.mpr ?_,?_⟩ <;> decide +kernel

/-- The modulus-eight gate passes on this input, but the proposed integer
sum is rejected. The proof reuses the existing prime and size certificates. -/
theorem adjacent_miss :
    CyclotomicDigitPeriod.FullPair adjacentN adjacentSmall adjacentLarge ∧
    adjacentN%8=1 ∧ ShiftedSquareSumReadout.read adjacentN 511=none := by
  have pair := CyclotomicDigitPeriod.grouped_examples.1
  refine ⟨pair,by decide +kernel,?_⟩
  rw [pair.1]
  have predicts := ShiftedSquareSumReadout.read_iff (j:=511) (by decide)
    pair.2.1 pair.2.2.1 pair.2.2.2.2.1.le (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have rejects : ¬∃ z : ℤ, Odd z ∧ (adjacentLarge:ℤ)-adjacentSmall=2^(511+1)*z := by
    rintro ⟨z,oz,h⟩
    have evenPart : (((adjacentLarge:ℤ)-adjacentSmall)/2^(511+1))%2=0 := by decide +kernel
    rw [h,Int.mul_ediv_cancel_left _ (by positivity : (2:ℤ)^(511+1)≠0)] at evenPart
    have one := Int.odd_iff.mp oz
    omega
  exact Option.not_isSome_iff_eq_none.mp (fun yes => rejects (predicts.mp yes))

/-- Fraction of the full eligible population for which the actual
single-candidate readout returns a split. -/
theorem full_population :
    2^500*(MixedPrefixSample.eligible.filter
      (fun v => (ShiftedSquareSumReadout.read (v.1*v.2) 511).isSome=true)).card <
    MixedPrefixSample.eligible.card := by
  have same : (MixedPrefixSample.eligible.filter
      (fun v => (ShiftedSquareSumReadout.read (v.1*v.2) 511).isSome=true)) =
      ShiftedSquareSumCoverage.successes 511 := by
    classical
    unfold ShiftedSquareSumCoverage.successes
    apply Finset.filter_congr
    rintro ⟨p,q⟩ member
    obtain ⟨pl,ord,qh,pp,qp,size⟩ := SumGridPopulation.eligible_data.mp member
    have p2 : 2<p := (by decide +kernel : 2<FullRangeResidueEstimates.X).trans_le pl
    have po := pp.odd_of_ne_two p2.ne'
    have qo := qp.odd_of_ne_two (p2.trans ord).ne'
    have hi : q<2^1024 := qh
    have lo : 2^1023≤p := pl
    have sz : 2^1025≤2*(p+q) := by rw [show (2:ℕ)^1025=4*2^1023 by decide +kernel]; omega
    have cap : p+q<2^1025 := by rw [show (2:ℕ)^1025=2*2^1024 by decide +kernel]; omega
    by_cases gate : (p*q)%8=1
    · have gz : (p:ℤ)*q ≡ 1 [ZMOD 8] := by
        exact_mod_cast Int.natCast_modEq_iff.mpr (show p*q ≡ 1 [MOD 8] from gate)
      change _ ↔ _ ∧ OddWidthSumPredictions.predicts _ _ _
      rw [and_iff_right gz,OddWidthSumPredictions.true_iff (by decide)
        (by exact_mod_cast po) (by exact_mod_cast qo) gz]
      exact ShiftedSquareSumReadout.read_iff (by decide) pp qp ord.le po qo gate sz cap
    · have gz : ¬(p:ℤ)*q ≡ 1 [ZMOD 8] := by
        intro z
        apply gate
        have now : ((p*q:ℕ):ℤ) ≡ (1:ℕ) [ZMOD (8:ℕ)] := by simpa using z
        exact Int.natCast_modEq_iff.mp now
      change (ShiftedSquareSumReadout.read (p*q) 511).isSome=true ↔ _ ∧ _
      simp only [ShiftedSquareSumReadout.read,gate,false_and,if_false,Option.isSome_none,
        Bool.false_eq_true,gz]
  rw [same]
  exact ShiftedSquareSumCoverage.full_width

end PrimeFactors.ShiftedSquareSumFullSize
