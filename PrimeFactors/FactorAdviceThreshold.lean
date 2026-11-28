import PrimeFactors.FiveSquareAdviceLimits
import PrimeFactors.FactorOrbitAdviceMenu
import PrimeFactors.FiveSquareActualSumClue

/-! A sharp threshold in the number of *supplied* bits. The visible
product remainder selects the menu, and the secret message selects one
complete list from it. Each guess names an unordered modular factor pair. -/
namespace PrimeFactors.FactorAdviceThreshold

open FactorOrbitAdviceFloor FactorOrbitAdviceMenu
open FiveSquareAdviceLimits (chosen hit averagePrime primeMean primePrefix)
open FiveSquarePolicy (U)
open FiveSquarePrimeSupply (m Endpoints)
open private PrimeFactors.FiveSquareFactorGuessing.lift from PrimeFactors.FiveSquareFactorGuessing
open scoped Classical

set_option maxRecDepth 4096
attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card

/-- All bit widths through 24 have the same limiting comparison,
including any choice of message based on the exact integer prime pair. -/
theorem short {li : ℕ→ℝ} (h : Endpoints li) {bits : ℕ} (width : bits≤24)
    (P : ∀ n : U, Menu n (2^bits)) (select : ℕ×ℕ → Fin (2^bits)) :
    589232/10000 < primeMean P select ∧ primePrefix P select < 855824/1000000 := by
  have le : 2^bits≤FiveSquareAdviceLimits.Codes := Nat.pow_le_pow_right (by decide) width
  choose Q eq using fun n : U => pad (by positivity) le (P n)
  let k (z : ℕ×ℕ) := Fin.castLE le (select z)
  have same (z : ℕ×ℕ) : chosen Q (k z)=chosen P (select z) := by
    funext a b
    exact eq (a*b) (select z) a
  have bound := FiveSquareAdviceLimits.bits24 h Q k
  simpa only [primeMean,primePrefix,same] using bound

/-- A supplied 25-bit message beats 31 mean guesses on the actual
population and guarantees 59 guesses for every eligible pair. -/
theorem sufficient {li : ℕ→ℝ} (h : Endpoints li) :
    ∃ (P : ∀ n : U, Menu n (2^25)) (select : ℕ×ℕ → Fin (2^25)),
      primeMean P select<31 ∧ ∀ z : ℕ×ℕ,
        PrimeFactors.FiveSquareFactorGuessing.lift (chosen P (select z)) z.1 z.2≤59 := by
  obtain ⟨base,_,mean⟩ := FactorOrbitAdviceConstruction.five_actual h
  have pos : 0<2^25 := by decide
  obtain ⟨P,good⟩ := realizes pos base
  let msg (a b : U) := FactorOrbitAdviceConstruction.code pos
    ((base (a*b)) (FactorOrbitGuessRanks.label (a*b) a)).val
  let select (z : ℕ×ℕ) : Fin (2^25) :=
    if a : IsUnit (z.1 : ZMod m) then
      if b : IsUnit (z.2 : ZMod m) then msg a.unit b.unit else ⟨0,pos⟩
    else ⟨0,pos⟩
  have same (z : ℕ×ℕ) : PrimeFactors.FiveSquareFactorGuessing.lift (chosen P (select z)) z.1 z.2=
      PrimeFactors.FiveSquareFactorGuessing.lift (FactorOrbitAdviceConstruction.advised (2^25) base) z.1 z.2 := by
    unfold PrimeFactors.FiveSquareFactorGuessing.lift select
    split_ifs <;> first | exact good _ _ | rfl
  refine ⟨P,select,?_,fun z => ?_⟩
  · simpa only [primeMean,averagePrime,same,FactorOrbitAdviceConstruction.primeMean,
      FiveSquareAllPrimeRanks.actual] using mean
  · rw [same]
    unfold PrimeFactors.FiveSquareFactorGuessing.lift
    split_ifs <;> first | apply FactorOrbitAdviceConstruction.five_worst | decide

/-- For the average achieved with a fully disclosed sum remainder,
25 is the smallest bit width that can do at least as well with an
arbitrary factor-informed message, under the stated endpoint estimates. -/
theorem least_bits {li : ℕ→ℝ} (h : Endpoints li) :
    ∃ s : FiveSquareActualSumClue.Policy,
      IsLeast (Set.range FiveSquareActualSumClue.primeMean) (FiveSquareActualSumClue.primeMean s) ∧
      IsLeast {bits : ℕ | ∃ (P : ∀ n : U, Menu n (2^bits)) (select : ℕ×ℕ→Fin (2^bits)),
        primeMean P select≤FiveSquareActualSumClue.primeMean s} 25 := by
  obtain ⟨s,minimal,close⟩ := FiveSquareActualSumClue.within_thousandth h
  obtain ⟨lo,hi⟩ := abs_lt.mp close
  refine ⟨s,minimal,?_,?_⟩
  · obtain ⟨P,select,mean,_⟩ := sufficient h
    exact ⟨P,select,mean.le.trans (by linarith only [lo])⟩
  · rintro bits ⟨P,select,success⟩
    by_contra! less
    have bound := (short h (show bits≤24 by omega) P select).1
    linarith only [success,bound,hi]

end PrimeFactors.FactorAdviceThreshold
