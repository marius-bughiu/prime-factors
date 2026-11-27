import PrimeFactors.FactorSum

/-! Complete lists of product residues and spacings for which two admissible sums
cannot occur. All residues, including a zero product or zero spacing, are included. -/
namespace PrimeFactors.FactorSumSpacingSmall

private noncomputable def sumDecidable {m : ℕ} [NeZero m] (n s : ZMod m) :
    Decidable (AdmissibleSum n s) := by
  unfold AdmissibleSum
  infer_instance

attribute [local instance] sumDecidable

/-- Only the odd spacing of an odd product fails modulo two. -/
theorem two (n t : ZMod 2) :
    ¬(∃ s : ZMod 2, AdmissibleSum n s ∧ AdmissibleSum n (s+t)) ↔ n=1 ∧ t=1 := by
  revert n t
  decide +kernel

/-- The nonsquare product has a single sum residue modulo three. -/
theorem three (n t : ZMod 3) :
    ¬(∃ s : ZMod 3, AdmissibleSum n s ∧ AdmissibleSum n (s+t)) ↔ n=2 ∧ t≠0 := by
  revert n t
  decide +kernel

/-- Each nonsquare product misses a different pair of opposite spacings modulo five. -/
theorem five (n t : ZMod 5) :
    ¬(∃ s : ZMod 5, AdmissibleSum n s ∧ AdmissibleSum n (s+t)) ↔
      (n=2 ∧ (t=2 ∨ t=3)) ∨ (n=3 ∧ (t=1 ∨ t=4)) := by
  revert n t
  decide +kernel

/-- Each of the three nonsquares misses its own pair of opposite spacings modulo seven. -/
theorem seven (n t : ZMod 7) :
    ¬(∃ s : ZMod 7, AdmissibleSum n s ∧ AdmissibleSum n (s+t)) ↔
      (n=3 ∧ (t=2 ∨ t=5)) ∨ (n=5 ∧ (t=3 ∨ t=4)) ∨ (n=6 ∧ (t=1 ∨ t=6)) := by
  revert n t
  decide +kernel

end PrimeFactors.FactorSumSpacingSmall
