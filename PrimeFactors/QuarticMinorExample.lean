import PrimeFactors.DivisorWindowRank
import Mathlib.Tactic.NormNum.Prime

namespace PrimeFactors.QuarticMinorExample

open QuarticDivisorWindow QuarticFactorLane DivisorWindowRank

/-- Four rows returned at public window 910 of the complete 49-bit experiment,
with coefficients in increasing degree. -/
noncomputable def rows : Fin 4 → Fin 5 → ℤ :=
  ![![3191663491950,21939948761,-145492857,-514007,2598],
    ![14167348053564,117239739800,-46103779,236784,876],
    ![981288606744,-31402690128,-386311788,-683943,-3280],
    ![-6670260952062,-91415687647,-127880546,1625491,1889]]

abbrev input : ℕ := 502005281288939
abbrev center : ℕ := 17838859
abbrev anchor : ℤ := 251002631725040

theorem short_rows : (input:ℤ) ∣ (center:ℤ)+2*anchor ∧
    ∀ i, jets (rows i) input anchor ∧ height (rows i) 291 < ((center:ℤ)-2*291)^2 := by
  constructor
  · decide +kernel
  · intro i
    fin_cases i <;> unfold jets <;> decide +kernel

theorem denominator : (nonconstant rows).det=397559205769926792824245573379 := by
  rw [Matrix.det_succ_row_zero,Fin.sum_univ_four]
  simp only [Matrix.det_fin_three]
  decide +kernel

theorem common_root (i : Fin 4) : value (weights (rows i)) 1 (-114)=0 := by
  fin_cases i <;> decide +kernel

theorem numerator : ((nonconstant rows).updateCol 0 (fun i => -rows i 0)).det =
    -45321749457771654381963995365206 := by
  rw [cramer_offset rows (-114) common_root,denominator]
  decide +kernel

/-- Dividing the observed determinant by N gives the exact square of the cofactor.
Square root and division reconstruct the prime pair, including primality. -/
theorem square_recovers :
    let q := ((nonconstant rows).det.natAbs / input).sqrt
    let p := input/q
    p=17838631 ∧ q=28141469 ∧ Nat.Prime p ∧ Nat.Prime q ∧ p*q=input := by
  rw [denominator]
  have square : Int.natAbs 397559205769926792824245573379 / input = 28141469*28141469 := by decide +kernel
  have first : input / 28141469 = 17838631 := by decide +kernel
  simp only [square,Nat.sqrt_eq,first,true_and,eq_self]
  exact ⟨by norm_num1,by norm_num1,True.intro⟩

end PrimeFactors.QuarticMinorExample
