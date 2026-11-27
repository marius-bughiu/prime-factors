import PrimeFactors.PairwiseSumCounts
import PrimeFactors.ThreeTestMarginals

/-! Exact counts for four consecutive permitted sums at every start in
one complete period of the 3, 13 and 11 tests for product residue 665. -/
namespace PrimeFactors.FourRowResidueCounts

open ThreeTestMarginals

/-- The three bit masks list all permitted sum residues of 665. -/
def row (s : ℕ) : Row :=
  ((1:ℕ).testBit (s%3), (3372:ℕ).testBit (s%13), (1386:ℕ).testBit (s%11))

private theorem same_residue {n m : ℕ} (h : n%1716=665) (div : m ∣ 1716) :
    (n : ZMod m) = (665 : ZMod m) := by
  apply (ZMod.natCast_eq_natCast_iff' n 665 m).mpr
  rw [←Nat.mod_mod_of_dvd n div,h]

/-- A pass in a table is exactly the original factor-pair congruence. -/
theorem row_spec {n : ℕ} (h : n%1716=665) (s : ℕ) :
    ((row s).1 = true ↔ AdmissibleSum (n : ZMod 3) (s : ZMod 3)) ∧
    ((row s).2.1 = true ↔ AdmissibleSum (n : ZMod 13) (s : ZMod 13)) ∧
    ((row s).2.2 = true ↔ AdmissibleSum (n : ZMod 11) (s : ZMod 11)) := by
  have a : ∀ z : ZMod 3, (1:ℕ).testBit z.val = true ↔ AdmissibleSum 665 z := by
    unfold AdmissibleSum; decide +kernel
  have b : ∀ z : ZMod 13, (3372:ℕ).testBit z.val = true ↔ AdmissibleSum 665 z := by
    unfold AdmissibleSum; decide +kernel
  have c : ∀ z : ZMod 11, (1386:ℕ).testBit z.val = true ↔ AdmissibleSum 665 z := by
    unfold AdmissibleSum; decide +kernel
  rw [same_residue h (by decide : 3 ∣ 1716), same_residue h (by decide : 13 ∣ 1716),
    same_residue h (by decide : 11 ∣ 1716)]
  simpa only [row, ZMod.val_natCast] using
    And.intro (a (s : ZMod 3)) (And.intro (b (s : ZMod 13)) (c (s : ZMod 11)))

/-- At index i the four rows are the sums 2+4i through 14+4i. -/
def window (i : ℕ) : List Row := [row (2+4*i),row (6+4*i),row (10+4*i),row (14+4*i)]

theorem period (i : ℕ) : window (i+429) = window i := by
  have periodic (s : ℕ) : row (s+1716) = row s := by
    unfold row
    simp only [Nat.add_mod, show 1716%3=0 by decide, show 1716%13=0 by decide,
      show 1716%11=0 by decide, Nat.add_zero, Nat.mod_mod]
  unfold window
  simp only [Nat.mul_add, show 4*429=1716 by decide, ←Nat.add_assoc, periodic]

/-- Sharp lower and upper bounds from the margins, and the actual common count. -/
noncomputable def result (i : ℕ) : ℤ × ℤ × ℕ :=
  let rows := window i
  let margins := observe rows
  (lower margins, upper margins, triple rows)

noncomputable def outcomes : List (ℤ × ℤ × ℕ) := (List.range 429).map result

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The counts account for all 429 alignments. In exactly 24, the bounds
allow 0 or 1, with twelve instances of each actual answer. -/
theorem census : outcomes.length = 429 ∧ outcomes.count (0,0,0) = 275 ∧
    outcomes.count (1,1,1) = 128 ∧ outcomes.count (2,2,2) = 2 ∧
    outcomes.count (0,1,0) = 12 ∧ outcomes.count (0,1,1) = 12 := by
  decide +kernel

end PrimeFactors.FourRowResidueCounts
