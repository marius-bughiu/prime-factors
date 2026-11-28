import PrimeFactors.QuotientStripSurvivingBlocks
import PrimeFactors.QuotientStripOddRootPairs

/-!
# Distinct square tests in a quotient-strip scan

For each full block ending strictly before the cutoff, use the selected direction
and its rounded chord endpoints. Keep the positive discriminants whose labels
satisfy the local residue of (1, N). Taking the union counts a square test once,
including when different labels, blocks, or directions give the same integer.
-/

namespace PrimeFactors.QuotientStripDistinctTests

open Finset QuotientStripScheduleCost QuotientStripSlopeRestart
open QuotientStripForcedLabels QuotientStripSurvivingBlocks QuotientStripSlopePopulation
open QuotientStripDiscriminantMultiplicity

set_option exponentiation.threshold 4096
attribute [local irreducible] QuotientStripSlopePopulation.directions

/-- All labels in the rounded interval that meet the surviving-label predicate. -/
noncomputable def blockLabels (n a b : ℕ) (d : Pair) : Finset ℤ := by
  classical
  exact (Icc (QuotientStripWideSlopeGeometry.Rounded.labelLow n a b d.1 d.2)
    (QuotientStripWideSlopeGeometry.Rounded.labelHigh n a b d.1 d.2)).filter
    (Survives n a b d)

theorem mem_blockLabels {n a b : ℕ} {d : Pair} {z : ℤ} :
    z ∈ blockLabels n a b d ↔ Survives n a b d z := by
  classical
  simp only [blockLabels, mem_filter, mem_Icc]
  exact ⟨And.right, fun row => ⟨row.2.2.2.2, row⟩⟩

/-- Distinct positive discriminants in the retained blocks of the scan.
The set uses the residue class defining Survives, for every label in each block. -/
noncomputable def tests (n origin cutoff : ℕ) : Finset ℤ :=
  (kept n origin cutoff).biUnion fun i =>
    let d := owner n origin i
    (blockLabels n (startAt n origin i) (stopAt n origin i) d).image
      (fun z => z ^ 2 - 4 * (weight d : ℤ) * n)

theorem mem_tests {n origin cutoff : ℕ} {D : ℤ} :
    D ∈ tests n origin cutoff ↔
      ∃ i ∈ kept n origin cutoff, ∃ z : ℤ,
        Survives n (startAt n origin i) (stopAt n origin i) (owner n origin i) z ∧
        z ^ 2 - 4 * (weight (owner n origin i) : ℤ) * n = D := by
  classical
  simp only [tests, mem_biUnion, mem_image, mem_blockLabels]

theorem positive_of_mem {n origin cutoff : ℕ} {D : ℤ} (h : D ∈ tests n origin cutoff) :
    0 < D := by
  obtain ⟨i, _, z, row, rfl⟩ := mem_tests.mp h
  exact row.2.2.2.1

private theorem positive_label {n a b : ℕ} {d : Pair} {z : ℤ}
    (row : Survives n a b d z) : 0 < z := by
  have nonnegative := row.1
  have disc := row.2.2.2.1
  by_contra! nonpositive
  have zero : z = 0 := le_antisymm nonpositive nonnegative
  rw [zero, zero_pow (by decide : 2 ≠ 0), zero_sub, neg_pos] at disc
  exact (not_lt_of_ge (by positivity)) disc

/-- Even complete sharing of identical discriminant tests leaves more than
2 ^ 635 distinct positive integers in every window meeting the endpoint bounds. -/
theorem distinct_tests {p q origin cutoff : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (odd : Odd (p * q)) (W : Window (p * q) origin cutoff) :
    2 ^ 635 < (tests (p * q) origin cutoff).card := by
  classical
  let N := p * q
  let S := directions (2 ^ 327)
  let witness (d : Pair) (z : ℤ) := ∃ i ∈ kept N origin cutoff,
    owner N origin i = d ∧ Survives N (startAt N origin i) (stopAt N origin i) d z
  let label (d : Pair) := Classical.epsilon (witness d)
  have picked (d : Pair) (hd : d ∈ S) : witness d (label d) := by
    obtain ⟨i, hi, _, _, _, own, _, z, row⟩ := two_for_each W hd
    exact Classical.epsilon_spec (p := witness d) ⟨z, i, hi, own, row⟩
  have box (d : Pair) (hd : d ∈ S) : 0 < d.1 ∧ d.1 ≤ 9 * 2 ^ 327 ∧ 0 < d.2 ∧ d.2 ≤ 7 * 2 ^ 327 := by
    obtain ⟨up, vlo, uc, vc, _⟩ := QuotientStripSlopePopulation.properties hd
    exact ⟨up, uc, by omega, vc⟩
  have bounds (d : Pair) (hd : d ∈ S) : 0 < label d ∧ label d < (N : ℤ) := by
    obtain ⟨_, _, _, row⟩ := picked d hd
    exact ⟨positive_label row, row.2.1⟩
  have all : S.image (discriminant N label) ⊆ tests N origin cutoff := by
    intro D hD
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hD
    obtain ⟨i, hi, own, row⟩ := picked d hd
    apply mem_tests.mpr
    refine ⟨i, hi, label d, ?_, ?_⟩
    · simpa only [own] using row
    · simp only [own, discriminant]
  exact (QuotientStripOddRootPairs.target hp hq hne odd S label many_directions.le box bounds).trans_le
    (card_le_card all)

/-- Complete balanced sweep, starting at the public lower endpoint. -/
theorem full_sweep {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (odd : Odd (p * q)) (low : 2 ^ 2047 ≤ p * q) (high : p * q < 2 ^ 2048) :
    2 ^ 635 < (tests (p * q) (first (p * q)) (p * q).sqrt).card :=
  distinct_tests hp hq hne odd (full_window low high)

/-- The counted full blocks end before p in the original ascending scan. -/
theorem before_factor {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (odd : Odd (p * q)) (low : 2 ^ 2047 ≤ p * q) (high : p * q < 2 ^ 2048) (ratio : 4 * q ≤ 5 * p) :
    2 ^ 635 < (tests (p * q) (first (p * q)) p).card :=
  distinct_tests hp hq hne odd (first_window low high ratio)

/-- The same strict before-p count from the restarted origin under its public
product threshold and partner cap. -/
theorem clipped_before_factor {p q D : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (odd : Odd (p * q)) (low : 2 ^ 2047 ≤ p * q) (high : p * q < 2 ^ 2048) (ratio : 4 * q ≤ 5 * p)
    (cut : 400 * (p * q) ≤ 289 * (2 ^ 1024 - 4) ^ 2) (partner : 2 ^ 1024 - 1 ≤ D) :
    2 ^ 635 < (tests (p * q) (clippedStart (p * q) D) p).card :=
  distinct_tests hp hq hne odd (clipped_window low high ratio cut partner)

end PrimeFactors.QuotientStripDistinctTests
