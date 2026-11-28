import PrimeFactors.BinaryRotationProduct

/-! An exhaustive control for the two square classes of a six-bit rotation.
The counted population contains each unordered pair of distinct six-bit primes
once and requires the product to have twelve bits. -/

namespace PrimeFactors.SmallRotationCensus

open Finset BinaryRotationProduct

noncomputable def primes : Finset ℕ := (Ico (2^5) (2^6)).filter Nat.Prime

noncomputable def eligible : Finset (ℕ×ℕ) := (primes ×ˢ primes).filter fun z =>
  z.1<z.2 ∧ 2^11≤z.1*z.2 ∧ z.1*z.2<2^12

noncomputable def rootClass (r : ℕ) := eligible.filter fun z =>
  (roots 6 (z.1*z.2) r).Nonempty

noncomputable def passes := rootClass 0 ∪ rootClass 1

noncomputable def rotations := eligible.filter fun z =>
  ∃ j∈range 6, z.2=rotate 6 j z.1

theorem eligible_iff {p q : ℕ} : (p,q)∈eligible ↔
    ((2^5≤p ∧ p<2^6) ∧ p.Prime) ∧ ((2^5≤q ∧ q<2^6) ∧ q.Prime) ∧
      p<q ∧ 2^11≤p*q ∧ p*q<2^12 := by
  simp only [eligible,primes,mem_filter,mem_product,mem_Ico,and_assoc]

theorem passes_iff {p q : ℕ} : (p,q)∈passes ↔
    (p,q)∈eligible ∧ ((roots 6 (p*q) 0).Nonempty ∨ (roots 6 (p*q) 1).Nonempty) := by
  simp only [passes,rootClass,mem_union,mem_filter,and_or_left]

theorem rotations_iff {p q : ℕ} : (p,q)∈rotations ↔
    (p,q)∈eligible ∧ ∃ j<6, q=rotate 6 j p := by
  simp only [rotations,mem_filter,mem_range]

theorem prime_list : primes={37,41,43,47,53,59,61} := by decide +kernel

private theorem eligible_list : eligible={
    (37,59),(37,61),(41,53),(41,59),(41,61),(43,53),(43,59),(43,61),
    (47,53),(47,59),(47,61),(53,59),(53,61),(59,61)} := by
  rw [eligible,prime_list]
  decide +kernel

/-- The even and odd root classes contain respectively two and four pairs. -/
theorem root_lists : rootClass 0={(41,59),(47,59)} ∧
    rootClass 1={(41,61),(43,53),(47,61),(59,61)} := by
  simp only [rootClass,eligible_list]
  decide +kernel

theorem actual_list : rotations={(43,53),(47,59),(47,61),(59,61)} := by
  rw [rotations,eligible_list]
  decide +kernel

/-- Each of the two root classes admits one product whose primes are not rotations. -/
theorem false_positives : passes \ rotations={(41,59),(41,61)} := by
  rw [passes,root_lists.1,root_lists.2,actual_list]
  decide +kernel

theorem counts : eligible.card=14 ∧ passes.card=6 ∧ rotations.card=4 ∧
    (passes \ rotations).card=2 := by
  rw [false_positives,eligible_list,passes,root_lists.1,root_lists.2,actual_list]
  decide +kernel

/-- Multiplying the pairs does not merge any inputs in this population. -/
theorem products_distinct : (eligible.image fun z => z.1*z.2).card=eligible.card := by
  rw [eligible_list]
  decide +kernel

theorem false_products : ((passes \ rotations).image fun z => z.1*z.2)={2419,2501} := by
  rw [false_positives]
  decide +kernel

end PrimeFactors.SmallRotationCensus
