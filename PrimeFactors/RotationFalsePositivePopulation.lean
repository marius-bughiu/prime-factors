import PrimeFactors.RotationPrimeSignature
import PrimeFactors.FiniteBinCollisionPopulation

/-! Lower bounds for false positives of the modular rotation test, drawn
from actual unordered prime pairs with a full-width product. -/
namespace PrimeFactors.RotationFalsePositivePopulation

open Finset MixedPrefixSample BinaryRotationProduct RotationPrimeSignature FiniteBinCollisionPopulation
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

noncomputable def passes := eligible.filter fun z =>
  (roots 1024 (z.1*z.2) 0).Nonempty ∨ (roots 1024 (z.1*z.2) 1).Nonempty

noncomputable def evenPasses := eligible.filter fun z => (roots 1024 (z.1*z.2) 0).Nonempty

noncomputable def falsePositives := passes \ BinaryRotationPopulation.family

attribute [local irreducible] eligible passes evenPasses

/-- Counting matches on sixteen local square signs forces this many actual
prime products to pass the even-phase square test. -/
theorem same_sign_lower : eligible.card < 786432*evenPasses.card := by
  have count := band_fraction_bins bins signature card_bins.le
    (fun p _ => signature_mem p) evenPasses (by
      intro p hp q hq pq same
      rw [evenPasses]
      exact mem_filter.mpr ⟨band_pair_eligible hp hq pq, square_of_same same⟩)
  rw [card_bins, show (12:ℕ)*65536=786432 by decide] at count
  exact count

/-- After normalizing the sign at three, fifteen sign bits suffice for
the union of both tests. -/
theorem passing_lower : eligible.card < 393216*passes.card := by
  have count := band_fraction_bins shortBins shortSignature
    (card_shortBins.le.trans (by decide)) (fun p _ => shortSignature_mem p) passes (by
      intro p hp q hq pq same
      rw [passes]
      exact mem_filter.mpr ⟨band_pair_eligible hp hq pq, same_phase same⟩)
  rw [card_shortBins, show (12:ℕ)*32768=393216 by decide] at count
  exact count

theorem true_subset : BinaryRotationPopulation.family ⊆ passes := by
  intro z hz
  obtain ⟨eligible_z,j,_,turn⟩ := BinaryRotationPopulation.mem_family.mp hz
  have sq := target (by decide : 0<1024) turn
  let x := 2^(half j)*z.1
  have member : (roots 1024 (z.1*z.2) (j%2)).Nonempty :=
    ⟨x%(modulus 1024),mem_roots.mpr ⟨Nat.mod_lt _ (by decide +kernel),
      ((Nat.mod_modEq ..).pow 2).trans sq⟩⟩
  rw [passes]
  apply mem_filter.mpr
  refine ⟨eligible_z,?_⟩
  rcases Nat.mod_two_eq_zero_or_one j with e|e
  · exact Or.inl (e ▸ member)
  · exact Or.inr (e ▸ member)

theorem partition : falsePositives.card + BinaryRotationPopulation.family.card = passes.card := by
  rw [falsePositives]
  exact card_sdiff_add_card_eq_card true_subset

private theorem compare_counts {u k f t : ℕ} (mass : u<393216*k)
    (rare : 2^998*t<u) (split : f+t=k) : u<393217*f ∧ 2^979*t<k := by
  norm_num1 at rare ⊢
  omega

/-- More than one in 393,217 eligible products is a false positive. Among
those that pass, fewer than one in 2^979 has prime factors related by rotation. -/
theorem false_positives : eligible.card < 393217*falsePositives.card ∧
    2^979*BinaryRotationPopulation.family.card < passes.card :=
  compare_counts passing_lower BinaryRotationPopulation.fraction partition

end PrimeFactors.RotationFalsePositivePopulation
