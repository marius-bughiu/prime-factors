import PrimeFactors.WeightedSubsetAnchor
import PrimeFactors.WeightedSubsetNonunit
import PrimeFactors.WeightedSubsetReduction

/-! Coverage of proper signed gcds from every subset of the sixteen
public labels, including a direct gcd of any individual label. -/

namespace PrimeFactors.WeightedSubsetLabels

open Finset WeightedSubsetAnchor WeightedSubsetReduction
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

/-- A proper gcd from a label itself, or from either sign of the exact
square relation on any nonempty subset of the public menu. -/
def Found (n : ℕ) : Prop :=
  (∃ i : Id, 1 < (label n i).gcd n ∧ (label n i).gcd n < n) ∨
  ∃ (S : Finset Id) (minus plus : ℕ), S.Nonempty ∧ Matches S (label n) (excess n) n minus plus ∧
    ((1 < minus ∧ minus < n) ∨ (1 < plus ∧ plus < n))

private theorem label_unit {n : ℕ} (ordinary : ¬ WeightedSubsetNonunit.Reached n) (i : Id) :
    (label n i).Coprime n := by
  apply Classical.byContradiction
  intro bad
  exact ordinary ⟨weight i, label n i, Nat.succ_pos _, i.1.isLt, in_window n i, bad⟩

private theorem positive {n : ℕ} (size : 1 < n) (i : Id) (unit : (label n i).Coprime n) :
    0 < excess n i := by
  apply Nat.pos_of_ne_zero
  intro zero
  have row := eq_row n i
  rw [zero, zero_add] at row
  have div : n ∣ (label n i)^2 := row ▸ dvd_mul_left _ _
  have one := (unit.pow_left 2).symm.eq_one_of_dvd div
  omega

private theorem nonempty_of_plus {n minus plus : ℕ} {T : Finset Id} (odd : Odd n)
    (hit : Matches T (label n) (excess n) n minus plus) (proper : 1 < plus) :
    T.Nonempty := by
  by_contra! empty
  rw [Finset.not_nonempty_iff_eq_empty.mp empty] at hit
  obtain ⟨z, eqn, _, hp⟩ := hit
  simp only [prod_empty] at eqn hp
  have one : z = 1 := (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp (by simpa using eqn.symm)
  rw [one] at hp
  change Nat.gcd 2 n = plus at hp
  have two := (Nat.coprime_two_left.mpr odd).gcd_eq_one
  omega

/-- The unit-label branch of every actual successful relation gives an
anchor counted by the support bound, even after cancellation changes the subset. -/
theorem found_candidate {n : ℕ} (size : 1 < n) (odd : Odd n)
    (top : Real.sqrt n ≤ 2*(2:ℝ)^1023) (ordinary : ¬ WeightedSubsetNonunit.Reached n)
    (found : Found n) : WeightedSubsetPopulation.Candidate modulus n := by
  rcases found with ⟨i, hp, _⟩ | ⟨S, minus, plus, _, matched, proper⟩
  · have := (label_unit ordinary i).gcd_eq_one
    omega
  obtain ⟨T, _, hit, distinct⟩ := reduced_subset S (label n) weight (excess n)
    (fun i _ => eq_row n i) (fun i _ => positive size i (label_unit ordinary i))
    (fun i _ => label_unit ordinary i) matched
  have ne : T.Nonempty := proper.elim (fun h => nonempty_of_minus hit h.2)
    (fun h => nonempty_of_plus odd hit h.1)
  obtain ⟨z, sq, _, _⟩ := hit
  exact hit_candidate top T ne (fun i _ => positive size i (label_unit ordinary i)) distinct ⟨z, sq⟩

attribute [local irreducible] MixedPrefixSample.ordered MixedPrefixSample.primes
  MixedPrefixSample.sample MixedPrefixSample.X MixedPrefixSample.eligible

private theorem sample_imp {E F : ℕ → Prop} {z : ℕ × ℕ} (hz : z ∈ MixedPrefixSample.sample E)
    (out : F (z.1*z.2)) : z ∈ MixedPrefixSample.sample F := by
  rw [MixedPrefixSample.sample, mem_filter] at hz ⊢
  obtain ⟨p,q,ne,large,_⟩ := (MixedPrefixSample.mem_ordered (E:=E) (z:=z)).mp hz.1
  exact ⟨(MixedPrefixSample.mem_ordered (E:=F) (z:=z)).mpr ⟨p,q,ne,large,out⟩, hz.2⟩

private def Clean (n : ℕ) : Prop := Found n ∧ ¬ WeightedSubsetNonunit.Reached n

private theorem clean_candidate (z : ℕ × ℕ) (hz : z ∈ MixedPrefixSample.sample Clean) :
    WeightedSubsetPopulation.Candidate modulus (z.1*z.2) := by
  obtain ⟨hp,hq,_,top,found,ordinary⟩ := WeightedMultiplierCoverage.sample_data (E:=Clean) (z:=z) hz
  rw [MixedPrefixSample.sample, mem_filter] at hz
  obtain ⟨pr,qr,_,_,_⟩ := (MixedPrefixSample.mem_ordered (E:=Clean) (z:=z)).mp hz.1
  rw [MixedPrefixSample.primes, mem_filter, mem_Ico] at pr qr
  have lo : 2 < MixedPrefixSample.X := by unfold MixedPrefixSample.X; decide +kernel
  have p2 : 2 < z.1 := lo.trans_le pr.1.1
  have q2 : 2 < z.2 := lo.trans_le qr.1.1
  have size : 1 < z.1*z.2 := by nlinarith only [p2,q2]
  exact found_candidate size ((hp.odd_of_ne_two p2.ne').mul (hq.odd_of_ne_two q2.ne'))
    top ordinary found

private theorem split_count : (MixedPrefixSample.sample Found).card ≤
    (MixedPrefixSample.sample Clean).card + (MixedPrefixSample.sample WeightedSubsetNonunit.Reached).card := by
  classical
  have cover : MixedPrefixSample.sample Found ⊆
      MixedPrefixSample.sample Clean ∪ MixedPrefixSample.sample WeightedSubsetNonunit.Reached := by
    intro z hz
    obtain ⟨_,_,_,_,found⟩ := WeightedMultiplierCoverage.sample_data (E:=Found) (z:=z) hz
    by_cases ex : WeightedSubsetNonunit.Reached (z.1*z.2)
    · exact mem_union_right _ (sample_imp hz ex)
    · exact mem_union_left _ (sample_imp (F:=Clean) hz ⟨found,ex⟩)
  exact (card_le_card cover).trans (card_union_le _ _)

private theorem combine {a b c p k d h big ceiling : ℕ}
    (split : c ≤ a+b) (count : a ≤ ceiling) (den : h < d*p) (exception : big*b < p)
    (room : d*((4*k)*ceiling) ≤ 3*h) (wide : 4*k ≤ big) : k*c < p := by
  have main : (4*k)*a < 3*p := by
    apply Nat.lt_of_mul_lt_mul_left (a:=d)
    calc
      _ ≤ 3*h := (Nat.mul_le_mul_left d (Nat.mul_le_mul_left _ count)).trans room
      _ < 3*(d*p) := Nat.mul_lt_mul_of_pos_left den (by decide)
      _ = _ := by ac_rfl
  have rare := (Nat.mul_le_mul_right b wide).trans_lt exception
  have total := Nat.mul_le_mul_left (4*k) split
  rw [Nat.mul_add] at total
  have bound := total.trans_lt (add_lt_add main rare)
  apply Nat.lt_of_mul_lt_mul_left (a:=4)
  rw [← Nat.mul_assoc]
  convert bound using 1; ring

/-- For distinct equal-width 1,024-bit primes conditioned on a 2,048-bit
product, fewer than one in 2^277 pairs can yield any proper gcd of these types. -/
theorem eligible_coverage : 2^277*(MixedPrefixSample.sample Found).card <
    MixedPrefixSample.eligible.card := by
  exact combine split_count (WeightedSubsetPopulation.eligible_count Clean modulus clean_candidate)
    ChebyshevPrimeSample.eligible_count WeightedSubsetNonunit.eligible_coverage
    (by decide +kernel) (by decide +kernel)

end PrimeFactors.WeightedSubsetLabels
