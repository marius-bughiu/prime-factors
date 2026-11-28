import PrimeFactors.AllSmallQuarticDenominatorCoverage
import PrimeFactors.QuarticLocalSearchWork

/-! Products passing the primitive local quartic condition for every finite
modulus while giving no reading in either strip throughout the specified
denominator range. -/
namespace PrimeFactors.QuarticLocalFalsePositives

open Finset
open MixedPrefixSample (eligible)
open ScaledQuarticMenuBound (covered family)
open QuarticLocalSearchWork (locallyPossible)
open QuarticLocalClassification (Tests)
open ComplementaryQuarticProducts (choices)
open scoped Classical
set_option maxRecDepth 4096
set_option exponentiation.threshold 4096
attribute [local irreducible] eligible

private theorem mem_scaled {d : ℕ} {v : ℕ×ℕ} : v∈family d ↔
    v∈eligible ∧ (choices (d^4*(v.1*v.2))).Nonempty := mem_filter

private theorem mem_possible {v : ℕ×ℕ} : v∈locallyPossible ↔
    v∈eligible ∧ Tests (v.1*v.2) := mem_filter

attribute [local irreducible] locallyPossible family

/-- An actual reading at any positive denominator passes every local test. -/
theorem covered_subset {D : Finset ℕ} (positive : ∀ d∈D,0<d) : covered D⊆locallyPossible := by
  intro v h
  obtain ⟨d,hd,hit⟩ := mem_biUnion.mp h
  obtain ⟨e,raw⟩ := mem_scaled.mp hit
  exact mem_possible.mpr ⟨e,QuarticPublicResidueGate.of_reading e (positive d hd) raw⟩

theorem recognized_subset : covered (Icc 1 (2^512))⊆locallyPossible :=
  covered_subset fun _ h => (mem_Icc.mp h).1

noncomputable def remaining (k : ℕ) := locallyPossible \ covered (Icc 1 k)
noncomputable abbrev misses := remaining (2^512)

/-- For each denominator in range, the set of factor pairs from the two
fourth-root readings is empty, even though every positive modulus has a point. -/
theorem mem_misses {v : ℕ×ℕ} : v∈misses ↔ v∈eligible ∧ Tests (v.1*v.2) ∧
    ∀ d : ℕ, 0<d → d≤2^512 → ¬(choices (d^4*(v.1*v.2))).Nonempty := by
  constructor
  · intro h
    obtain ⟨possible,no⟩ := mem_sdiff.mp h
    obtain ⟨e,localTest⟩ := mem_possible.mp possible
    exact ⟨e,localTest,fun d dp hi raw =>
      no (mem_biUnion.mpr ⟨d,mem_Icc.mpr ⟨dp,hi⟩,mem_scaled.mpr ⟨e,raw⟩⟩)⟩
  · rintro ⟨e,localTest,empty⟩
    refine mem_sdiff.mpr ⟨mem_possible.mpr ⟨e,localTest⟩,?_⟩
    intro hit
    obtain ⟨d,hd,inFamily⟩ := mem_biUnion.mp hit
    exact empty d (mem_Icc.mp hd).1 (mem_Icc.mp hd).2 (mem_scaled.mp inFamily).2

private theorem partition_at (k : ℕ) :
    (remaining k).card+(covered (Icc 1 k)).card=locallyPossible.card :=
  card_sdiff_add_card_eq_card (s:=covered (Icc 1 k)) (t:=locallyPossible)
    (covered_subset fun _ h => (mem_Icc.mp h).1)

attribute [local irreducible] remaining covered

theorem card_partition : (remaining (2^512)).card+(covered (Icc 1 (2^512))).card=locallyPossible.card :=
  partition_at (2^512)

private theorem remove_small {M C L T : ℝ} (split : M+C=L) (pos : 0<T) (nn : 0≤C)
    (rare : 2^227*C<T) (close : |L/T-1/8|≤1/2^146) : |M/T-1/8|<1/2^145 := by
  have parts : M/T+C/T=L/T := by rw [←add_div,split]
  have tiny : C/T<1/2^227 :=
    (div_lt_div_iff₀ pos (by positivity : (0:ℝ)<2^227)).mpr (by simpa only [one_mul,mul_one,mul_comm] using rare)
  have nonneg := div_nonneg nn pos.le
  have near := abs_le.mp close
  have room : (1:ℝ)/2^146+1/2^227<1/2^145 := by norm_num
  apply abs_lt.mpr
  constructor <;> linarith

private theorem close_at (k : ℕ) (rare : 2^227*(covered (Icc 1 k)).card<eligible.card)
    {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints 16 li) :
    |((remaining k).card:ℝ)/eligible.card-1/8|<1/(2:ℝ)^145 := by
  have pos : 0<eligible.card := by omega
  apply remove_small (C:=((covered (Icc 1 k)).card:ℝ)) (L:=(locallyPossible.card:ℝ))
  · exact_mod_cast partition_at k
  · exact_mod_cast pos
  · exact Nat.cast_nonneg _
  · exact_mod_cast rare
  · rw [QuarticLocalSearchWork.possible_eq]
    exact QuarticLocalPopulation.close_ehp h

/-- Under the stated prime-count endpoint estimates at modulus 16, the share
of all eligible products that pass every modulus yet have no bounded
fourth-root reading differs from one eighth by strictly less than 2⁻¹⁴⁵. -/
theorem close_ehp {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints 16 li) :
    |((remaining (2^512)).card:ℝ)/eligible.card-1/8|<1/(2:ℝ)^145 :=
  close_at (2^512) AllSmallQuarticDenominatorCoverage.rare h

end PrimeFactors.QuarticLocalFalsePositives
