import PrimeFactors.ReduceQuarticDenominator
import PrimeFactors.ScaledQuarticReadings
import PrimeFactors.FullWidthQuarticFixture

/-! Equality of the executable searches on the full balanced population. -/
namespace PrimeFactors.ThreeQuarticDenominators

open ComplementaryQuarticProducts (choices)
open MixedPrefixSample (eligible)
open ScaledQuarticReadings (run)
open ScaledQuarticMenuBound (covered)
open scoped Classical
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible

/-- The input alone supplies all six branch checks. -/
def recover (n : ℕ) := run n [1,725,1517]

private theorem range_mem {d k : ℕ} : d∈List.range' 1 k ↔ d∈Finset.Icc 1 k := by
  rw [List.mem_range'_1,Finset.mem_Icc]
  omega

/-- Both the returned prime pair and failure agree. The reference algorithm
tries every integer denominator in ascending order. -/
theorem identical {p q : ℕ} (mem : (p,q)∈eligible) :
    run (p*q) (List.range' 1 2048)=recover (p*q) := by
  have all := ScaledQuarticReadings.run_eq mem (List.range' 1 2048)
    (fun _ hd => (Finset.mem_Icc.mp (range_mem.mp hd)).2)
  have few := ScaledQuarticReadings.run_eq mem [1,725,1517] (by simp)
  have event : (∃ d∈List.range' 1 2048,(choices (d^4*(p*q))).Nonempty) ↔
      ∃ d∈([1,725,1517]:List ℕ),(choices (d^4*(p*q))).Nonempty := by
    simp only [range_mem]
    rw [ReduceQuarticDenominator.menu_hit_iff mem]
    simp
  unfold recover
  rw [all,few]
  exact if_congr event rfl rfl

theorem rarity : 2^1102*(covered (Finset.Icc 1 2048)).card<eligible.card := by
  rw [ReduceQuarticDenominator.menu_covered]
  exact ScaledQuarticMenuBound.three

/-- On unrestricted small inputs the public three checks give these two
selected successful controls from the products alone. -/
theorem controls :
    recover ScaledQuarticControls.N58=some (362037209,536767369) ∧
    recover ScaledQuarticControls.N37=some (229777,420853) :=
  ⟨ScaledQuarticReadings.example58,ScaledQuarticReadings.example37⟩

private theorem at_one {p q n : ℕ} (prod : p*q=n) (mem : (p,q)∈eligible)
    (hit : ComplementaryQuarticProducts.recognizeY n=some (p,q)) : recover n=some (p,q) := by
  subst n
  have witness : (p,q)∈choices (p*q) := Finset.mem_union_right _ (Option.mem_toFinset.mpr hit)
  have event : ∃ d∈([1,725,1517]:List ℕ),(choices (d^4*(p*q))).Nonempty :=
    ⟨1,by simp,(p,q),by simpa only [one_pow,one_mul] using witness⟩
  unfold recover
  rw [ScaledQuarticReadings.run_eq mem [1,725,1517] (by simp),if_pos event]

open FullWidthQuarticFixture
attribute [local irreducible] recover

/-- A certified full-width success for the same executable. The constructed
product is accepted on the ordinary denominator-one branch. -/
theorem full_width : recover N=some (p,q) := by
  have prod : p*q=N := by simpa using data.1.1
  apply at_one prod _ quartic.2
  exact SumGridPopulation.eligible_data.mpr
    ⟨data.2.1,data.2.2.1,data.2.2.2.1,p_prime,q_prime,prod.symm ▸ data.2.2.2.2.1⟩

end PrimeFactors.ThreeQuarticDenominators
