import PrimeFactors.FiveSquarePolicy
import PrimeFactors.FiveSquareSignPopulation

/-! Optimal sum-remainder guessing across every distinct pair of 1,024-bit
primes with full-width product. Each product residue may select a different
guess order. The actual-prime transfer assumes explicit Dirichlet-GRH
prime-count estimates in residue classes. -/
namespace PrimeFactors.FiveSquarePooledRanks

open Finset FiveSquarePolicy FiveSquareAllPrimeRanks FiveSquareSignRanks
open FiveSquarePrimeSupply (Endpoints)
open scoped Classical

set_option exponentiation.threshold 4096

private theorem pattern_average (f : Pattern → ℚ) :
    (∑ u : U,f (sign u.val.val))/3920716800=(∑ b : Pattern,f b)/32 := by
  simpa only [FiveSquarePolicy.unit_count.1,Nat.cast_ofNat] using FiveSquareSignPopulation.mean_by_pattern f

/-- No product-dependent policy beats the pooled modular optimum. -/
theorem uniform_optimum : IsLeast (Set.range (fun P : Policy => uniform (cost P)))
    (159599216429/6144:ℝ) := by
  have value := (pattern_average mean).trans pooled.1
  constructor
  · obtain ⟨P,good⟩ := optimal_family
    refine ⟨P,?_⟩
    dsimp only
    rw [uniform_eq P]
    simp_rw [good]
    simpa only [Rat.cast_div,Rat.cast_ofNat] using congrArg (fun q : ℚ => (q:ℝ)) value
  · rintro _ ⟨P,rfl⟩
    dsimp only
    rw [uniform_eq P]
    have lo := sum_le_sum (s:=univ) (fun u _ => local_lower P u)
    have h := div_le_div_of_nonneg_right lo (by norm_num : (0:ℚ)≤3920716800)
    rw [value] at h
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr h

/-- The exact comparison when the list for each product remainder is
ordered uniformly at random, independent of the hidden factor residues. -/
theorem uniform_baseline : uniform twiceRandom/2=(2367408217/64:ℝ) := by
  have v := (pattern_average baseline).trans pooled.2.1
  have twice : (2*(∑ u : U,baseline (sign u.val.val)))/3920716800=2*(2367408217/64:ℚ) := by
    linarith only [v]
  rw [uniform_twiceRandom,twice]
  norm_num

/-- Mean costs on the actual full-width prime-pair population. The lower
bound applies to every product-dependent set of lists. The witness attains
the modular optimum and its actual cost is within a thousandth of it. -/
theorem actual_interval {li : ℕ→ℝ} (h : Endpoints li) :
    (∀ P : Policy, (159599216429/6144:ℝ)-1/1000 < actual (cost P)) ∧
    (∃ P : Policy, uniform (cost P)=159599216429/6144 ∧
      |actual (cost P)-159599216429/6144|<1/1000) ∧
    |actual twiceRandom/2-2367408217/64|<1/2000 := by
  constructor
  · intro P
    have lo := uniform_optimum.2 ⟨P,rfl⟩
    have near := (abs_lt.mp (every_cost h (cost P) (cost_sym P) (cost_bound P))).1
    linarith only [lo,near]
  constructor
  · obtain ⟨P,good⟩ := uniform_optimum.1
    exact ⟨P,good,good ▸ every_cost h (cost P) (cost_sym P) (cost_bound P)⟩
  · have near := abs_lt.mp (every_cost h twiceRandom random_sym random_bound)
    have base := uniform_baseline
    exact abs_lt.mpr ⟨by linarith only [near.1,base], by linarith only [near.2,base]⟩

/-- The saving of an appropriate family of lists exceeds 29.7758% over the
whole eligible population. This counts inclusive guesses of sum residues. -/
theorem actual_saving {li : ℕ→ℝ} (h : Endpoints li) :
    ∃ P : Policy, actual (cost P)<(702242:ℝ)/1000000*(actual twiceRandom/2) := by
  obtain ⟨_,⟨P,_,near⟩,random⟩ := actual_interval h
  exact ⟨P,by linarith only [(abs_lt.mp near).2,(abs_lt.mp random).1]⟩

end PrimeFactors.FiveSquarePooledRanks
