import PrimeFactors.FloorSquareShiftPopulation
import PrimeFactors.GaussianGateAggregateCost

/-! Aggregate cost of the screened Fermat scan on pairs admitting any
positive floor-square shift. Each eligible pair is counted once. -/
namespace PrimeFactors.FloorShiftAggregateCost

open Finset MixedPrefixSample FloorSquareShiftPopulation GaussianGateAggregateCost

/-- Even if all tests on every pair admitting a shift were saved, the
reduction in total exact square tests would be less than 2^-434. -/
theorem aggregate :
    2^434*(∑ v∈successes,(tests v).card) < ∑ v∈eligible,(tests v).card := by
  classical
  apply family_bound successes 434
  · exact filter_subset _ _
  · rw [show 434+48=482 by decide]
    exact full_width

end PrimeFactors.FloorShiftAggregateCost
