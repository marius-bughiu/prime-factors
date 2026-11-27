import PrimeFactors.OptionalFilterCost
import PrimeFactors.PublicSumSieveOrdering

/-! The small public control with an exact square test after a prefix of
the density-ordered filters. All prices use a scalar lookup as one unit. -/
namespace PrimeFactors.PublicSumFinalTestCost

open PublicSumSieveOrdering
open private PrimeFactors.PublicSumSieveOrdering.work_from from PrimeFactors.PublicSumSieveOrdering

noncomputable def total (price k : ℕ) : ℕ :=
  let tests := densityOrder.take k
  FiniteFilterWork.work (positions []) (tests.map lookup) + price*(positions tests).length

private def costs (sizes : List ℕ) (price k : ℕ) :=
  ((sizes.take k).sum) + price*sizes[k]?.getD 0

attribute [local irreducible] positions

private theorem read_sizes (k : Fin 14) (price : ℕ) :
    total price k = costs (stageSizes densityOrder) price k := by
  have bound : (k:ℕ) ≤ densityOrder.length := by
    have size : densityOrder.length = 13 := by decide +kernel
    omega
  have sub : densityOrder.take k ⊆ ascendingOrder := fun _ h =>
    same_rows.subset (List.mem_of_mem_take h)
  rw [total,PrimeFactors.PublicSumSieveOrdering.work_from _ [] sub (by simp)]
  have lt : (k:ℕ) < densityOrder.length+1 := by omega
  simp only [List.nil_append, costs, stageSizes, ←List.map_take, List.getElem?_map,
    List.getElem?_range lt, List.take_range, List.length_take, Nat.min_eq_left bound,
    Option.map_some, Option.getD_some, Nat.min_eq_left lt.le]
  apply congrArg (· + price*(positions (densityOrder.take k)).length)
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [List.take_take, Nat.min_eq_left (List.mem_range.mp hi).le]

/-- The first ten density-ordered primes cost 12,726 lookups and leave two
sums for an exact square test. Twelve primes cost 12,730 lookups and leave one. -/
theorem selected_costs (price : ℕ) :
    total price 0 = price*7273 ∧ total price 10 = 12726+price*2 ∧
      total price 12 = 12730+price ∧ total price 13 = 12731+price := by
  have eval (k : Fin 14) := (read_sizes k price).trans (congrArg (fun l => costs l price k) density_sizes)
  have twelve : total price 12 = 12730+price*1 := eval 12
  have last : total price 13 = 12731+price*1 := eval 13
  exact ⟨by simpa using (show total price 0 = 0+price*7273 from eval 0),
    eval 10, by simpa using twelve, by simpa using last⟩

private theorem best_numeric (price : ℕ) (k : Fin 14) :
    let sizes := [7273,2909,1323,638,310,143,75,37,13,5,2,2,1,1]
    costs sizes price (if price ≤ 1 then 0 else if price ≤ 4 then 10 else 12) ≤ costs sizes price k := by
  dsimp only
  split_ifs <;> fin_cases k <;>
    norm_num [costs, List.take, List.sum, Fin.val_natCast, Option.getD] <;> omega

/-- Among the fourteen prefixes, for every integer price choose zero tests
at prices 0–1, ten at 2–4, and twelve at 5 or above. At price 4 there is a tie. -/
theorem best_prefix (price : ℕ) (k : Fin 14) :
    total price (if price ≤ 1 then 0 else if price ≤ 4 then 10 else 12) ≤ total price k := by
  let winner : Fin 14 := ⟨if price ≤ 1 then 0 else if price ≤ 4 then 10 else 12,
    by split_ifs <;> decide⟩
  change total price winner ≤ _
  rw [read_sizes,read_sizes,density_sizes]
  exact best_numeric price k

end PrimeFactors.PublicSumFinalTestCost
