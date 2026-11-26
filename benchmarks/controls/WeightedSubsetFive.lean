import PrimeFactors.WeightedSubsetWitness

/-! Reproduce with python3 -m experiments.weighted_subset_witness --check. -/
namespace PrimeFactors.WeightedSubsetFive
open WeightedSubsetWitness

def product : ℕ := 8928473

private noncomputable def ceiling : Fin 8 → ℕ := ![
  5977,
  8452,
  10351,
  11953,
  13363,
  14639,
  15812,
  16903]

private noncomputable def probes : Fin 8 → Fin 2 → List ℕ := ![
  ![[], [19, 41, 59, 79, 97, 101]],
  ![[23, 41, 59, 67, 73, 79, 83, 89, 97, 101], [37, 41, 61, 67, 73, 79, 83, 89, 97, 101]],
  ![[19, 23, 37, 67, 79, 83, 97, 101], [61, 73, 83, 97, 101]],
  ![[59, 61, 67, 83, 97], [41, 61, 79, 97, 137]],
  ![[37, 41, 59, 67, 101], [19, 41, 59, 67, 73, 89, 137]],
  ![[79, 89, 107, 137], [41, 59, 73, 83, 89, 97, 137]],
  ![[19, 23, 59, 61, 73, 79, 83, 89, 97, 101, 107], [19, 37, 41, 89, 97, 101, 107, 137]],
  ![[19, 23, 37, 41, 59, 61, 79, 89, 101, 107], [19, 41, 59, 61, 83, 97]]]

/-- Coordinates are zero-based for both the weight index and the rank. -/
def uniqueRows : Finset Id := {(0,0), (0,1), (1,1), (5,0), (7,0)}

/-- Exactly one nonempty subset of the sixteen public remainders has square product. -/
theorem onlySquareSubset (S : Finset Id) (nonempty : S.Nonempty) :
    (∃ y : ℕ, (∏ i∈S, excess product i)=y^2) ↔ S=uniqueRows :=
  certify_unique product ceiling probes (0,0) uniqueRows 64336673856 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) S nonempty

#print axioms onlySquareSubset
end PrimeFactors.WeightedSubsetFive
