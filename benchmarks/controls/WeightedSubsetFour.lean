import PrimeFactors.WeightedSubsetWitness

/-! Reproduce with python3 -m experiments.weighted_subset_witness --check. -/
namespace PrimeFactors.WeightedSubsetFour
open WeightedSubsetWitness

def product : ℕ := 2222417

private noncomputable def ceiling : Fin 8 → ℕ := ![
  2982,
  4217,
  5165,
  5964,
  6667,
  7304,
  7889,
  8434]

private noncomputable def probes : Fin 8 → Fin 2 → List ℕ := ![
  ![[], [29, 47, 59, 61, 71, 73, 97, 101, 107, 113]],
  ![[43, 47, 53, 61, 71, 89, 97, 107, 109, 113], [29, 71, 73, 113]],
  ![[53, 73, 89, 97, 101, 109], [29, 43, 53, 67, 71, 73, 89, 101, 109]],
  ![[67, 71, 89, 97, 101, 107], [29, 47, 73, 97, 109, 113]],
  ![[47, 59, 61, 89, 107], [43, 53, 59, 67, 89, 97, 101, 107, 109, 113]],
  ![[53, 59, 61, 71, 89, 101, 113], [29, 47, 59, 89, 97, 101, 107, 113]],
  ![[43, 47, 53, 59, 61, 67, 101, 109], [29, 43, 53, 73, 109]],
  ![[43, 59, 61, 67, 71, 73, 97, 109], [43, 89, 97, 101, 107, 109, 113]]]

/-- Coordinates are zero-based for both the weight index and the rank. -/
def uniqueRows : Finset Id := {(0,0), (0,1), (4,0), (7,1)}

/-- Exactly one nonempty subset of the sixteen public remainders has square product. -/
theorem onlySquareSubset (S : Finset Id) (nonempty : S.Nonempty) :
    (∃ y : ℕ, (∏ i∈S, excess product i)=y^2) ↔ S=uniqueRows :=
  certify_unique product ceiling probes (0,0) uniqueRows 725088000 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) S nonempty

#print axioms onlySquareSubset
end PrimeFactors.WeightedSubsetFour
