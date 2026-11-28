import PrimeFactors.ToySumIsolation

/-! Exact sum frequencies for the nine-bit prime population, conditional on
the product being 1 modulo 25. Compare with uniform ordered residue pairs
having that product, and with uniform draws from the allowed sum residues. -/

namespace PrimeFactors.PrimePairSumFrequency

set_option maxRecDepth 8192

/-- Each unordered pair occurs once, represented in increasing order. -/
noncomputable def sample : List (ℕ × ℕ) :=
  (ToySumIsolation.pairs 256).filter fun (p,q) => p*q % 25 = 1

theorem sample_nodup : sample.Nodup := (ToySumIsolation.nodup_pairs 256).filter _

theorem mem_sample {p q : ℕ} : (p,q) ∈ sample ↔
    256 ≤ p ∧ p < q ∧ q < 512 ∧ p.Prime ∧ q.Prime ∧ p*q % 25 = 1 := by
  simp only [sample,List.mem_filter,ToySumIsolation.mem_pairs,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨lower,_,pp,order,upper,qp⟩,prod⟩
    exact ⟨lower,order,upper,pp,qp,prod⟩
  · rintro ⟨lower,order,upper,pp,qp,prod⟩
    exact ⟨⟨lower,order.trans upper,pp,order,upper,qp⟩,prod⟩

noncomputable def observedSums : List ℕ := sample.map fun (p,q) => (p+q)%25

/-- Uniform ordered residue pairs with product 1. Every possible first entry
is a unit, and its inverse is the unique possible second entry. -/
noncomputable def modelSums : List ℕ := (List.range 25).flatMap fun a =>
  ((List.range 25).filter fun b => a*b%25 = 1).map fun b => (a+b)%25

def allowed : List ℕ := [0,2,5,10,15,20,23]

/-- These seven residues form the entire local sum menu. -/
theorem admissible_iff (s : ZMod 25) : AdmissibleSum 1 s ↔ s.val ∈ allowed := by
  revert s
  unfold AdmissibleSum allowed
  decide +kernel

/-- On this local menu, 2 and 23 are exactly the residues where the
discriminant vanishes modulo 5. -/
theorem singular_iff : ∀ s ∈ allowed, s^2%5 = 4 ↔ s=2 ∨ s=23 := by decide +kernel

private theorem observed_trace : observedSums =
    [0,0,15,23,23,2,2,2,15,15,2,5,5,0,0,0,2,20,20,2,10,5,5,23,23,20,20,
      23,23,20,10,23,5,23,23,5,23,23,2,23,0,23,2,20] := by
  rw [observedSums,sample,ToySumIsolation.pairs,ToySumIsolation.catalog_nine]
  decide +kernel

private theorem model_trace : modelSums =
    [2,15,20,23,2,0,5,23,2,10,15,23,2,20,0,23,2,5,10,23] := by decide +kernel

theorem sample_size : sample.length = 44 := by
  simpa only [observedSums,List.length_map] using congrArg List.length observed_trace

/-- Frequencies in ascending order of the seven admissible sum residues. -/
theorem frequencies :
    allowed.map (fun s => observedSums.count s) = [6,8,6,2,3,6,13] ∧
    allowed.map (fun s => modelSums.count s) = [2,5,2,2,2,2,5] := by
  rw [observed_trace,model_trace]
  decide +kernel

noncomputable def singularCount (sums : List ℕ) : ℕ :=
  (sums.filter fun s => s^2%5 = 4).length

/-- The probability of landing in either singular class is 21/44 for the
prime pairs, 10/20 for the residue-pair model, and 2/7 for uniform sums. -/
theorem singular_mass :
    (singularCount observedSums, observedSums.length) = (21,44) ∧
    (singularCount modelSums, modelSums.length) = (10,20) ∧
    (singularCount allowed, allowed.length) = (2,7) := by
  rw [observed_trace,model_trace]
  decide +kernel

/-- Count exact matches when the guess and the actual prime pair are drawn
independently and uniformly from their respective lists. -/
noncomputable def matchCount (guesses answers : List ℕ) : ℕ :=
  (guesses.map fun g => answers.count g).sum

theorem exact_guess_scores :
    (matchCount modelSums observedSums, modelSums.length * observedSums.length) = (151,880) ∧
    (matchCount allowed observedSums, allowed.length * observedSums.length) = (44,308) := by
  rw [observed_trace,model_trace]
  decide +kernel

/-- Keep only eighteen-bit products of nine-bit primes. Restricting both
primes to the upper half of their interval drops sixteen eligible products. -/
theorem full_width_control :
    let full := sample.filter fun (p,q) => 2^17≤p*q
    let upper := full.filter fun (p,_) => 384<p
    let selected := fun v : ℕ×ℕ => (v.1+v.2)%25==2 || (v.1+v.2)%25==23
    (full.length,(full.filter selected).length,upper.length,(upper.filter selected).length)=(27,15,11,8) ∧
      (311,491)∈full ∧ (311,491)∉upper ∧ selected (311,491)=true := by
  rw [sample,ToySumIsolation.pairs,ToySumIsolation.catalog_nine]
  decide +kernel

end PrimeFactors.PrimePairSumFrequency
