import PrimeFactors.ExtendedModulusPrimeSupply
import PrimeFactors.FiveSquareGuessRanks

/-! Counts of distinct, full-width actual prime pairs in individual residue
cells for the five-prime example. The analytic estimates are explicit inputs
from Ernvall-Hytönen and Palojärvi, Corollary 2, assuming Dirichlet GRH. -/

namespace PrimeFactors.FiveSquarePrimeSupply

open Finset WideResiduePrimeSupply PrimeResidueRankTransfer
open FullRangeResidueEstimates (X)
open PrimeProductRegion (K)
open PrimeSquareSumWeights (Pairs)
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

noncomputable abbrev m : ℕ := CoprimeGuessTables.modulus FiveSquareGuessRanks.primes
abbrev D := 52800*2^512
abbrev M := 2^975
abbrev F := 2^380

/-- Common logarithmic integral and published estimates at every integer
endpoint used by the product threshold. -/
structure Endpoints (li : ℕ→ℝ) : Prop where
  quarter : li B=li L+increment L (B-L)
  pointwise (a : ZMod m) (unit : IsUnit a) (z : ℕ) (lo : X≤z) (hi : z≤B) :
    |((through m a.val z).card:ℝ)-li z/m.totient|≤ehpError m z

private theorem modulus_bounds : 3≤m ∧ m≤2^33 := by
  rw [show m=7239457225 from FiveSquareGuessRanks.modulus_value]
  decide

/-- All real x and integer moduli in the estimates are in the paper's range. -/
theorem source_domain {z : ℕ} (lo : X≤z) : 3≤m ∧ m≤z :=
  ⟨modulus_bounds.1,modulus_bounds.2.trans ((by decide +kernel : 2^33≤X).trans lo)⟩

private theorem extended {li : ℕ→ℝ} (h : Endpoints li) : ExtendedModulusPrimeSupply.Endpoints m li :=
  ⟨h.quarter,h.pointwise⟩

private theorem room : (M:ℝ)+26400*(2:ℝ)^512≤((B-L:ℕ):ℝ)/(710*((2^33:ℕ):ℝ)) := by
  norm_num [M,B,L]

theorem spread {li : ℕ→ℝ} (h : Endpoints li) {v w : ZMod m × ZMod m}
    (ua : IsUnit v.1) (ub : IsUnit v.2) (uc : IsUnit w.1) (ue : IsUnit w.2) :
    cell X B K v≤cell X B K w+(2*D*B+B) :=
  ExtendedModulusPrimeSupply.spread modulus_bounds.1 (source_domain (z:=X) le_rfl).2 (extended h) ua ub uc ue

theorem lower {li : ℕ→ℝ} (h : Endpoints li) {v : ZMod m × ZMod m}
    (ua : IsUnit v.1) (ub : IsUnit v.2) : M*(M-1)≤cell X B K v :=
  ExtendedModulusPrimeSupply.lower_of_cap modulus_bounds.1 modulus_bounds.2 (by decide +kernel) room (extended h) ua ub

attribute [local irreducible] cell tail

/-- Every product-one residue cell occurs, and the largest has at most
1+2⁻³⁸⁰ times the population of the smallest. -/
theorem cell_bounds {li : ℕ→ℝ} (h : Endpoints li) : ∃ l u : ℕ, 0<l ∧ F*u≤(F+1)*l ∧
    ∀ v : Pairs 1 m, l≤cell X B K v.val ∧ cell X B K v.val≤u := by
  obtain ⟨l,u,pos,ratio,all⟩ := ExtendedModulusPrimeSupply.bounds_of_stages (F:=F) modulus_bounds.1
    modulus_bounds.2 (by decide +kernel) room (by decide +kernel) (by decide +kernel) (extended h)
  refine ⟨l,u,pos,ratio,fun v => ?_⟩
  obtain ⟨a,b⟩ : IsUnit v.val.1 ∧ IsUnit v.val.2 :=
    (Commute.all _ _).isUnit_mul_iff.mp (by rw [v.property]; simp)
  simpa only [IsUnit.unit_spec,Prod.eta] using all (a.unit,b.unit)

end PrimeFactors.FiveSquarePrimeSupply
