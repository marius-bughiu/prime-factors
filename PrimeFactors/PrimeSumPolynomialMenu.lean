import PrimeFactors.PrimeSumPolynomialPopulation

/-! Coverage of any member of a fixed finite menu of rational polynomial
relations, even when the selector uses the entire public product. -/

namespace PrimeFactors.PrimeSumPolynomialMenu

open Finset MvPolynomial PrimeSumPolynomialPopulation
open MixedPrefixSample (eligible primes)

set_option exponentiation.threshold 2048
attribute [local irreducible] eligible primes

private theorem in_hits {R : ℕ → ℕ → Prop} {z : ℕ×ℕ} :
    z∈hits R ↔ z∈eligible ∧ R (z.1*z.2) (z.1+z.2) := by
  classical simp only [hits,mem_filter]

private theorem in_grid {R : ℕ → ℕ → Prop} {A : Finset ℕ} {z : ℕ×ℕ} :
    z∈grid A R ↔ z∈A×ˢA ∧ R (z.1*z.2) (z.1+z.2) := by
  classical simp only [grid,mem_filter]

attribute [local irreducible] hits grid

abbrev Poly := MvPolynomial (Fin 2) ℚ

def agrees (F : Poly) (n s : ℕ) : Prop := eval ![(n:ℚ),(s:ℚ)] F=0

noncomputable def product (menu : Finset Poly) : Poly := ∏ F ∈ menu, F
noncomputable def cost (menu : Finset Poly) : ℕ := ∑ F ∈ menu, F.totalDegree

/-- Count all pairs where at least one menu member holds, even if the
observer has no way to identify a successful choice. -/
noncomputable abbrev possible (menu : Finset Poly) := hits (agrees (product menu))

theorem mem_possible {menu : Finset Poly} {z : ℕ × ℕ} :
    z∈possible menu ↔ z∈eligible ∧ ∃ F∈menu, agrees F (z.1*z.2) (z.1+z.2) := by
  classical
  simp only [possible,in_hits,agrees,product,map_prod,prod_eq_zero_iff]

/-- The selector may use any function of N and may abstain. -/
noncomputable def chosen (select : ℕ → Option Poly) :=
  hits fun n s => ∃ F, select n=some F ∧ agrees F n s

theorem chosen_subset (menu : Finset Poly) (select : ℕ → Option Poly)
    (allowed : ∀ n F, select n=some F → F∈menu) : chosen select ⊆ possible menu := by
  classical
  intro z hz
  rw [chosen,in_hits] at hz
  obtain ⟨eligible_z,F,selected,hit⟩ := hz
  exact mem_possible.mpr ⟨eligible_z,F,allowed _ F selected,hit⟩

theorem product_nonzero {menu : Finset Poly} (nz : ∀ F∈menu, F≠0) :
    product menu≠0 := prod_ne_zero_iff.mpr nz

theorem product_degree (menu : Finset Poly) : (product menu).totalDegree≤cost menu :=
  totalDegree_finset_prod menu id

private theorem grid_bound (menu : Finset Poly) (nz : ∀ F∈menu, F≠0) :
    (grid primes (agrees (product menu))).card≤2*(cost menu)*primes.card := by
  classical
  have localBound := PrimeSumPolynomialGrid.nat_grid_bound primes (product menu) (product_nonzero nz)
  apply le_trans _ (localBound.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (product_degree menu))))
  apply card_le_card
  intro z hz
  rw [in_grid] at hz
  exact mem_filter.mpr hz

private theorem empty_of_zero {α : Type*} (S : Finset α) {g d a : ℕ}
    (twice : 2*S.card≤g) (bound : g≤2*d*a) (zero : d=0) : S=∅ := by
  subst d
  simp at bound
  exact card_eq_zero.mp (by omega)

/-- For positive total degree D, the fraction covered by the entire menu is
strictly below D/2^1007. The zero-cost case has no successes. -/
theorem cost_bound (menu : Finset Poly) (nz : ∀ F∈menu, F≠0) :
    (0<cost menu → 2^1007*(possible menu).card<cost menu*eligible.card) ∧
    (cost menu=0 → possible menu=∅) := by
  have g := grid_bound menu nz
  constructor
  · intro pos
    exact fraction (agrees (product menu)) pos g
  · exact empty_of_zero (possible menu) (twice_hits (agrees (product menu))) g

/-- The product-dependent selector inherits the bound for the whole menu. -/
theorem selector_budget (menu : Finset Poly) (nz : ∀ F∈menu,F≠0) (select : ℕ → Option Poly)
    (allowed : ∀ n F, select n=some F → F∈menu) {k : ℕ} (limit : k≤1007) (cap : cost menu≤2^k) :
    2^(1007-k)*(chosen select).card<eligible.card :=
  (Nat.mul_le_mul_left _ (card_le_card (chosen_subset menu select allowed))).trans_lt
    (polynomial_budget (product menu) (product_nonzero nz) limit ((product_degree menu).trans cap))

theorem cost_of_max (menu : Finset Poly) {D : ℕ} (bound : ∀ F∈menu,F.totalDegree≤D) :
    cost menu≤menu.card*D := by
  simpa only [cost,sum_const,nsmul_eq_mul] using sum_le_sum bound

/-- At most 2^32 entries, each of degree at most 2^96, cover fewer than one
in 2^879 of the eligible pairs under every product-dependent selector. -/
theorem example_budget (menu : Finset Poly) (nz : ∀ F∈menu,F≠0) (select : ℕ → Option Poly)
    (allowed : ∀ n F, select n=some F → F∈menu)
    (size : menu.card≤2^32) (degree : ∀ F∈menu,F.totalDegree≤2^96) :
    2^879*(chosen select).card<eligible.card := by
  apply selector_budget menu nz select allowed (k:=128) (by decide)
  exact (cost_of_max menu degree).trans ((Nat.mul_le_mul_right _ size).trans_eq (by decide))

/-- Clear the denominator of a rational prediction A(N)/B(N). -/
noncomputable def graph (A B : Polynomial ℚ) : Poly :=
  X 1 * Polynomial.aeval (X 0 : Poly) B - Polynomial.aeval (X 0 : Poly) A

theorem graph_eval (A B : Polynomial ℚ) (n s : ℚ) :
    eval ![n,s] (graph A B)=s*B.eval n-A.eval n := by
  have one (P : Polynomial ℚ) :
      eval ![n,s] (Polynomial.aeval (X 0 : Poly) P)=P.eval n := by
    change (MvPolynomial.aeval ![n,s]) (Polynomial.aeval (X 0 : Poly) P)=P.eval n
    rw [←Polynomial.aeval_algHom_apply]
    simp [Polynomial.aeval_def]
    rfl
  simp [graph,one]

theorem graph_nonzero (A B : Polynomial ℚ) (nonzero : B≠0) : graph A B≠0 := by
  intro z
  apply nonzero
  apply Polynomial.funext
  intro n
  have at_zero := graph_eval A B n 0
  have at_one := graph_eval A B n 1
  rw [z,map_zero] at at_zero at_one
  simp only [Polynomial.eval_zero]
  linarith

theorem graph_iff {A B : Polynomial ℚ} {n s : ℕ} (den : B.eval (n:ℚ)≠0) :
    agrees (graph A B) n s ↔ (s:ℚ)=A.eval (n:ℚ)/B.eval (n:ℚ) := by
  rw [agrees,graph_eval,sub_eq_zero,eq_div_iff den]

end PrimeFactors.PrimeSumPolynomialMenu
