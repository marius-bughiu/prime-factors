import PrimeFactors.WidePrimePairSumFrequency
import PrimeFactors.PrimeProductRegion

/-! Frequency of the two distinguished sum residues modulo 25 across the
complete region of pairs of distinct 1,024-bit primes with 2,048-bit product
congruent to one modulo 25. -/

namespace PrimeFactors.FullRangePrimeSumShare

open Finset ResiduePairWeights
open WidePrimePairSumFrequency (selected local_counts)

set_option exponentiation.threshold 4096

private theorem compare_ten {α : Type*} (f : α → ℕ) {S T : Finset α} {δ : ℕ}
    (sSize : S.card=10) (tSize : T.card=10)
    (gap : ∀ x∈S, ∀ y∈T, f x≤f y+δ) :
    ∑ x∈S,f x ≤ (∑ y∈T,f y)+10*δ := by
  have row (x : α) (hx : x∈S) := sum_le_sum (s:=T) (fun y hy => gap x hx y hy)
  simp only [sum_const,smul_eq_mul,sum_add_distrib,tSize] at row
  have all := sum_le_sum (s:=S) row
  rw [←mul_sum,sum_const,smul_eq_mul,sSize] at all
  omega

private theorem ratio {g t b δ L F : ℕ} (fp : 0<F) (lp : 0<L)
    (split : 2*t=2*g+b) (totalLo : 20*L≤2*t)
    (left : 2*g≤b+10*δ) (right : b≤2*g+10*δ) (budget : F*δ≤L) :
    |(g:ℚ)/t-1/2|≤1/(4*(F:ℚ)) := by
  have tpos : (0:ℚ)<t := by exact_mod_cast (by omega : 0<t)
  have fpos : (0:ℚ)<F := by exact_mod_cast fp
  have bounds : |2*(g:ℚ)-t|≤5*(δ:ℚ) := by
    have split' : 2*(t:ℚ)=2*(g:ℚ)+b := by exact_mod_cast split
    have left' : 2*(g:ℚ)≤b+10*(δ:ℚ) := by exact_mod_cast left
    have right' : (b:ℚ)≤2*(g:ℚ)+10*(δ:ℚ) := by exact_mod_cast right
    exact abs_le.mpr ⟨by linarith only [split',right'],by linarith only [split',left']⟩
  have total' : 20*(L:ℚ)≤2*(t:ℚ) := by exact_mod_cast totalLo
  have budget' : (F:ℚ)*δ≤L := by exact_mod_cast budget
  have eq : (g:ℚ)/t-1/2=(2*g-t)/(2*t) := by field_simp; ring
  rw [eq,abs_div,abs_of_pos (by positivity : (0:ℚ)<2*t),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have weighted := mul_le_mul_of_nonneg_right bounds (by positivity : 0≤4*(F:ℚ))
  nlinarith only [weighted,budget',total']

/-- Transfer the ten-versus-ten local partition to counts of unordered
prime pairs. Every ordered cell may have a different population. -/
theorem from_cells (f : ZMod 25 × ZMod 25 → ℕ) {g t δ L F : ℕ}
    (fp : 0<F) (lp : 0<L) (budget : F*δ≤L)
    (G : 2*g=∑ v∈cells (1:ZMod 25) selected,f v)
    (T : 2*t=∑ v∈cells (1:ZMod 25) univ,f v)
    (lo : ∀ v∈cells (1:ZMod 25) univ, L≤f v)
    (gap : ∀ v∈cells (1:ZMod 25) univ, ∀ w∈cells (1:ZMod 25) univ, f v≤f w+δ) :
    |(g:ℚ)/t-1/2|≤1/(4*(F:ℚ)) := by
  classical
  let S := cells (1:ZMod 25) selected
  let A := cells (1:ZMod 25) univ
  let C := A \ S
  have sub : S⊆A := fun v hv => mem_filter.mpr
    ⟨mem_univ _,(mem_filter.mp hv).2.1,mem_univ _⟩
  have subC : C⊆A := sdiff_subset
  have sizeS : S.card=10 := local_counts.1
  have sizeA : A.card=20 := local_counts.2.1
  have sizeC : C.card=10 := by rw [show C=A \ S by rfl,card_sdiff sub,sizeA,sizeS]
  have sumC := sum_sdiff sub (f:=f)
  change (∑ v∈C,f v)+(∑ v∈S,f v)=∑ v∈A,f v at sumC
  change 2*g=∑ v∈S,f v at G
  change 2*t=∑ v∈A,f v at T
  have loT := sum_le_sum (s:=A) lo
  rw [sum_const,smul_eq_mul,sizeA,←T] at loT
  have h₁ := compare_ten f sizeS sizeC (fun x hx y hy => gap x (sub hx) y (subC hy))
  have h₂ := compare_ten f sizeC sizeS (fun x hx y hy => gap x (subC hx) y (sub hy))
  rw [←G] at h₁ h₂ sumC
  rw [←T] at sumC
  exact ratio fp lp (by omega) loT h₁ h₂ budget

/-- Uniformly weight each distinct pair with p<q and product 1 modulo 25
in the full 2,048-bit region. The numerator selects sums 2 and 23 modulo 25. -/
noncomputable def share : ℚ :=
  ((PrimeProductRegion.population selected).card : ℚ)/(PrimeProductRegion.population univ).card

private theorem units_of_cell {v : ZMod 25 × ZMod 25} (h : v∈cells (1:ZMod 25) univ) :
    IsUnit v.1 ∧ IsUnit v.2 := by
  apply (Commute.all _ _).isUnit_mul_iff.mp
  rw [(mem_filter.mp h).2.1]
  exact isUnit_one

/-- Any uniform estimate for prime-count suffixes meeting this precision
budget controls the share over all products in the region. -/
theorem from_estimates {D U M F : ℕ} (h : FullRangeResidueEstimates.Estimates D U M)
    (positive : 0<F) (atLeastTwo : 2≤M) (budget : F*(2*D*U+U)≤M*(M-1)) :
    |share-1/2|≤1/(4*(F:ℚ)) := by
  unfold share
  have lower : 0<M*(M-1) := Nat.mul_pos (by omega) (by omega)
  apply from_cells PrimeProductRegion.cell positive lower budget
    (PrimeProductRegion.twice_count selected) (PrimeProductRegion.twice_count univ)
  · intro v hv
    have u := units_of_cell hv
    exact PrimeProductRegion.cell_lower h u.1 u.2
  · intro v hv w hw
    have u := units_of_cell hv
    have u' := units_of_cell hw
    exact PrimeProductRegion.cell_spread h u.1 u.2 u'.1 u'.2

open FullRangeResidueEstimates

/-- With the published unconditional BMOR endpoint estimate supplied,
the share differs from one half by at most 1/1648. -/
theorem bmor_accuracy {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    |share-1/2|≤1/1648 := by
  have bound := from_estimates (bmor h) (by decide : 0<bmorF) two_le_M bmor_precision
  rwa [show 4*(bmorF:ℚ)=1648 by norm_num [bmorF]] at bound

/-- The BMOR bound places the reported percentage between 49.9 and 50.1. -/
theorem bmor_percentage {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    49.9 < 100*share ∧ 100*share < 50.1 := by
  obtain ⟨lo,hi⟩ := abs_le.mp (bmor_accuracy h)
  constructor <;> linarith

/-- With the EHP endpoint estimate under Dirichlet GRH supplied,
the error in the share is at most 2^(-480). -/
theorem ehp_accuracy {li : ℕ → ℝ} (h : EndpointEstimates ehpError25 li) :
    |share-1/2|≤1/(2:ℚ)^480 := by
  have bound := from_estimates (ehp h) (by decide : 0<ehpF) two_le_M ehp_precision
  rwa [show 4*(ehpF:ℚ)=(2:ℚ)^480 by norm_num [ehpF]] at bound

end PrimeFactors.FullRangePrimeSumShare
