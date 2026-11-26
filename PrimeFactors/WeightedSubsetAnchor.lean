import PrimeFactors.WeightedSubsetPopulation
import PrimeFactors.WeightedTripleSupport
import PrimeFactors.WeightedSubsetMenu
import PrimeFactors.WeightedSubsetFiber

/-! A successful nonproportional subset has a row whose squarefree part
divides a single positive integer depending only on the full menu and that
row. This counts all choices of the remaining subset simultaneously. -/
namespace PrimeFactors.WeightedSubsetAnchor
open Finset WeightedMultiplierPopulation WeightedSubsetMenu
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

abbrev Id := Fin 8 × Fin 2

def weight (i : Id) := i.1.val+1
def label (n : ℕ) (i : Id) := vector n i.1 i.2
def excess (n : ℕ) (i : Id) := (label n i)^2-4*weight i*n

theorem eq_row (n : ℕ) (i : Id) : (label n i)^2=excess n i+4*weight i*n :=
  (Nat.sub_add_cancel (WeightedMultiplierLabels.above n (weight i) i.2.val)).symm

theorem in_window (n : ℕ) (i : Id) : Label (weight i) 2 (label n i) (Real.sqrt n) :=
  WeightedMultiplierLabels.inside i.2.isLt

private theorem weight_bounds (i : Id) : 0<weight i ∧ weight i≤8 :=
  ⟨Nat.succ_pos _,i.1.isLt⟩

def determinant (V : Vector) (i j : Id) :=
  difference (weight i,weight j) (V i.1 i.2) (V j.1 j.2)

private def factorAt (V : Vector) (i j : Id) := max 1 (determinant V i j)

noncomputable def modulus (V : Vector) (i : Id) := ∏ j ∈ univ.erase i, factorAt V i j

theorem modulus_pos (V : Vector) (i : Id) : 0<modulus V i :=
  Finset.prod_pos (fun _ _ => lt_of_lt_of_le (by decide : 0<1) (le_max_left ..))

private abbrev X : ℕ := 2^1023

theorem modulus_lt {n : ℕ} (top : Real.sqrt n≤2*(2:ℝ)^1023) (i : Id) :
    modulus (vector n) i<2^(15*1037) := by
  have bounds (j : Id) : factorAt (vector n) i j ≤ 2^1037-1 := by
    obtain ⟨rp,rk⟩ := weight_bounds i
    obtain ⟨sp,sk⟩ := weight_bounds j
    have h := difference_lt rp sp rk sk (by decide : 8≤3^2) (by decide +kernel : 24*2≤3*X)
      (Real.sqrt_nonneg _) (by exact_mod_cast top : Real.sqrt n≤2*(X:ℝ)) (in_window n i) (in_window n j)
    have small : determinant (vector n) i j<2^1037 := h.trans_le (by decide +kernel)
    exact max_le (by decide +kernel) (by omega)
  have card : ((univ : Finset Id).erase i).card=15 := by
    rw [card_erase_of_mem (mem_univ _),card_univ]
    decide
  calc
    modulus (vector n) i ≤ ∏ _j ∈ univ.erase i, (2^1037-1) :=
      Finset.prod_le_prod' (fun j _ => bounds j)
    _ = (2^1037-1)^15 := by rw [prod_const,card]
    _ < ((2:ℕ)^1037)^15 := Nat.pow_lt_pow_left (by decide +kernel) (by decide)
    _ = _ := by rw [←pow_mul,Nat.mul_comm 1037]

private theorem excess_le {n : ℕ} (top : Real.sqrt n≤2*(2:ℝ)^1023) (i : Id) :
    excess n i≤(2^517)^2 := by
  obtain ⟨rp,rk⟩ := weight_bounds i
  have h := (WeightedMultiplierPopulation.excess rp (rk.trans (by decide : 8≤3^2))
    (by decide +kernel : 24*2≤3*X) (Real.sqrt_nonneg _)
    (by exact_mod_cast top : Real.sqrt n≤2*(X:ℝ)) (in_window n i)).2
  rw [Real.sq_sqrt (Nat.cast_nonneg n)] at h
  have eq : (label n i:ℝ)^2=excess n i+4*(weight i:ℝ)*n := by exact_mod_cast eq_row n i
  rw [eq,add_sub_cancel_right] at h
  have hi : excess n i<216*3*X*2 := by exact_mod_cast h
  exact hi.le.trans (by decide +kernel)

theorem hit_candidate {n : ℕ} (top : Real.sqrt n≤2*(2:ℝ)^1023) (T : Finset Id)
    (nonempty : T.Nonempty) (pos : ∀ i∈T, 0<excess n i)
    (distinct : ∀ i∈T, ∀ j∈T, i≠j → weight j*(label n i)^2≠weight i*(label n j)^2)
    (square : ∃ z : ℕ, (∏ i∈T, excess n i)=z^2) :
    WeightedSubsetPopulation.Candidate modulus n := by
  classical
  obtain ⟨i,hi⟩ := nonempty
  obtain ⟨z,hz⟩ := square
  have rem : 0<∏ j∈T.erase i, excess n j :=
    Finset.prod_pos (fun j hj => pos j (mem_of_mem_erase hj))
  have joint : excess n i*(∏ j∈T.erase i, excess n j)=z^2 :=
    (T.mul_prod_erase _ hi).trans hz
  have supported (p : ℕ) (prime : p.Prime) (pd : p∣excess n i)
      (pr : p∣∏ j∈T.erase i, excess n j) : p∣modulus (vector n) i := by
    obtain ⟨j,hj,dj⟩ := (prime.prime.dvd_finset_prod_iff _).mp pr
    have ne := ne_of_mem_erase hj
    have det : 0<determinant (vector n) i j := by
      apply Nat.pos_of_ne_zero
      intro zero
      have same : (weight j:ℤ)*(label n i)^2=(weight i:ℤ)*(label n j)^2 :=
        sub_eq_zero.mp (Int.natAbs_eq_zero.mp zero)
      exact distinct i hi j (mem_of_mem_erase hj) ne.symm (by exact_mod_cast same)
    have div : p∣determinant (vector n) i j :=
      WeightedTripleSupport.common_divides_cross (eq_row n i) (eq_row n j) pd dj
    have lo : 1≤determinant (vector n) i j := det
    have term : p∣factorAt (vector n) i j := by simpa only [factorAt,max_eq_right lo] using div
    exact term.trans (Finset.dvd_prod_of_mem _ (mem_erase.mpr ⟨ne,mem_univ _⟩))
  obtain ⟨m,u,_,sf,eq,_,div⟩ := WeightedTripleSupport.supported_kernel (pos i hi) rem joint supported
  have up : 0<u := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    simp only [zero_pow (by decide : 2≠0),mul_zero] at eq
    exact (pos i hi).ne' eq
  refine ⟨i,modulus_pos _ _,modulus_lt top _,m,u,sf,div,up,?_,?_⟩
  · rw [←eq]
    exact excess_le top i
  · rw [←eq]
    exact eq_row n i

end PrimeFactors.WeightedSubsetAnchor
