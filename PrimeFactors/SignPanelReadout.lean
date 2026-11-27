import PrimeFactors.PrimeSignIsolation
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! A weighted sum of the sign tests returns the unique surviving integer.
Expanding it in the symbols gives one character sum per subset of the panel. -/
namespace PrimeFactors.SignPanelReadout
open Finset

noncomputable def mask {k : ℕ} (z : Fin k → ℤ) (x : ℕ) : ℤ :=
  ∏ i, (jacobiSym (z i) x + (jacobiSym (z i) x)^2)

theorem mask_value {k : ℕ} (z : Fin k → ℤ) (x : ℕ) :
    mask z x = if ∀ i, jacobiSym (z i) x = 1 then 2^k else 0 := by
  classical
  split_ifs with all
  · simp [mask,all]
  · push_neg at all
    obtain ⟨i,hi⟩ := all
    unfold mask
    apply prod_eq_zero (mem_univ i)
    rcases jacobiSym.trichotomy (z i) x with h|h|h <;>
      first | exact False.elim (hi h) | norm_num [h]

/-- If a panel singles out p, its weighted sum equals 2^k times p. -/
theorem weighted_singleton {k p : ℕ} (C : Finset ℕ) (z : Fin k → ℤ)
    (unique : C.filter (fun x => ∀ i, jacobiSym (z i) x = 1) = {p}) :
    (∑ x ∈ C, (x:ℤ)*mask z x) = 2^k*p := by
  classical
  simp_rw [mask_value, mul_ite, mul_zero]
  rw [← sum_filter, unique]
  simp [mul_comm]

/-- Apply the readout to any of the actual affine sign candidate sets. The
input equality is exactly the uniqueness conclusion of the panel theorem. -/
theorem affine_weighted_singleton {N k p : ℕ} (C : Finset ℕ) (w : Fin k → ℕ)
    (valid : ∀ i, w i < N)
    (unique : PrimeSignIsolation.surviving C (AffinePrimeSign.seeds N) w = {p}) :
    (∑ x ∈ C, (x:ℤ)*mask (fun i => 1-4*(N:ℤ)*(w i)) x) = 2^k*p := by
  apply weighted_singleton
  rw [← unique]
  ext x
  classical
  simp [PrimeSignIsolation.surviving, AffinePrimeSign.mem_seeds, AffinePrimeSign.passes, valid]

private noncomputable def character (x : ℕ) : ℤ →* ℤ where
  toFun a := jacobiSym a x
  map_one' := jacobiSym.one_left _
  map_mul' _ _ := jacobiSym.mul_left _ _ _

/-- The complete signed numerator associated with one subset in the expansion. -/
noncomputable def numerator {k : ℕ} (z : Fin k → ℤ) (s : Finset (Fin k)) : ℤ :=
  (∏ i ∈ s, z i) * ∏ i ∈ sᶜ, (z i)^2

theorem expansion {k : ℕ} (C : Finset ℕ) (z : Fin k → ℤ) :
    (∑ x ∈ C, (x:ℤ)*mask z x) =
      ∑ s : Finset (Fin k), ∑ x ∈ C, (x:ℤ)*jacobiSym (numerator z s) x := by
  classical
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [← mul_sum, mask, Fintype.prod_add]
  congr 1
  apply sum_congr rfl
  intro s _
  change _ = character x (numerator z s)
  simp only [numerator, map_mul, map_prod, map_pow]
  rfl

example : (∑ x ∈ ({3,5,7} : Finset ℕ), (x:ℤ)*mask (fun _ : Fin 1 => -307) x) = 14 := by
  norm_num [mask, Fin.prod_univ_one]

end PrimeFactors.SignPanelReadout
