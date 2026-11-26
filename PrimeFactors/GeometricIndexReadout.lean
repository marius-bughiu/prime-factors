import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Ring

/-! The two first derivatives of a geometric progression product can identify
its hidden index when the derivative in the target direction is invertible. -/

namespace PrimeFactors.GeometricIndexReadout
open Finset

variable {R : Type*} [CommRing R]

/-- Product with one specified index omitted. The indices themselves remain labeled. -/
noncomputable def omitted (S : Finset ℕ) (y g : R) (i : ℕ) : R :=
  ∏ j ∈ S.erase i, (y-g^j)

/-- Derivative in y of the product of the terms y−g^j. -/
noncomputable def targetDerivative (S : Finset ℕ) (y g : R) : R :=
  ∑ i ∈ S, omitted S y g i

/-- Logarithmic base derivative g ∂/∂g of the same product. This definition
by the product rule applies to g=0 as well. -/
noncomputable def baseTangent (S : Finset ℕ) (y g : R) : R :=
  -(∑ i ∈ S, (i:R)*g^i*omitted S y g i)

private theorem vanish {S : Finset ℕ} {y g : R} {j i : ℕ} (hj : j∈S)
    (hit : y=g^j) (ne : i≠j) : omitted S y g i=0 := by
  apply prod_eq_zero (mem_erase.mpr ⟨ne.symm,hj⟩)
  simp only [hit,sub_self]

/-- Every summand other than the occupied index contains an actual zero factor. -/
theorem derivatives_at {S : Finset ℕ} {y g : R} {j : ℕ} (hj : j∈S) (hit : y=g^j) :
    targetDerivative S y g=omitted S y g j ∧
    baseTangent S y g= -((j:R)*y*omitted S y g j) := by
  have a := sum_eq_single_of_mem j hj (fun i _ h => vanish hj hit h)
  have b := sum_eq_single_of_mem (f := fun i : ℕ => (i:R)*g^i*omitted S y g i) j hj
    (fun i _ h => by simp only [vanish hj hit h, mul_zero])
  exact ⟨a, by change -(∑ i ∈ S, (i:R)*g^i*omitted S y g i) = _; rw [b]; dsimp; rw [← hit]⟩

/-- A public inverse of y times the target derivative recovers the index in R. -/
theorem readout {S : Finset ℕ} {y g v : R} {j : ℕ} (hj : j∈S) (hit : y=g^j)
    (inverse : y*targetDerivative S y g*v=1) :
    -baseTangent S y g*v=(j:R) := by
  obtain ⟨der,tan⟩ := derivatives_at hj hit
  rw [der] at inverse
  rw [tan,neg_neg]
  calc
    (j:R)*y*omitted S y g j*v = (j:R)*(y*omitted S y g j*v) := by ring
    _ = _ := by rw [inverse,mul_one]

/-- In a ring, invertibility follows when the target and every competing
root difference are units. A field needs just a nonzero target and a unique root. -/
theorem can_read {S : Finset ℕ} {y g : R} {j : ℕ} (hj : j∈S) (hit : y=g^j)
    (yu : IsUnit y) (simple : ∀ i∈S, i≠j → IsUnit (y-g^i)) :
    IsUnit (y*targetDerivative S y g) := by
  rw [(derivatives_at hj hit).1]
  apply yu.mul
  apply IsUnit.prod_iff.mpr
  intro i hi
  obtain ⟨ne,mem⟩ := mem_erase.mp hi
  exact simple i mem ne

/-- Reducing the recovered residue gives the actual natural index when it is below n. -/
theorem index_nat {n : ℕ} {S : Finset ℕ} {y g v : ZMod n} {j : ℕ} (small : j<n)
    (hj : j∈S) (hit : y=g^j) (inverse : y*targetDerivative S y g*v=1) :
    (-baseTangent S y g*v).val=j := by
  rw [readout hj hit inverse,ZMod.val_natCast_of_lt small]

/-- Both derivatives vanish when at least two indices hit in the ring (in
particular, over either residue field of a semiprime). -/
theorem double_zero {S : Finset ℕ} {y g : R} {i j : ℕ} (hi : i∈S) (hj : j∈S)
    (ne : j≠i) (a : y=g^i) (b : y=g^j) :
    targetDerivative S y g=0 ∧ baseTangent S y g=0 := by
  have ve := vanish hi a ne
  obtain ⟨l,r⟩ := derivatives_at hj b
  simp only [l,r,ve,mul_zero,neg_zero,and_self]

/-- Over a field, a single occupied index and a nonzero target suffice. -/
theorem field_simple {K : Type*} [Field K] {S : Finset ℕ} {y g : K} {j : ℕ}
    (hj : j ∈ S) (hit : y = g^j) (hy : y ≠ 0)
    (unique : ∀ i ∈ S, y = g^i → i = j) : IsUnit (y * targetDerivative S y g) := by
  apply can_read hj hit (isUnit_iff_ne_zero.mpr hy)
  intro i hi ne
  exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun e => ne (unique i hi e)))

section Examples

-- For N=33127 and an origin of 365, the public target is g^(N+1−365).
private abbrev residues := ZMod 33127
private abbrev labels := range 22
private theorem in_labels : 3 ∈ labels := by decide

/-- The recovered index 3 gives the factor sum 365+3. -/
theorem example_unit :
    (2:residues)^32763 = 8 ∧ targetDerivative labels (8:residues) 2 = 3812 ∧
    baseTangent labels (8:residues) 2 = 7893 ∧
    (-baseTangent labels (8:residues) 2 * 4772).val = 3 ∧
    Nat.Prime 157 ∧ Nat.Prime 211 ∧ 157*211 = (33127:ℕ) ∧ 157+211 = (365+3:ℕ) := by
  have h : (8:residues) = 2^3 := by decide +kernel
  obtain ⟨d,t⟩ := derivatives_at in_labels h
  have o : omitted labels (8:residues) 2 3 = 3812 := by decide +kernel
  rw [o] at d t
  refine ⟨by unfold residues; reduce_mod_char, d, t.trans (by decide +kernel), ?_, by norm_num1,
    by norm_num1, rfl, rfl⟩
  apply index_nat (by decide : 3 < 33127) in_labels h
  rw [d]
  decide +kernel

/-- A repeated target in just one residue field exposes its prime by a gcd. -/
theorem example_proper_gcd :
    (13:residues)^32763 = 2197 ∧ targetDerivative labels (2197:residues) 13 = 15700 ∧
    baseTangent labels (2197:residues) 13 = 10048 ∧
    Nat.gcd (targetDerivative labels (2197:residues) 13).val 33127 = 157 := by
  have h : (2197:residues) = 13^3 := by decide +kernel
  obtain ⟨d,t⟩ := derivatives_at in_labels h
  have o : omitted labels (2197:residues) 13 3 = 15700 := by decide +kernel
  rw [o] at d t
  exact ⟨by unfold residues; reduce_mod_char, d, t.trans (by decide +kernel), by rw [d]; decide +kernel⟩

/-- A unique global index can coexist with zero first derivatives modulo N. -/
theorem example_invisible :
    (12:residues)^32763 = 1728 ∧
    (∀ i : Fin 22, (12:residues)^i.val = 1728 ↔ i.val = 3) ∧
    targetDerivative labels (1728:residues) 12 = 0 ∧
    baseTangent labels (1728:residues) 12 = 0 := by
  have h : (1728:residues) = 12^3 := by decide +kernel
  obtain ⟨d,t⟩ := derivatives_at in_labels h
  have o : omitted labels (1728:residues) 12 3 = 0 := by decide +kernel
  rw [o] at d t
  exact ⟨by unfold residues; reduce_mod_char, by decide +kernel, d, by simpa only [mul_zero, neg_zero] using t⟩

end Examples
end PrimeFactors.GeometricIndexReadout
