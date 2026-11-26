import PrimeFactors.GeometricReadingLift
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! Shared baby polynomial and geometric evaluation points over the composite
scalar modulus, including the last incomplete block. -/
namespace PrimeFactors.GeometricBlockReading
open Finset
variable {R : Type*} [CommRing R]

/-- A scalar geometric product of the given length. -/
noncomputable def block (y : R) (g : Rˣ) (n : ℕ) := ∏ i ∈ range n, (y-(g:R)^i)

/-- All complete blocks evaluate the same monic product at scaled targets.
The only inverses are powers of the known unit g. -/
theorem translated (y : R) (g : Rˣ) (begin width : ℕ) :
    (∏ i ∈ range width, (y-(g:R)^(begin+i))) =
      ((g:R)^begin)^width * block (y*(↑(g⁻¹):R)^begin) g width := by
  unfold block
  rw [show ((g:R)^begin)^width = ∏ _i ∈ range width, (g:R)^begin by simp]
  rw [←prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  have inv : (g:R)^begin * (↑(g⁻¹):R)^begin = 1 := by
    rw [←mul_pow,Units.mul_inv,one_pow]
  rw [pow_add,mul_sub]
  rw [show (g:R)^begin * (y*(↑(g⁻¹):R)^begin) = y*((g:R)^begin*(↑(g⁻¹):R)^begin) by ring,inv,mul_one]

theorem full_blocks (y : R) (g : Rˣ) (b q : ℕ) :
    block y g (b*q) = ∏ j ∈ range q,
      (((g:R)^(b*j))^b * block (y*((↑(g⁻¹):R)^(b*j))) g b) := by
  induction q with
  | zero => simp [block]
  | succ q ih =>
    rw [prod_range_succ,Nat.mul_succ]
    unfold block at ih ⊢
    rw [prod_range_add,ih]
    congr 1
    exact translated y g (b*q) b

theorem with_tail (y : R) (g : Rˣ) (b q r : ℕ) :
    block y g (b*q+r) =
      (∏ j ∈ range q, (((g:R)^(b*j))^b * block (y*((↑(g⁻¹):R)^(b*j))) g b)) *
        ∏ i ∈ range r, (y-(g:R)^(b*q+i)) := by
  rw [←full_blocks]
  exact prod_range_add _ _ _

end PrimeFactors.GeometricBlockReading
