import PrimeFactors.QuarticDivisorWindow
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PrimeFactors.DivisorWindowRank

open Polynomial Finset Module

private theorem rank_budget {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {k r : ℕ} (f : V →ₗ[K] (Fin r → K))
    (onto : Function.Surjective f) (row : Fin k → V) (li : LinearIndependent K row)
    (zero : ∀ i, f (row i)=0) : k+r ≤ finrank K V := by
  let inner (i : Fin k) : LinearMap.ker f := ⟨row i,zero i⟩
  have indep : LinearIndependent K inner := LinearIndependent.of_comp (LinearMap.ker f).subtype li
  have kr : Fintype.card (Fin k) ≤ finrank K (LinearMap.ker f) := indep.fintype_card_le_finrank
  have rank := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr onto,finrank_top,Module.finrank_pi] at rank
  simp only [Fintype.card_fin] at kr rank
  omega

/-- k independent polynomial constraints of degree below h leave room for at most h−k
distinct common roots. The nodes may be any finite sample of up to h putative roots. -/
theorem common_roots {K : Type*} [Field K] {k h r : ℕ} (within : r≤h)
    (row : Fin k → degreeLT K h) (indep : LinearIndependent K row)
    (node : Fin r → K) (distinct : Function.Injective node)
    (roots : ∀ i j, (row i).val.eval (node j) = 0) : k+r≤h := by
  classical
  let mapAt : degreeLT K h →ₗ[K] (Fin r → K) :=
    { toFun := fun p j => p.val.eval (node j)
      map_add' := by intro p q; funext j; exact eval_add
      map_smul' := by intro a p; funext j; simp }
  have onto : Function.Surjective mapAt := by
    intro target
    have inj : Set.InjOn node (↑(univ : Finset (Fin r))) := distinct.injOn
    let p := Lagrange.interpolate univ node target
    have small : p∈degreeLT K r := by
      apply mem_degreeLT.mpr
      simpa using Lagrange.degree_interpolate_lt target inj
    refine ⟨⟨p,degreeLT_mono within small⟩,?_⟩
    funext j
    exact Lagrange.eval_interpolate_at_node target inj (mem_univ j)
  letI : FiniteDimensional K (degreeLT K h) := (degreeLTEquiv K h).symm.finiteDimensional
  have width : finrank K (degreeLT K h) = h := by
    rw [(degreeLTEquiv K h).finrank_eq,Module.finrank_pi]; simp
  rw [←width]
  exact rank_budget mapAt onto row indep (fun i => funext (roots i))

/-- With at least one independent relation, no separate a priori bound on
the number of distinct common roots is needed. -/
theorem positive_rank_bound {K : Type*} [Field K] {k h r : ℕ} (positive : 0<k)
    (row : Fin k → degreeLT K h) (indep : LinearIndependent K row)
    (node : Fin r → K) (distinct : Function.Injective node)
    (roots : ∀ i j, (row i).val.eval (node j)=0) : k+r≤h := by
  by_cases within : r≤h
  · exact common_roots within row indep node distinct roots
  have le : h≤r := by omega
  have restrict := common_roots (le_refl h) row indep (fun i : Fin h => node (i.castLE le))
    (distinct.comp (fun _ _ eq => Fin.ext (congrArg (fun z : Fin r => z.val) eq))) (fun i j => roots i (j.castLE le))
  omega

private theorem misses_parity {v : Fin 5 → ℤ} {x y : ℤ} (parity : x ≡ y [ZMOD 2])
    (miss : QuarticFactorLane.value (QuarticDivisorWindow.weights v) 1 y % 2 ≠ 0) :
    QuarticFactorLane.value (QuarticDivisorWindow.weights v) 1 x ≠ 0 := by
  intro root
  have h := (Int.modEq_iff_dvd.mp parity).trans
    (Polynomial.sub_dvd_eval_sub y x (QuarticFactorLane.polynomial (QuarticDivisorWindow.weights v) 1))
  rw [QuarticFactorLane.eval_polynomial,QuarticFactorLane.eval_polynomial,root,sub_zero] at h
  exact miss (Int.emod_eq_zero_of_dvd h)

/-- Two rows can jointly exclude a window even when each polynomial has a root
modulo two. Only the even offset of one and the odd offset of the other are tested. -/
theorem joint_parity {evenRow oddRow : Fin 5 → ℤ} {n t d x : ℤ} {W : ℕ}
    (j0 : QuarticDivisorWindow.jets evenRow n t) (j1 : QuarticDivisorWindow.jets oddRow n t)
    (s0 : QuarticDivisorWindow.height evenRow W < d^2) (s1 : QuarticDivisorWindow.height oddRow W < d^2)
    (m0 : QuarticFactorLane.value (QuarticDivisorWindow.weights evenRow) 1 0 % 2 ≠ 0)
    (m1 : QuarticFactorLane.value (QuarticDivisorWindow.weights oddRow) 1 1 % 2 ≠ 0)
    (offset : d ∣ x-t) (nearby : |x|≤W) : ¬ d ∣ n := by
  intro hd
  have parity : x ≡ 0 [ZMOD 2] ∨ x ≡ 1 [ZMOD 2] := by change x%2=0%2 ∨ x%2=1%2; omega
  rcases parity with h|h
  · exact misses_parity h m0 (QuarticDivisorWindow.root_of_divisor j0 hd offset nearby s0)
  · exact misses_parity h m1 (QuarticDivisorWindow.root_of_divisor j1 hd offset nearby s1)

/-- The four nonconstant coefficients of each row as a square system.
A common root x solves A·(x,x²,x³,x⁴) = −(the constant coefficients). -/
noncomputable def nonconstant (row : Fin 4 → Fin 5 → ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => row i j.succ

/-- Cramer's first numerator equals the first unknown times the determinant,
including the singular case. A nonzero denominator yields at most one signed offset. -/
theorem cramer_offset (row : Fin 4 → Fin 5 → ℤ) (x : ℤ)
    (roots : ∀ i, QuarticFactorLane.value (QuarticDivisorWindow.weights (row i)) 1 x=0) :
    ((nonconstant row).updateCol 0 (fun i => -row i 0)).det = (nonconstant row).det*x := by
  let A := nonconstant row
  let powers : Fin 4 → ℤ := ![x,x^2,x^3,x^4]
  have solve : A.mulVec powers = (fun i => -row i 0) := by
    funext i
    have hr := roots i
    simp only [QuarticFactorLane.value,QuarticDivisorWindow.weights,one_pow,mul_one] at hr
    change (∑ j : Fin 4, row i j.succ * powers j) = -row i 0
    rw [Fin.sum_univ_four]
    change row i 1*x+row i 2*x^2+row i 3*x^3+row i 4*x^4 = _
    linarith only [hr]
  change (A.updateCol 0 _).det=A.det*x
  rw [←Matrix.cramer_apply,←solve,Matrix.cramer_eq_adjugate_mulVec,Matrix.mulVec_mulVec,
    Matrix.adjugate_mul,Matrix.smul_mulVec_assoc,Matrix.one_mulVec]
  rfl

theorem recover_offset (row : Fin 4 → Fin 5 → ℤ) (x : ℤ)
    (nonsingular : (nonconstant row).det ≠ 0)
    (roots : ∀ i, QuarticFactorLane.value (QuarticDivisorWindow.weights (row i)) 1 x=0) :
    ((nonconstant row).updateCol 0 (fun i => -row i 0)).det / (nonconstant row).det = x := by
  rw [cramer_offset row x roots,Int.mul_ediv_cancel_left _ nonsingular]

end PrimeFactors.DivisorWindowRank
