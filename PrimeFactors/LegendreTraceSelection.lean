import PrimeFactors.ExtensionTrace
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots

namespace PrimeFactors.LegendreTraceSelection

open Polynomial PrimeFactors.ExtensionTrace

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Reduction of the Legendre trace modulo the characteristic, with the
curve parameter as the sole polynomial variable. -/
noncomputable def parameterPolynomial (F : Type*) [Field F] [Fintype F] [DecidableEq F] : F[X] :=
  ∑ x : F, C (quadraticChar F (x*(x-1)) : F) * (C x-X)^(Fintype.card F/2)

theorem eval_parameter (odd : ringChar F ≠ 2) (l : F) :
    (parameterPolynomial F).eval l = (trace (-(1+l)) l 0 : F) := by
  unfold parameterPolynomial trace
  rw [Polynomial.eval_finset_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [show cubic (-(1+l)) l 0 x = x*(x-1)*(x-l) by unfold cubic; ring,
    map_mul (quadraticChar F) (x*(x-1)) (x-l), Int.cast_mul,
    quadraticChar_eq_pow_of_char_ne_two' odd (x-l)]
  simp

theorem degree_bound : (parameterPolynomial F).natDegree ≤ Fintype.card F/2 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x _
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  rw [Polynomial.natDegree_pow]
  have deg : (C x-X : F[X]).natDegree ≤ 1 := (Polynomial.natDegree_sub_le _ _).trans (by simp)
  simpa [mul_comm] using Nat.mul_le_mul_left (Fintype.card F/2) deg

private theorem parameter_nonzero (odd : ringChar F ≠ 2) : parameterPolynomial F ≠ 0 := by
  have translated := Equiv.sum_comp (Equiv.subRight (1 : F)) (quadraticChar F)
  change (∑ x : F, quadraticChar F (x-1)) = ∑ x : F, quadraticChar F x at translated
  rw [quadraticChar_sum_zero odd] at translated
  have term (x : F) : quadraticChar F (cubic (-(1+(0:F))) 0 0 x) =
      quadraticChar F (x-1) - (if x=0 then quadraticChar F (-1) else 0) := by
    by_cases zero : x=0
    · simp [zero,cubic]
    · rw [show cubic (-(1+(0:F))) 0 0 x=x^2*(x-1) by unfold cubic; ring,
        map_mul, map_pow, quadraticChar_sq_one zero, if_neg zero]
      ring
  have atZero : trace (-(1+(0:F))) 0 0 = -quadraticChar F (-1) := by
    unfold trace
    simp_rw [term]
    rw [Finset.sum_sub_distrib, translated]
    simp
  intro zero
  have ev := eval_parameter odd (0 : F)
  rw [zero, Polynomial.eval_zero, atZero, Int.cast_neg] at ev
  rcases quadraticChar_dichotomy (F := F) (neg_ne_zero.mpr one_ne_zero) with pos | neg
  · simp [pos] at ev
  · simp [neg] at ev

/-- At most half the field parameters give zero integer trace. This counts
even the two singular parameters, whose presence cannot spoil the bound. -/
theorem zero_count (odd : ringChar F ≠ 2) :
    (Finset.univ.filter (fun l : F => trace (-(1+l)) l 0 = 0)).card ≤ Fintype.card F/2 := by
  classical
  apply le_trans _ (degree_bound (F := F))
  apply Polynomial.card_le_degree_of_subset_roots
  intro l hl
  have zero := (Finset.mem_filter.mp (show l ∈ Finset.univ.filter _ from hl)).2
  exact (Polynomial.mem_roots (parameter_nonzero odd)).mpr (by
    change (parameterPolynomial F).eval l = 0
    rw [eval_parameter odd, zero, Int.cast_zero])

end PrimeFactors.LegendreTraceSelection
