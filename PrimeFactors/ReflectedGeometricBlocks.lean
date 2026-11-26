import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! The finite q-binomial product over a commutative ring. A coefficient
recurrence and reflection recover the geometric root polynomial from its
lower half when the stated denominators are units. -/

namespace PrimeFactors.ReflectedGeometricBlocks
open Finset Polynomial
variable {R : Type*} [CommRing R]

noncomputable def block (h : R) (b : ℕ) : R[X] :=
  ∏ i ∈ range b, (1-C (h^i)*X)

private theorem shifted (h : R) (b : ℕ) :
    (block h b).comp (C h*X)*(1-X)=block h b*(1-C (h^b)*X) := by
  have each (i : ℕ) : (1-C (h^i)*X).comp (C h*X)=1-C (h^(i+1))*X := by
    rw [sub_comp,one_comp,C_mul_comp,X_comp,pow_succ,map_mul,mul_assoc]
  calc
    _ = (∏ i ∈ range b, (1 - C (h^(i+1))*X))*(1-X) := by
      simp only [block,Polynomial.prod_comp,each]
    _ = block h (b+1) := by
      rw [block,prod_range_succ']
      simp
    _ = _ := by rw [block,prod_range_succ]; rfl

/-- The coefficient recurrence clears the possibly noninvertible
denominator and holds even in a ring with zero divisors. -/
theorem recurrence (h : R) (b i : ℕ) :
    (1-h^(i+1))*(block h b).coeff (i+1) =
      (h^b-h^i)*(block h b).coeff i := by
  have co := congrArg (fun f : R[X] => f.coeff (i+1)) (shifted h b)
  simp only [mul_sub,mul_one,←mul_assoc,coeff_sub,coeff_mul_X,coeff_mul_C,comp_C_mul_X_coeff] at co
  linear_combination -co

private theorem deg_one (a : R) : (1-C a*X).natDegree≤1 :=
  (natDegree_sub_le ..).trans (max_le (by simp) ((natDegree_C_mul_le a X).trans natDegree_X_le))

/-- Reversing coefficients produces the monic product actually consumed by
the scalar evaluator, including when h is a zero divisor. -/
theorem root_polynomial (h : R) (b : ℕ) :
    reflect b (block h b) = ∏ i ∈ range b, (X-C (h^i)) := by
  induction b with
  | zero => simp [block]
  | succ b ih =>
    have deg : (block h b).natDegree≤b := calc
      _ ≤ ∑ i ∈ range b, (1-C (h^i)*X).natDegree := natDegree_prod_le ..
      _ ≤ ∑ _i ∈ range b, 1 := sum_le_sum (f:=fun i => (1-C (h^i)*X).natDegree) (fun i _ => deg_one (h^i))
      _ = b := by simp
    rw [show block h (b+1)=block h b*(1-C (h^b)*X) by simp only [block,prod_range_succ],
      reflect_mul _ _ deg (deg_one _),ih,prod_range_succ]
    simp only [sub_eq_add_neg,reflect_add,reflect_neg,reflect_one,pow_one,reflect_C_mul,reflect_one_X,mul_one]

private theorem reflected_comp (h : R) (b : ℕ) :
    (reflect b (block h b)).comp (C (h^(b-1))*X) =
      C ((-1)^b*h^(b.choose 2))*(block h b) := by
  rw [root_polynomial,Polynomial.prod_comp]
  have each (i : ℕ) (hi : i ∈ range b) :
      (X-C (h^i)).comp (C (h^(b-1))*X)=C ((-1)*h^i)*(1-C (h^(b-1-i))*X) := by
    have ex : i+(b-1-i)=b-1 := by have := mem_range.mp hi; omega
    rw [sub_comp,X_comp,C_comp,map_mul,map_neg,map_one]
    have join : C (h^i)*C (h^(b-1-i))= C (h^(b-1)) := by rw [←map_mul,←pow_add,ex]
    linear_combination X*join.symm
  rw [prod_congr rfl each,prod_mul_distrib,←map_prod,prod_mul_distrib,prod_const,card_range,
    prod_pow_eq_pow_sum,sum_range_id,←Nat.choose_two_right]
  congr 1
  exact prod_range_reflect (fun i => (1-C (h^i)*X)) b

/-- The upper half needs no additional inversions. The exponent is
nonnegative under the stated bound on i. -/
theorem mirror {h : R} (unit : IsUnit h) {b i : ℕ} (low : 2*i≤b) :
    (block h b).coeff (b-i)=
      (-1)^b*h^((b-1)*(b-2*i)/2)*(block h b).coeff i := by
  have co := congrArg (fun p : R[X] => p.coeff i) (reflected_comp h b)
  simp only [comp_C_mul_X_coeff,coeff_reflect,revAt_le (show i≤b by omega),coeff_C_mul] at co
  have split : b*(b-1)=(b-1)*(b-2*i)+2*((b-1)*i) := by
    have e : b-2*i+2*i=b := by omega
    calc
      _ = (b-1)*(b-2*i+2*i) := by rw [e,mul_comm]
      _ = _ := by ring
  have ex : b.choose 2 = (b-1)*(b-2*i)/2 + (b-1)*i := by
    rw [Nat.choose_two_right,split,Nat.add_mul_div_left _ _ (by decide)]
  apply (unit.pow ((b-1)*i)).mul_right_cancel
  rw [← pow_mul,ex,pow_add] at co
  calc
    _ = _ := co
    _ = _ := by ring

end PrimeFactors.ReflectedGeometricBlocks
