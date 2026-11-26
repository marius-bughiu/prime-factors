import PrimeFactors.QuarticSquareRemainder
import PrimeFactors.SquareRootFormulaPopulation
import PrimeFactors.VariableBlockProbe

/-! Two public gcd tests using the product and its integer square root,
including finite population bounds and complete small benchmark readings. -/
namespace PrimeFactors.SquareRootFormulaExamples

open Polynomial SquareRootPolynomialFormula

private noncomputable def remainder : Formula := X - C X^2

/-- Width twice the square-root remainder plus three, used in the normalized probe. -/
noncomputable def remainderWidth : Formula :=
  let t : Formula := C X
  let m := 2*remainder+3
  48*t^4-24*(1+m^2)*t^2+(m^2-1)^3

/-- The nontrivial reciprocal factor at width equal to the square-root center. -/
noncomputable def reciprocal : Formula := remainder^2-22*remainder+1

theorem remainder_reading (n : ℕ) (t : ℤ) :
    value remainderWidth n t = BlockSubresultantProbe.probe (2*((n:ℤ)-t^2)+3) t := by
  simp [remainderWidth,remainder,value,BlockSubresultantProbe.probe]

theorem reciprocal_reading (n : ℕ) (t : ℤ) :
    value reciprocal n t = ((n:ℤ)-t^2)^2-22*((n:ℤ)-t^2)+1 := by
  simp [reciprocal,remainder,value]

theorem remainder_specialized : specialized remainderWidth =
    64*X^12-576*X^10+2112*X^8-4128*X^6+4560*X^4-2544*X^2+512 := by
  simp only [specialized,coeff_zero_eq_eval_zero,remainderWidth,remainder,
    eval_sub,eval_mul,eval_X,eval_C,eval_add,eval_pow,eval_ofNat,eval_one]
  ring

theorem reciprocal_specialized : specialized reciprocal = X^4+22*X^2+1 := by
  simp only [specialized,coeff_zero_eq_eval_zero,reciprocal,remainder,
    eval_sub,eval_mul,eval_X,eval_C,eval_add,eval_pow,eval_ofNat,eval_one]
  ring

theorem remainder_degree : (specialized remainderWidth).natDegree = 12 := by
  rw [remainder_specialized]
  compute_degree!

theorem reciprocal_degree : (specialized reciprocal).natDegree = 4 := by
  rw [reciprocal_specialized]
  compute_degree!

theorem remainder_const : (specialized remainderWidth).coeff 0=512 := by
  rw [remainder_specialized,coeff_zero_eq_eval_zero]
  simp

theorem reciprocal_const : (specialized reciprocal).coeff 0=1 := by
  rw [reciprocal_specialized,coeff_zero_eq_eval_zero]
  simp

open SquareRootFormulaPopulation
set_option exponentiation.threshold 4096
attribute [local irreducible] MixedPrefixSample.eligible MixedPrefixSample.primes

private theorem no_exceptions {P : ℤ[X]} (nz : P.coeff 0 ≠ 0) (h : (P.coeff 0).natAbs < 1024) :
    (exceptions P.content).card = 0 := by
  obtain ⟨nonzero,size⟩ := content_bound P 0 nz
  have budget := exception_bits (L:=10) nonzero (size.trans_lt h)
  omega

/-- The admissible population consists of distinct, unordered 1024-bit prime
pairs whose product has 2048 bits. Hits on either prime are counted. -/
theorem remainder_population : 2^1003*(splits remainderWidth).card < MixedPrefixSample.eligible.card := by
  apply dyadic_bound remainderWidth (D:=12) (E:=0) remainder_degree.le
  · exact (no_exceptions (by rw [remainder_const]; decide) (by rw [remainder_const]; decide)).le
  · decide
  · rw [MixedPrefixSample.X]
    decide +kernel

theorem reciprocal_population : 2^1004*(splits reciprocal).card < MixedPrefixSample.eligible.card := by
  apply dyadic_bound reciprocal (D:=4) (E:=0) reciprocal_degree.le
  · exact (no_exceptions (by rw [reciprocal_const]; decide) (by rw [reciprocal_const]; decide)).le
  · decide
  · rw [MixedPrefixSample.X]
    decide +kernel

/-- The seven reported gcds in benchmark order. A selected width of three
reuses the already evaluated fixed-width gcd in the implementation. -/
noncomputable def seven (n : ℕ) (t selected : ℤ) : List ℕ :=
  let r := (n:ℤ)-t^2
  let probe := BlockSubresultantProbe.probe
  [Int.gcd (BlockSubresultantProbe.nine t) n, Int.gcd (t-5) n, Int.gcd (probe 3 t) n,
   Int.gcd (r^2-22*r+1) n, Int.gcd (probe (2*r+3) t) n, Int.gcd (t^2-1) n,
   Int.gcd (probe selected t) n]

/-- These public signs give the selected widths used in the two receipts. -/
theorem selected_widths :
    jacobiSym (VariableBlockProbe.discriminant (3:ℤ)) 156263=1 ∧
    jacobiSym (VariableBlockProbe.discriminant (5:ℤ)) 156263=1 ∧
    jacobiSym (VariableBlockProbe.discriminant (7:ℤ)) 156263= -1 ∧
    jacobiSym (VariableBlockProbe.discriminant (3:ℤ)) 34756699= -1 := by
  norm_num [VariableBlockProbe.discriminant]

theorem reciprocal_example :
    let n : ℕ := 156263
    n.sqrt = 395 ∧ n-n.sqrt^2 = 238 ∧ seven n n.sqrt 7 = [1,1,1,509,1,1,1] ∧
    Nat.Prime 307 ∧ Nat.Prime 509 ∧ 307*509=n := by
  have root : (156263:ℕ).sqrt=395 := Nat.eq_of_le_of_lt_succ
    (Nat.le_sqrt'.mpr (by decide)) (Nat.sqrt_lt'.mpr (by decide))
  simp only [root]
  decide +kernel

theorem remainder_example :
    let n : ℕ := 34756699
    n.sqrt = 5895 ∧ n-n.sqrt^2 = 5674 ∧ seven n n.sqrt 3 = [1,1,1,1,4483,1,1] ∧
    Nat.Prime 4483 ∧ Nat.Prime 7753 ∧ 4483*7753=n := by
  have root : (34756699:ℕ).sqrt=5895 := Nat.eq_of_le_of_lt_succ
    (Nat.le_sqrt'.mpr (by decide)) (Nat.sqrt_lt'.mpr (by decide))
  simp only [root]
  refine ⟨True.intro,by decide +kernel,by decide +kernel,?_,?_,by decide +kernel⟩ <;> norm_num1

end PrimeFactors.SquareRootFormulaExamples
