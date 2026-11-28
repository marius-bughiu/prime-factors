import PrimeFactors.PrimeSumPolynomialExtremum
import PrimeFactors.PrimeSumPolynomialStars

/-! A sharp degree-two relation on ten small semiprimes. -/
namespace PrimeFactors.PrimeSumPolynomialExamples

open Finset MvPolynomial PrimeSumPolynomialGrid PrimeSumPolynomialStars
open scoped Classical

noncomputable def pool : Finset ℚ := {3,5,7,11,13}
noncomputable def selected : Finset ℚ := {3,5}

/-- No quadratic relation covers more than seven of the ten unordered
distinct pairs. The grid counts both orders of every covered pair. -/
theorem quadratic_bound (F : MvPolynomial (Fin 2) ℚ) (nz : F≠0) (deg : F.totalDegree≤2) :
    ((hits pool F).filter (fun z => z.1≠z.2)).card ≤ 14 := by
  have size : pool.card=5 := by decide
  have cap : F.totalDegree≤pool.card-1 := by omega
  have bound : F.totalDegree*(pool.card-1)+(pool.card-F.totalDegree)*F.totalDegree≤14 := by
    rw [size]
    interval_cases d : F.totalDegree <;> decide
  have counted := PrimeSumPolynomialExtremum.distinct_grid pool F nz cap
  have same : ((hits pool F).filter (fun z => z.1≠z.2)).card ≤
      F.totalDegree*(pool.card-1)+(pool.card-F.totalDegree)*F.totalDegree := by
    convert counted using 1
    apply congrArg Finset.card
    ext z
    simp only [mem_filter]
  exact same.trans bound

/-- The construction attains seven distinct products. It covers 55 and
misses 143 because its two linear factors explicitly select 3 and 5. -/
theorem attained :
    (stars selected).totalDegree=2 ∧
    ((pool.powersetCard 2).filter (fun pair => (pair∩selected).Nonempty)).card=7 ∧
    eval ![(55:ℚ),16] (stars selected)=0 ∧ eval ![(143:ℚ),24] (stars selected)≠0 := by
  have a := eval_zero selected 5 11
  have b := eval_zero selected 11 13
  rw [(degrees selected).2]
  refine ⟨by decide,by decide,?_,?_⟩
  · norm_num at a
    exact a.mpr (by decide)
  · norm_num at b
    exact fun z => (by decide : ¬((11:ℚ)∈selected ∨ (13:ℚ)∈selected)) (b.mp z)

end PrimeFactors.PrimeSumPolynomialExamples
