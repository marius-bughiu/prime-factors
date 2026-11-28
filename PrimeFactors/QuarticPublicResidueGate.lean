import PrimeFactors.ProductSelectedQuarticDenominators
import PrimeFactors.QuarticLocalClassification

/-! Discarding impossible quartic inputs using their last four bits. -/
namespace PrimeFactors.QuarticPublicResidueGate

open MixedPrefixSample (eligible)
open ComplementaryQuarticProducts (choices)
open QuarticLocalClassification (Tests)
open ScaledQuarticReadings (run)
open scoped Classical
attribute [local irreducible] eligible

abbrev Allowed (n : ℕ) : Prop := n%16=1 ∨ n%16=5

def denominators (n : ℕ) : List ℕ :=
  if Allowed n then ProductSelectedQuarticDenominators.denominators n else []

def recover (n : ℕ) := run n (denominators n)

theorem of_point {n a b d : ℕ} (dp : 0<d) (prim : a.Coprime b)
    (point : d^4*n=a^4+4*b^4) : Tests n := by
  intro m _
  refine ⟨a,b,d,dp,?_,?_⟩
  · intro p prime _
    by_cases dvd : p∣a
    · exact Or.inr (fun bd => (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,prime,dvd,bd⟩) prim)
    · exact Or.inl dvd
  · rw [←point,Nat.mul_comm (d^4)]

theorem of_reading {p q d : ℕ} (mem : (p,q)∈eligible) (dp : 0<d)
    (hit : (choices (d^4*(p*q))).Nonempty) : Tests (p*q) := by
  obtain ⟨_,ord,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp mem
  have sf := (Nat.squarefree_mul ((Nat.coprime_primes pp qp).mpr ord.ne)).mpr ⟨pp.squarefree,qp.squarefree⟩
  obtain ⟨_,_,pos,_,_,_,_,_,cop,form,_⟩ := ReduceQuarticDenominator.primitive_choice dp sf hit
  exact of_point pos cop form

open private PrimeFactors.QuarticPrimePopulation.eligible_bounds from PrimeFactors.QuarticPrimePopulation

theorem allowed_of_reading {p q d : ℕ} (mem : (p,q)∈eligible) (dp : 0<d)
    (hit : (choices (d^4*(p*q))).Nonempty) : Allowed (p*q) :=
  ((QuarticLocalClassification.all_iff (PrimeFactors.QuarticPrimePopulation.eligible_bounds mem).2.2).mp
    (of_reading mem dp hit)).1

theorem reference {p q : ℕ} (mem : (p,q)∈eligible) :
    run (p*q) (List.range' 1 2048)=recover (p*q) := by
  by_cases good : Allowed (p*q)
  · simpa only [recover,denominators,if_pos good,ProductSelectedQuarticDenominators.recover] using
      ProductSelectedQuarticDenominators.reference mem
  · rw [ThreeQuarticDenominators.identical mem,ThreeQuarticDenominators.recover,
      ScaledQuarticReadings.run_eq mem [1,725,1517] (by simp)]
    have empty : ¬∃ d∈([1,725,1517]:List ℕ),(choices (d^4*(p*q))).Nonempty := by
      rintro ⟨d,hd,hit⟩
      have three : d=1 ∨ d=725 ∨ d=1517 := by simpa using hd
      have pos : 0<d := by omega
      exact good (allowed_of_reading mem pos hit)
    simp only [if_neg empty,recover,denominators,if_neg good,run,List.findSome?_nil]

end PrimeFactors.QuarticPublicResidueGate
