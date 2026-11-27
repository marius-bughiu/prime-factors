import PrimeFactors.FareyParentSufficient
import PrimeFactors.FareyParentNecessary

/-! The exact one-sided continued-fraction threshold for a positive candidate E/F above E/N.
The test uses the candidate F. It does not supply a value of F from N. -/
namespace PrimeFactors.FareyParentCriterion

/-- A fraction in lowest terms and its explicit left parent give a strict integer test.
At equality the input is the mediant and its canonical expansion omits the candidate. -/
theorem explicit_iff {N E F a b c d : ℕ} (ep : 0<E) (fp : 0<F) (fn : F<N)
    (bp : 0<b) (db : d≤b) (fraction : a*F=E*b) (parent : a*d=b*c+1) :
    (∃ i, (E:ℚ)/F=((E:ℝ)/N).convergent i) ↔ (a*(N-F))*(b+d)<N :=
  ⟨FareyParentNecessary.necessary ep fp fn bp db fraction parent,
   FareyParentSufficient.sufficient ep fp fn bp db fraction parent⟩

/-- Compute both the reduced ratio and its left parent's denominator from the specified E,F.
For an integer ratio the denominator is one, including the target 1/1. -/
theorem criterion {E F N : ℕ} (ep : 0<E) (fp : 0<F) (fn : F<N) :
    let g := E.gcd F
    let a := E/g
    let b := F/g
    (∃ i, (E:ℚ)/F=((E:ℝ)/N).convergent i) ↔
      (a*(N-F))*(b+FareyParentSufficient.parentDen a b)<N := by
  let g := E.gcd F
  let a := E/g
  let b := F/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left F ep
  have eg : a*g=E := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have fg : b*g=F := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  have ap : 0<a := Nat.div_pos (Nat.le_of_dvd ep (Nat.gcd_dvd_left ..)) gp
  have bp : 0<b := Nat.div_pos (Nat.le_of_dvd fp (Nat.gcd_dvd_right ..)) gp
  have eq : a*F=E*b := by rw [←eg,←fg]; ring
  have parent := FareyParentSufficient.parent_spec ap bp (Nat.coprime_div_gcd_div_gcd gp)
  exact explicit_iff ep fp fn bp parent.2.1 eq parent.2.2

/-- With target 2/3 and left parent 1/2, the canonical expansion excludes
the mediant 3/5 itself. The examples on either side test the strict boundary. -/
theorem boundary_examples :
    (¬ ∃ i, (4:ℚ)/6=((4:ℝ)/7).convergent i) ∧
    (¬ ∃ i, (6:ℚ)/9=((6:ℝ)/10).convergent i) ∧
    (∃ i, (14:ℚ)/21=((14:ℝ)/23).convergent i) := by
  have test {E F N : ℕ} (ep : 0<E) (fp : 0<F) (fn : F<N) (eq : 2*F=E*3) :=
    explicit_iff (a:=2) (b:=3) (c:=1) (d:=2) ep fp fn (by decide) (by decide) eq (by decide)
  have below := test (E:=4) (F:=6) (N:=7) (by decide) (by decide) (by decide) (by decide)
  have edge := test (E:=6) (F:=9) (N:=10) (by decide) (by decide) (by decide) (by decide)
  have above := test (E:=14) (F:=21) (N:=23) (by decide) (by decide) (by decide) (by decide)
  exact ⟨fun h => (by decide : ¬2*(7-6)*(3+2)<7) (below.mp h),
    fun h => (by decide : ¬2*(10-9)*(3+2)<10) (edge.mp h), above.mpr (by decide)⟩

end PrimeFactors.FareyParentCriterion
