import PrimeFactors.PrimitiveParityAverages
import PrimeFactors.PrimitiveEvenMean
import PrimeFactors.Certificate
import Mathlib.Tactic.NormNum.Prime

/-! Decode the genuine finite primitive-even character average. Computing
that average is a separate input requirement. -/
namespace PrimeFactors.PrimitiveParityReadout

open PrimitiveParityAverages PrimitiveEvenMean

theorem reading {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 8<p) (hq : 8<q) :
    average p q true twoPower = ((mean (parameter p q)):ℂ) := by
  rw [twoPower_even hp hq]
  simp [mean,parameter,T]

/-- The real part of the actual character-family average gives both roots. -/
theorem decode {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 8<p) (order : p≤q) :
    let n := (p:ℝ)*q
    let s := sumFromMean n (average p q true twoPower).re
    let d := Real.sqrt (s^2-4*n)
    (s-d)/2=(p:ℝ) ∧ (s+d)/2=(q:ℝ) := by
  rw [reading hp (hp.trans_le order)]
  exact exact_factors (by omega) order

/-- The numerator 102, denominator 50, and final factorization of the worked
example all concern the same even character family. -/
theorem control143 : total 11 13 true (fun _ _ => 1)=50 ∧ total 11 13 true twoPower=102 ∧
    average 11 13 true twoPower=51/25 ∧ ExactFactorization 143 [11,13] := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have size := (sizes (by decide : 2<11) (by decide : 2<13)).1
  norm_num [T] at size
  have avg := twoPower_even (by decide : 8<11) (by decide : 8<13)
  norm_num [T] at avg
  refine ⟨size,?_,avg,by norm_num [ExactFactorization]⟩
  unfold average at avg
  rw [size] at avg
  linear_combination 50*avg

end PrimeFactors.PrimitiveParityReadout
