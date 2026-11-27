import PrimeFactors.RootableSignSpan
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime

/-! Four products with the same residue and three common square classes realize
all four possible answers for the two remaining small square classes. -/
namespace PrimeFactors.SignAmbiguityExamples

def Compatible (n p q a b c : ℕ) (s t : ℤ) : Prop :=
  n = p*q ∧ p.Prime ∧ q.Prime ∧ 2^13 ≤ p ∧ p < q ∧ q < 2^14 ∧
  2^27 ≤ n ∧ n < 2^28 ∧ n%9240 = 5699 ∧
  (a : ZMod n)^2 = (-11 : ℤ) ∧ (b : ZMod n)^2 = 14 ∧ (c : ZMod n)^2 = 22 ∧
  jacobiSym 3 p = s ∧ jacobiSym 3 q = s ∧ jacobiSym 5 p = t ∧ jacobiSym 5 q = t

/-- The roots in the four receipts belong to their respective moduli. -/
theorem four_patterns :
    Compatible 138051299 9241 14939 54051419 82420615 126927373 1 1 ∧
    Compatible 135205379 8779 15401 72989602 67583407 79330766 (-1) 1 ∧
    Compatible 146626019 11027 13297 111354713 141588576 24560147 1 (-1) ∧
    Compatible 145951499 9067 16097 51014123 8245944 139052369 (-1) (-1) := by
  unfold Compatible
  repeat' apply And.intro
  all_goals first | (solve | norm_num) | decide +kernel

end PrimeFactors.SignAmbiguityExamples
