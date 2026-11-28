import PrimeFactors.DyadicFactorClueGain
import PrimeFactors.TrueTraceTableCost
import PrimeFactors.FullWidthQuarticLaterMidpoint

/-! Two existing full-width controls with the same supplied bit budget.
The reference factors verify both the supplied label and the reported residue. -/
namespace PrimeFactors.DyadicClueControls

open DyadicFactorClueGain FactorClueSumPrecision

/-- Numerical certificate for the pair and its supplied low k factor bits. -/
structure Reading (N p q k a gain residue : ℕ) : Prop where
  product : p*q=N
  supplied : p%2^k=a
  modulus : greatest N a (2^k)=2^(k+gain)
  extra_bits : extra k a N=gain
  true_sum : (p+q)%2^(k+gain)=residue
  unique_sum (s : ℕ) : a*s ≡ a^2+N [MOD 2^(k+gain)] ↔ s ≡ residue [MOD 2^(k+gain)]

private theorem check {N p q k a gain residue : ℕ} (hk : 1≤k)
    (prod : p*q=N) (clue : p%2^k=a) (odd : Odd a) (cap : gain≤k+1)
    (hit : N ≡ a^2+a*2^k [MOD 2^gain])
    (miss : ¬ N ≡ a^2+a*2^k [MOD 2^(gain+1)])
    (trueSum : (p+q)%2^(k+gain)=residue)
    (equation : a*residue ≡ a^2+N [MOD 2^(k+gain)]) : Reading N p q k a gain residue := by
  have lower := (extra_iff hk a N gain).mpr ⟨cap,hit⟩
  have upper : ¬gain+1≤extra k a N := fun h => miss ((extra_iff hk a N _).mp h).2
  have exactGain : extra k a N=gain := by omega
  refine ⟨prod,clue,by rw [greatest_eq hk,exactGain],exactGain,trueSum,?_⟩
  intro s
  constructor
  · intro hs
    exact Nat.ModEq.cancel_left_of_coprime (((Nat.coprime_two_right.mpr odd).pow_right _).symm) (hs.trans equation.symm)
  · intro hs
    exact (hs.mul_left a).trans equation

/-- The independent fresh control gains one bit from the supplied 160-bit class. -/
theorem fresh : Reading ChebyshevQuarticScale.fresh TrueTraceTableCost.freshP TrueTraceTableCost.freshQ
    160 347304353813149557101162729845850277667140887327 1
    1513878057010853217856674867035423563804221996176 := by
  apply check
  · decide
  · exact TrueTraceTableCost.fresh_price.1
  all_goals first | exact Nat.odd_iff.mpr (by decide +kernel) | decide +kernel

/-- The constructed quartic has a supplied class of one. It determines the
sum residue two modulo 2^320. -/
theorem quartic : Reading FullWidthQuarticLaterMidpoint.N FullWidthQuarticLaterMidpoint.p
    FullWidthQuarticLaterMidpoint.q 160 1 160 2 := by
  apply check
  all_goals first | exact Nat.odd_iff.mpr (by decide +kernel) | decide +kernel

/-- At fixed factor 71 and k=3, a gap of 8 gives four extra bits. A gap of
32 gives three. All three primes have seven bits. -/
theorem gap_control : Nat.Prime 71 ∧ Nat.Prime 79 ∧ Nat.Prime 103 ∧ 71%8=7 ∧
    79-71=8 ∧ 103-71=32 ∧ extra 3 7 (71*79)=4 ∧ extra 3 7 (71*103)=3 := by
  norm_num [extra,greatest,cap,Nat.log]

end PrimeFactors.DyadicClueControls
