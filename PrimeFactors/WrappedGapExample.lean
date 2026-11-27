import PrimeFactors.WeightedGlobalTrace
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! Public 21-bit diagnostic for an off-gap hit separated from the ordinary
integer alternate sums by exactly one full order of the base. -/
namespace PrimeFactors.WrappedGapExample

set_option maxRecDepth 8192

/-- The modulus 1092 of the wrapped sum is the actual order of 2 modulo N. -/
theorem order : orderOf (2:ZMod 1784821)=1092 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · change (2:ZMod 1784821)^1092=1
    decide +kernel
  · intro r prime divides
    have divs : r∣2*(2*(3*(7*13))) := divides
    rcases prime.dvd_mul.mp divs with h|h
    · have := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp h
      have : r=2 := this.resolve_left prime.ne_one
      subst r; decide +kernel
    rcases prime.dvd_mul.mp h with h|h
    · have := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp h
      have : r=2 := this.resolve_left prime.ne_one
      subst r; decide +kernel
    rcases prime.dvd_mul.mp h with h|h
    · have := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp h
      have : r=3 := this.resolve_left prime.ne_one
      subst r; decide +kernel
    rcases prime.dvd_mul.mp h with h|h
    · have := (Nat.dvd_prime (by decide : Nat.Prime 7)).mp h
      have : r=7 := this.resolve_left prime.ne_one
      subst r; decide +kernel
    · have := (Nat.dvd_prime (by decide : Nat.Prime 13)).mp h
      have : r=13 := this.resolve_left prime.ne_one
      subst r; decide +kernel

private def two : (ZMod 1784821)ˣ := ⟨2,892411,by decide,by decide⟩

private theorem reduced (e f : ℕ) (same : e%1092=f%1092) : two^e=two^f := by
  apply pow_eq_pow_iff_modEq.mpr
  have ord : orderOf two=1092 := by rw [←orderOf_units]; exact order
  rwa [ord]

/-- X=2^s/2^((h+1)c), Y=2^(he), with the inverse 892411 of 2.
The public example has k=45, y=8962, c=14 and matched gap 3. -/
theorem receipt :
    let X := WeightedGlobalTrace.left two (1784821/2) 14 17924
    let Y := WeightedGlobalTrace.right two (1784821/2) 3
    (X:ZMod 1784821)=1779742 ∧ (Y:ZMod 1784821)=1422528 ∧
      TraceFoldedRight.trace 1 X=319977 ∧ TraceFoldedRight.trace 1 Y=319977 ∧
      Nat.gcd (((Y:ZMod 1784821)^2-1).val) 1784821=1 ∧
      Nat.gcd ((X:ZMod 1784821)-(Y:ZMod 1784821)).val 1784821=1249 ∧
      Nat.gcd 17924 1784821=1 ∧ 1784821=1249*1429 ∧ Nat.Prime 1249 ∧ Nat.Prime 1429 ∧
      ((1249+1429)/2*14+(1429-1249)/2*3=17924+1092) ∧
      (17924:ℤ)^2-(14^2-3^2)*1784821 = -12491751 := by
  let ux : (ZMod 1784821)ˣ := ⟨1779742,325056,by decide,by decide⟩
  let uy : (ZMod 1784821)ˣ := ⟨1422528,682270,by decide,by decide⟩
  have hx : WeightedGlobalTrace.left two (1784821/2) 14 17924=ux := by
    change two^17924/two^12493754=ux
    rw [reduced 17924 452 (by decide),reduced 12493754 182 (by decide)]
    exact Units.ext (by decide +kernel)
  have hy : WeightedGlobalTrace.right two (1784821/2) 3=uy := by
    change two^2677230=uy
    rw [reduced 2677230 738 (by decide)]
    exact Units.ext (by decide +kernel)
  dsimp only
  rw [hx,hy]
  decide +kernel

end PrimeFactors.WrappedGapExample
