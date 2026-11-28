import PrimeFactors.FactorEndingDecoder
import PrimeFactors.ObservableSeparationDepth
import PrimeFactors.DyadicClueControls

/-! Full-size controls for decoding factor endings with a supplied true
sum suffix. The known primes supply and independently validate the clue. -/
namespace PrimeFactors.FactorEndingDecoderControls

open FactorEndingDecoder ObservableSeparationDepth

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 4096

private theorem fresh_gate {e : ℕ} {s : ℤ} (lo : 2≤e)
    (sum : s ≡ (TrueTraceTableCost.freshP:ℤ)+TrueTraceTableCost.freshQ [ZMOD (2:ℤ)^e]) :
    ready ChebyshevQuarticScale.fresh s 160 e=true ↔ 161≤e := by
  let p : ℤ := TrueTraceTableCost.freshP
  let q : ℤ := TrueTraceTableCost.freshQ
  have eq : (ChebyshevQuarticScale.fresh:ℤ)=p*q := by
    dsimp [p,q]
    exact_mod_cast DyadicClueControls.fresh.product.symm
  rw [eq]
  exact ready_iff_depth (g:=(q-p)/2) (t:=1) lo
    (Int.odd_iff.mpr (by decide +kernel)) (Int.odd_iff.mpr (by decide +kernel))
    sum (by decide +kernel) (Int.odd_iff.mpr (by decide +kernel))

/-- The independently generated comparison needs 161 supplied sum bits
for the unordered 160-bit factor endings. Dropping the last bit loses
identifiability among the compatible modular factor pairs. -/
theorem fresh :
    let p := TrueTraceTableCost.freshP
    let q := TrueTraceTableCost.freshQ
    let n : ℤ := ChebyshevQuarticScale.fresh
    let s : ℤ := 1513878057010853217856674867035423563804221996176
    p*q=ChebyshevQuarticScale.fresh ∧ ((p+q:ℕ):ℤ)%(2^161)=s ∧
    readEndings n (s%2^160) 160 160=none ∧
    readEndings n s 160 161=some (1166573703197703660755512137189573286137081108849,
      347304353813149557101162729845850277667140887327) ∧
    (q:ℤ)%2^160=1166573703197703660755512137189573286137081108849 ∧
    (p:ℤ)%2^160=347304353813149557101162729845850277667140887327 := by
  dsimp only
  refine ⟨DyadicClueControls.fresh.product,by decide +kernel,?_,?_,by decide +kernel,by decide +kernel⟩
  · have miss := (fresh_gate (e:=160) (s:=1513878057010853217856674867035423563804221996176%2^160)
        (by decide) (by decide +kernel)).not.mpr (by decide)
    simp only [readEndings,if_neg miss]
  · have hit := (fresh_gate (e:=161) (s:=1513878057010853217856674867035423563804221996176)
        (by decide) (by decide +kernel)).mpr (by decide)
    simp only [readEndings,hit,if_true,Option.some.injEq]
    decide +kernel

/-- On the constructed quartic control both 160-bit endings are 1. The
same supplied numerical remainder 2 becomes sufficient at width 319. -/
theorem quartic :
    let p := FullWidthQuarticLaterMidpoint.p
    let q := FullWidthQuarticLaterMidpoint.q
    let n : ℤ := FullWidthQuarticLaterMidpoint.N
    p*q=FullWidthQuarticLaterMidpoint.N ∧ ((p+q:ℕ):ℤ)%(2^319)=2 ∧
    readEndings n 2 160 318=none ∧ readEndings n 2 160 319=some (1,1) ∧
    (p:ℤ)%2^160=1 ∧ (q:ℤ)%2^160=1 := by
  dsimp only
  exact ⟨DyadicClueControls.quartic.product,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,by decide +kernel⟩

end PrimeFactors.FactorEndingDecoderControls
