import PrimeFactors.DyadicSumPeak
import PrimeFactors.FactorEndingDecoder
import PrimeFactors.TwoMaximalClueSuffixes
import PrimeFactors.FactorClueWidthProfile

/-! Two product-only sum predictions at odd precision. The shifted square
root fixes both guesses. Their success at a specified width is precisely
one value of the true gap's two-adic order. -/
namespace PrimeFactors.OddWidthSumPredictions

open private PrimeFactors.FactorPairSeparationDepth.nondiv from PrimeFactors.FactorPairSeparationDepth
open private PrimeFactors.FactorEndingDecoder.unit_spec from PrimeFactors.FactorEndingDecoder
open private PrimeFactors.TwoMaximalClueSuffixes.root_signs from PrimeFactors.TwoMaximalClueSuffixes
open private PrimeFactors.LocalMidpointLanes.odd_square from PrimeFactors.LocalMidpointLanes

/-- Width 2j+3, with j≥2. Each sign supplies one predicted sum remainder. -/
def root (N : ℤ) (j : ℕ) : ℤ :=
  FactorEndingDecoder.unitRoot ((N+2^(2*j))%(2:ℤ)^(2*j+3)) (2*j)

def predicts (N s : ℤ) (j : ℕ) : Prop :=
  s ≡ 2*root N j [ZMOD (2:ℤ)^(2*j+3)] ∨ s ≡ -(2*root N j) [ZMOD (2:ℤ)^(2*j+3)]

theorem root_spec {N : ℤ} {j : ℕ} (hj : 2≤j) (one : N ≡ 1 [ZMOD 8]) :
    Odd (root N j) ∧ (root N j)^2 ≡ N+2^(2*j) [ZMOD (2:ℤ)^(2*j+3)] := by
  let D := N+2^(2*j)
  let M : ℤ := 2^(2*j+3)
  have small : D ≡ 1 [ZMOD 8] := by
    have z : (2:ℤ)^(2*j) ≡ 0 [ZMOD 8] := Int.modEq_zero_iff_dvd.mpr
      (pow_dvd_pow (2:ℤ) (by omega : 3≤2*j))
    simpa [D] using one.add z
  have rem := Int.mod_modEq D M
  have low := rem.of_dvd (pow_dvd_pow (2:ℤ) (by omega : 3≤2*j+3))
  have base : (8:ℤ) ∣ D%M-1 := Int.modEq_iff_dvd.mp (low.trans small).symm
  have spec := PrimeFactors.FactorEndingDecoder.unit_spec base (2*j)
  exact ⟨spec.1,(Int.modEq_iff_dvd.mpr spec.2).trans rem⟩

private theorem twice_iff {h r : ℤ} {j : ℕ} :
    2*h ≡ 2*r [ZMOD (2:ℤ)^(j+1)] ↔ h ≡ r [ZMOD (2:ℤ)^j] := by
  rw [Int.modEq_iff_dvd,Int.modEq_iff_dvd,pow_succ,mul_comm ((2:ℤ)^j),←mul_sub]
  exact (mul_dvd_mul_iff_left (by decide : (2:ℤ)≠0))

theorem midpoint_iff {N h : ℤ} {j : ℕ} (hj : 2≤j) (one : N ≡ 1 [ZMOD 8]) :
    predicts N (2*h) j ↔ h^2 ≡ N+2^(2*j) [ZMOD (2:ℤ)^(2*j+3)] := by
  obtain ⟨odd,sq⟩ := root_spec hj one
  unfold predicts
  rw [←mul_neg,twice_iff,twice_iff,←PrimeFactors.TwoMaximalClueSuffixes.root_signs
    (by omega : 1≤2*j+2) h _ odd]
  exact ⟨fun l => l.trans sq,fun r => r.trans sq.symm⟩

/-- At odd precision these are exactly the highest-multiplicity even
sum guesses, counting all ordered modular presentations of the product. -/
theorem winning_iff {N j : ℕ} (hj : 2≤j) (good : N%8=1) (h : ℤ) :
    PrimeSquareSumWeights.weight (m:=2^(2*j+3)) N ((2*h:ℤ):ZMod _) = 2^(j+2) ↔
      predicts N (2*h) j := by
  have one : (N:ℤ) ≡ 1 [ZMOD 8] := by
    exact_mod_cast Int.natCast_modEq_iff.mpr (show N ≡ 1 [MOD 8] from good)
  rw [midpoint_iff hj one,Int.cast_mul,Int.cast_ofNat,DyadicSumPeak.odd_midpoint_iff]
  have cast := ZMod.intCast_eq_intCast_iff (h^2) ((N:ℤ)+2^(2*j)) (2^(2*j+3))
  push_cast at cast ⊢
  exact cast

private theorem square_order (j : ℕ) (d : ℤ) :
    d^2 ≡ 2^(2*j) [ZMOD (2:ℤ)^(2*j+3)] ↔ ∃ z : ℤ, Odd z ∧ d=2^j*z := by
  let B : ℤ := 2^j
  have power : (2:ℤ)^(2*j)=B^2 := by dsimp [B]; rw [←pow_mul,Nat.mul_comm]
  rw [pow_add,power]
  constructor
  · intro test
    have short := test.of_dvd (dvd_mul_right (B^2) ((2:ℤ)^3))
    have dv : B^2 ∣ d^2 := Int.modEq_zero_iff_dvd.mp (short.trans (Int.modEq_zero_iff_dvd.mpr (dvd_refl _)))
    obtain ⟨z,hz⟩ := (Int.pow_dvd_pow_iff (by decide : 2≠0)).mp dv
    refine ⟨z,?_,hz⟩
    obtain ⟨v,hv⟩ := Int.modEq_iff_dvd.mp test
    have nz : B^2 ≠ 0 := by dsimp [B]; positivity
    have eq : 1-z^2=8*v := mul_left_cancel₀ nz (show B^2*(1-z^2)=B^2*(8*v) by
      rw [hz] at hv; linear_combination hv)
    rcases Int.even_or_odd z with ⟨c,hc⟩|o
    · have bad : 4*(2*v+c^2)=1 := by rw [hc] at eq; linear_combination -eq
      omega
    · exact o
  · rintro ⟨z,odd,hz⟩
    obtain ⟨v,hv⟩ := PrimeFactors.LocalMidpointLanes.odd_square odd
    exact Int.modEq_iff_dvd.mpr ⟨-v,by rw [hz]; dsimp [B]; linear_combination -(2:ℤ)^(2*j)*hv⟩

/-- Either predicted sum is correct exactly when the factors differ by
2^(j+1) times an odd integer. The numerical predictions use no factor clue. -/
theorem true_iff {p q : ℤ} {j : ℕ} (hj : 2≤j) (op : Odd p) (oq : Odd q)
    (one : p*q ≡ 1 [ZMOD 8]) :
    predicts (p*q) (p+q) j ↔ ∃ z : ℤ, Odd z ∧ q-p=2^(j+1)*z := by
  obtain ⟨a,ha⟩ := op
  obtain ⟨b,hb⟩ := oq
  let h := a+b+1
  let d := b-a
  have hs : p+q=2*h := by dsimp [h]; omega
  have ds : h^2=p*q+d^2 := by dsimp [d,h]; rw [ha,hb]; ring
  have cancel {A B m c : ℤ} : (c+A ≡ c+B [ZMOD m]) ↔ A ≡ B [ZMOD m] :=
    ⟨Int.ModEq.add_left_cancel' c,fun v => v.add_left c⟩
  rw [hs,midpoint_iff hj one,ds,cancel,square_order]
  have gap : q-p=2*d := by dsimp [d]; omega
  simp only [gap,pow_succ,mul_comm ((2:ℤ)^j) 2,mul_assoc,mul_right_inj' (by decide : (2:ℤ)≠0)]

/-- Even when the winning sum prediction is correct, it determines
exactly (e+1)/2 low bits of both factors. At the next factor width
there is a compatible modular pair with different endings. -/
theorem ending_width {p q : ℤ} {j k : ℕ} (hj : 2≤j) (hk : 3≤k)
    (op : Odd p) (oq : Odd q) (one : p*q ≡ 1 [ZMOD 8])
    (hit : predicts (p*q) (p+q) j) :
    FactorPairSeparationDepth.Determines p q k (2*j+3) ↔ k≤j+2 := by
  obtain ⟨z,oz,gap⟩ := (true_iff hj op oq one).mp hit
  rw [FactorPairSeparationDepth.determines_iff hk gap oz]
  unfold FactorPairSeparationDepth.depth
  split_ifs <;> omega

/-- Correct predictions at distinct odd widths are mutually exclusive. -/
theorem disjoint_widths {p q : ℤ} {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (ne : i ≠ j)
    (op : Odd p) (oq : Odd q) (one : p*q ≡ 1 [ZMOD 8])
    (first : predicts (p*q) (p+q) i) : ¬predicts (p*q) (p+q) j := by
  intro second
  obtain ⟨x,ox,gx⟩ := (true_iff hi op oq one).mp first
  obtain ⟨y,oy,gy⟩ := (true_iff hj op oq one).mp second
  have eq := gx.symm.trans gy
  rcases lt_or_gt_of_ne ne with lt|gt
  · exact PrimeFactors.FactorPairSeparationDepth.nondiv ox (by omega : i+1 < j+1) ⟨y,eq⟩
  · exact PrimeFactors.FactorPairSeparationDepth.nondiv oy (by omega : j+1 < i+1) ⟨x,eq.symm⟩

end PrimeFactors.OddWidthSumPredictions
