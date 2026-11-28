import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.Ring

/-! Exact gcd readings along a progression selected by the two covering
congruences. When the central product is a unit of the wheel, the entire
sequence can be calculated from the signed index alone. -/

namespace PrimeFactors.FractionalWheelTranscript

private theorem gcd_congr {x y : ℤ} {w : ℕ} (congruent : x ≡ y [ZMOD (w : ℤ)]) :
    x.gcd w = y.gcd w := by
  have divides {a b : ℤ} (h : a ≡ b [ZMOD (w : ℤ)]) : a.gcd w ∣ b.gcd w := by
    have dw : ((a.gcd w : ℕ) : ℤ) ∣ w := Int.gcd_dvd_right
    have dx : ((a.gcd w : ℕ) : ℤ) ∣ a := Int.gcd_dvd_left
    have dy : ((a.gcd w : ℕ) : ℤ) ∣ b := by
      have d := Int.dvd_add dx (dw.trans h.dvd)
      simpa only [add_sub_cancel] using d
    exact Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd dy dw)
  exact Nat.dvd_antisymm (divides congruent) (divides congruent.symm)

private theorem cancel {a w : ℕ} (unit : a.Coprime w) (j : ℤ) :
    ((a : ℤ)*j).gcd w = j.natAbs.gcd w := by
  simpa only [Int.gcd_def, Int.natAbs_mul, Int.natAbs_natCast] using
    (Nat.Coprime.gcd_mul_left_cancel j.natAbs unit)

/-- Whenever the step is a known multiple of the central unit modulo the
wheel, every signed reading reduces to a single input-independent table. -/
theorem scaled_gcd {n m w c : ℕ} (unit : n.Coprime w)
    (phase : m ≡ c*n [MOD w]) (j : ℤ) :
    ((n : ℤ)+j*m).gcd w = (1+j*c).natAbs.gcd w := by
  have coePhase : (m : ℤ) ≡ (c : ℤ)*n [ZMOD (w : ℤ)] := by
    exact_mod_cast Int.natCast_modEq_iff.mpr phase
  have same : (n : ℤ)+j*m ≡ n*(1+j*c) [ZMOD (w : ℤ)] := calc
    _ ≡ n+j*((c : ℤ)*n) [ZMOD (w : ℤ)] := (coePhase.mul_left j).add_left _
    _ = _ := by ring
  exact (gcd_congr same).trans (cancel unit _)

/-- At every signed index, including indices outside the balanced interval,
the complete gcd equals two gcds involving just the index and wheel. -/
theorem exact_gcd {n m P r : ℕ} (disjoint : P.Coprime r) (unit : n.Coprime (P*r))
    (wheel : m ≡ n [MOD P]) (extra : 2*m ≡ n [MOD r]) (j : ℤ) :
    ((n : ℤ)+j*m).gcd (P*r : ℕ) = (j+1).natAbs.gcd P * (j+2).natAbs.gcd r := by
  obtain ⟨leftUnit, rightUnit⟩ := Nat.coprime_mul_iff_right.mp unit
  have both : (2*m).Coprime r := extra.gcd_eq.trans rightUnit
  have mUnit := (Nat.coprime_mul_iff_left.mp both).2
  have a : (m : ℤ) ≡ n [ZMOD (P : ℤ)] := Int.natCast_modEq_iff.mpr wheel
  have b : 2*(m : ℤ) ≡ n [ZMOD (r : ℤ)] := by exact_mod_cast Int.natCast_modEq_iff.mpr extra
  have left : (n : ℤ)+j*m ≡ n*(j+1) [ZMOD (P : ℤ)] := calc
    _ ≡ n+j*n [ZMOD (P : ℤ)] := (a.mul_left j).add_left _
    _ = _ := by ring
  have right : (n : ℤ)+j*m ≡ m*(j+2) [ZMOD (r : ℤ)] := calc
    _ ≡ 2*m+j*m [ZMOD (r : ℤ)] := b.symm.add_right _
    _ = _ := by ring
  change ((n : ℤ)+j*m).natAbs.gcd (P*r) = _
  rw [Nat.Coprime.gcd_mul _ disjoint]
  exact congrArg₂ (·*·) ((gcd_congr left).trans (cancel leftUnit _))
    ((gcd_congr right).trans (cancel mUnit _))

end PrimeFactors.FractionalWheelTranscript
