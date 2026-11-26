import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Data.Nat.Choose.Lucas

/-!
The low base-`p` digit controls the width of a Hasse derivative in
characteristic `p`. This supplies degree bounds for the polynomial in the
translation parameter of a cubic raised to the half-prime exponent.
-/

namespace PrimeFactors.HasseShiftDegree

open Polynomial

/-- With fewer than `p` possible index increments, a carry in the units
digit annihilates every coefficient beyond the displayed endpoint. -/
theorem degree_from_carry {p : ℕ} [Fact p.Prime] (F : (ZMod p)[X]) (k : ℕ)
    (width : F.natDegree < k + p) :
    (hasseDeriv k F).natDegree ≤ min (F.natDegree - k) (p - 1 - k % p) := by
  refine le_min (natDegree_hasseDeriv_le F k) (natDegree_le_iff_coeff_eq_zero.mpr ?_)
  intro j beyond
  rw [hasseDeriv_coeff]
  by_cases active : j + k ≤ F.natDegree
  · have pp : 0 < p := (Fact.out : p.Prime).pos
    have hm := Nat.mod_lt k pp
    have jw : j < p := by omega
    have carry : p ≤ j + k % p := by omega
    have reduced : (j + k) % p < k % p := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt jw, Nat.mod_eq_sub_mod carry,
        Nat.mod_eq_of_lt (show j + k % p - p < p by omega)]
      omega
    have lucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := j + k) (k := k) (p := p)
    rw [Nat.choose_eq_zero_of_lt reduced, Nat.zero_mul] at lucas
    have vanish := (ZMod.natCast_eq_natCast_iff _ _ _).mpr lucas
    simpa using congrArg (fun z : ZMod p => z * F.coeff (j + k)) vanish
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge active), mul_zero]

/-- The number of possible roots of a nonzero translation polynomial is at
most one third of the field size when the inert prime `q` is the smaller
prime. The natural-degree conclusion also holds for the zero polynomial. -/
theorem degree_small_partner {p q h : ℕ} [Fact p.Prime] (F : (ZMod p)[X])
    (size : F.natDegree ≤ 3 * h) (half : 2 * h + 1 = q) (order : q < p) :
    3 * (hasseDeriv (2 * h) F).natDegree ≤ p := by
  have carry := degree_from_carry F (2 * h) (by omega)
  rw [Nat.mod_eq_of_lt (show 2 * h < p by omega)] at carry
  have a := (le_min_iff.mp carry).1
  have b := (le_min_iff.mp carry).2
  omega

/-- When the other prime is larger but less than twice the field size, at
most two thirds of the field can be roots of a nonzero translation polynomial. -/
theorem degree_large_partner {p q h : ℕ} [Fact p.Prime] (F : (ZMod p)[X])
    (size : F.natDegree ≤ 3 * h) (half : 2 * h + 1 = q) (order : p < q)
    (balanced : q < 2 * p) :
    3 * (hasseDeriv (2 * h) F).natDegree ≤ 2 * p := by
  have carry := degree_from_carry F (2 * h) (by omega)
  rw [Nat.mod_eq_sub_mod (show p ≤ 2 * h by omega),
    Nat.mod_eq_of_lt (show 2 * h - p < p by omega)] at carry
  have a := (le_min_iff.mp carry).1
  have b := (le_min_iff.mp carry).2
  omega

end PrimeFactors.HasseShiftDegree
