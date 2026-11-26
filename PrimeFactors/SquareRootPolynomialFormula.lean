import PrimeFactors.SquareRootShiftPartners
import Mathlib.RingTheory.Polynomial.Content

/-! Reduce bivariate integer formulas in a product and its integer square
root modulo a divisor. Only the constant coefficient in the product survives. -/

namespace PrimeFactors.SquareRootPolynomialFormula

open Polynomial Finset

abbrev Formula := Polynomial (Polynomial ℤ)

/-- The outer variable is the product, and the inner variable is its square root. -/
noncomputable def value (F : Formula) (n : ℕ) (t : ℤ) : ℤ :=
  F.eval₂ (evalRingHom t) (n : ℤ)

noncomputable def specialized (F : Formula) : ℤ[X] := F.coeff 0

/-- Reduction works modulo any divisor of the input, including the input itself. -/
theorem reduce {k n : ℕ} (factor : k ∣ n) (F : Formula) (t : ℤ) :
    (value F n t : ZMod k) = (((specialized F).eval t : ℤ) : ZMod k) := by
  have zero : (n : ZMod k) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd n k).mpr factor
  change (Int.castRingHom (ZMod k)) (F.eval₂ (evalRingHom t) (n : ℤ)) = _
  rw [hom_eval₂, show (Int.castRingHom (ZMod k)) (n : ℤ) = 0 by simpa using zero,
    eval₂_at_zero]
  rfl

theorem primitive_nonzero {P : ℤ[X]} (h : P.IsPrimitive) {p : ℕ} (prime : p.Prime) :
    P.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro zero
  have all : C (p : ℤ) ∣ P := by
    apply (C_dvd_iff_dvd_coeff ..).2
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have coeff := congrArg (fun f : (ZMod p)[X] => f.coeff i) zero
    simpa using coeff
  have absurd := Int.isUnit_iff_natAbs_eq.mp (h _ all)
  exact prime.ne_one (by simpa using absurd)

noncomputable def residues (P : ℤ[X]) (p : ℕ) : Finset (ZMod p) := by
  classical
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    exact (P.map (Int.castRingHom (ZMod p))).roots.toFinset
  else exact ∅

theorem residues_card (P : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    (residues P p).card ≤ P.natDegree := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [residues, dif_pos hp] using
    ((Multiset.toFinset_card_le _).trans
      ((P.map (Int.castRingHom (ZMod p))).card_roots'.trans natDegree_map_le))

/-- With unit content locally, vanishing of the public expression forces the
integer square root into the roots of one fixed primitive polynomial. -/
theorem hit {p n : ℕ} (hp : p.Prime) (factor : p ∣ n) (F : Formula)
    (good : ((specialized F).content : ZMod p) ≠ 0) (t : ℤ)
    (h : (value F n t : ZMod p) = 0) :
    (t : ZMod p) ∈ residues (specialized F).primPart p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rw [reduce factor] at h
  let P := specialized F
  change ((P.eval t : ℤ) : ZMod p) = 0 at h
  change (P.content : ZMod p) ≠ 0 at good
  change (t : ZMod p) ∈ residues P.primPart p
  have split : ((P.eval t : ℤ) : ZMod p) = (P.content : ZMod p) * ((P.primPart.eval t : ℤ) : ZMod p) := by
    conv_lhs => rw [P.eq_C_content_mul_primPart, eval_mul, eval_C, Int.cast_mul]
  have root := (mul_eq_zero.mp (split.symm.trans h)).resolve_left good
  simp only [residues, dif_pos hp, Multiset.mem_toFinset]
  apply (mem_roots (primitive_nonzero P.isPrimitive_primPart hp)).2
  simpa only [IsRoot.def, eval_map, eval₂_at_intCast, Int.coe_castRingHom] using root

/-- A zero specialization always returns a multiple of the entire input. -/
theorem whole_of_zero (F : Formula) (zero : specialized F = 0) (n : ℕ) (t : ℤ) :
    (n : ℤ) ∣ value F n t := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
  rw [reduce (dvd_refl n), zero, eval_zero, Int.cast_zero]

/-- After a successful modular inversion, a rational formula has the same
local zeros as its numerator. The inverse witness is checked modulo N. -/
theorem rational_zero {p n : ℕ} (hp : p.Prime) (factor : p ∣ n)
    (A B : Formula) (t inv : ℤ) (inverse : (n : ℤ) ∣ value B n t*inv-1) :
    ((value A n t*inv : ℤ) : ZMod p) = 0 ↔ (((specialized A).eval t : ℤ) : ZMod p) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have localInv := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    ((Int.natCast_dvd_natCast.mpr factor).trans inverse)
  rw [Int.cast_sub, Int.cast_mul, Int.cast_one, sub_eq_zero] at localInv
  have nz : (inv : ZMod p) ≠ 0 := fun bad => by simp [bad] at localInv
  rw [Int.cast_mul, mul_eq_zero, or_iff_left nz, reduce factor]

end PrimeFactors.SquareRootPolynomialFormula
