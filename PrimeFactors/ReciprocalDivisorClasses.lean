import PrimeFactors.ReciprocalSumCharacter
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Fintype.Units
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.SetTheory.Cardinal.Finite

/-! A public square root of `-D` modulo `N` restricts every odd divisor of `N`
coprime to `D`, when `D ≡ 3 (mod 4)`. For pairwise coprime such moduli,
the simultaneous Jacobi tests retain exactly `1/2^k` of the unit residues
in a complete period. -/

namespace PrimeFactors.ReciprocalDivisorClasses

open ReciprocalSumCharacter
open scoped BigOperators

/-- An integer witness works for every quotient of `a² + D` by `N`. -/
theorem square_of_witness {N D : ℕ} {a : ℤ} (h : (N : ℤ) ∣ a^2 + D) :
    IsSquare (-(D : ZMod N)) := by
  refine ⟨(a : ZMod N), ?_⟩
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  push_cast at hz
  linear_combination -hz

/-- Every odd divisor of the input coprime to the discriminant has positive
Jacobi symbol modulo the discriminant. Both the divisor and the discriminant
may be composite. -/
theorem divisor {D N d : ℕ} (three : D % 4 = 3) (odd : Odd d) (dv : d ∣ N)
    (cop : D.Coprime d) (sq : IsSquare (-(D : ZMod N))) :
    jacobiSym (d : ℤ) D = 1 := by
  have localSquare : IsSquare (-(D : ZMod d)) := by
    simpa only [map_neg, map_natCast] using IsSquare.map (ZMod.castHom dv (ZMod d)) sq
  obtain ⟨z, hz⟩ := localSquare
  have norm : (d : ℤ) ∣ z.valMinAbs^2 + D := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [pow_two, ← hz, neg_add_cancel]
  have pos := from_norm three odd norm
  have alternatives := jacobiSym.eq_one_or_neg_one
    (show (d : ℤ).gcd D = 1 by rw [Int.gcd_natCast_natCast]; exact cop.symm)
  omega

/-- A global coprimality check and a public integer root suffice for every
odd divisor. -/
theorem divisor_of_witness {D N d : ℕ} {a : ℤ} (three : D % 4 = 3)
    (odd : Odd d) (dv : d ∣ N) (cop : N.Coprime D) (h : (N : ℤ) ∣ a^2 + D) :
    jacobiSym (d : ℤ) D = 1 :=
  divisor three odd dv (cop.of_dvd_left dv).symm (square_of_witness h)

/-- Removing an invertible square from the discriminant preserves the square-root
condition on the input. In the forward direction the root is divided by that unit. -/
theorem strip_square {N D s : ℕ} (cop : s.Coprime N) :
    IsSquare (-((D * s^2 : ℕ) : ZMod N)) ↔ IsSquare (-(D : ZMod N)) := by
  let u := ZMod.unitOfCoprime s cop
  have hu : (u : ZMod N) = (s : ZMod N) := ZMod.coe_unitOfCoprime s cop
  push_cast
  rw [← hu, ← neg_mul]
  constructor
  · intro h
    have hs := h.mul (IsSquare.sq ((u⁻¹ : (ZMod N)ˣ) : ZMod N))
    simpa only [mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one] using hs
  · exact fun h => h.mul (IsSquare.sq _)

/-- The congruence on a discriminant survives removal of its square factor. -/
theorem strip_mod_four {D s : ℕ} :
    (D * s^2) % 4 = 3 ↔ D % 4 = 3 ∧ Odd s := by
  rw [Nat.mul_mod, Nat.pow_mod, Nat.odd_iff]
  have hD := Nat.mod_lt D (by decide : 0 < 4)
  have hs := Nat.mod_lt s (by decide : 0 < 4)
  have parity : s % 2 = (s % 4) % 2 := (Nat.mod_mod_of_dvd s (by decide : 2 ∣ 4)).symm
  rw [parity]
  interval_cases D % 4 <;> interval_cases s % 4 <;> decide

/-- The Jacobi test itself is unchanged after removing an invertible square
factor from a positive discriminant. -/
theorem strip_symbol {N D s d : ℕ} (three : (D * s^2) % 4 = 3)
    (cop : s.Coprime N) (dv : d ∣ N) :
    jacobiSym (d : ℤ) (D * s^2) = jacobiSym (d : ℤ) D := by
  obtain ⟨hD, hs⟩ := strip_mod_four.mp three
  rw [jacobiSym.mul_right' _ (by omega : D ≠ 0) (pow_ne_zero _ hs.pos.ne'),
    jacobiSym.pow_right, jacobiSym.sq_one, mul_one]
  rw [Int.gcd_natCast_natCast]
  exact (cop.of_dvd_right dv).symm

/-- Unit residues have a symbol in `{1,-1}`. -/
theorem unit_sign {D : ℕ} [NeZero D] (u : (ZMod D)ˣ) :
    sign (u : ZMod D) = 1 ∨ sign (u : ZMod D) = -1 := by
  have rep : (((u : ZMod D).val : ℤ) : ZMod D) = u := by simp
  rw [← rep, sign_cast]
  exact jacobiSym.eq_one_or_neg_one
    (by rw [Int.gcd_natCast_natCast]; exact ZMod.val_coe_unit_coprime u)

/-- For a single discriminant, exactly half of all units pass. -/
theorem half_units {D : ℕ} (three : D % 4 = 3) :
    2 * Nat.card {u : (ZMod D)ˣ // sign (u : ZMod D) = 1} =
      Nat.card (ZMod D)ˣ := by
  classical
  letI : NeZero D := ⟨by omega⟩
  let flip : {u : (ZMod D)ˣ // sign (u : ZMod D) = 1} ≃
      {u : (ZMod D)ˣ // ¬ sign (u : ZMod D) = 1} := {
    toFun := fun u => ⟨-u.val, by
      change ¬sign (-(u.val : ZMod D)) = 1
      rw [sign_neg three, u.property]
      decide⟩
    invFun := fun u => ⟨-u.val, by
      change sign (-(u.val : ZMod D)) = 1
      rw [sign_neg three, (unit_sign u.val).resolve_left u.property]
      decide⟩
    left_inv := fun u => Subtype.ext (neg_neg _)
    right_inv := fun u => Subtype.ext (neg_neg _) }
  have both := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ) (fun u : (ZMod D)ˣ => sign (u : ZMod D) = 1)
  rw [← Fintype.card_subtype, ← Fintype.card_subtype, ← Fintype.card_congr flip,
    Finset.card_univ] at both
  simpa only [Nat.card_eq_fintype_card, two_mul] using both

/-- A test on the units of the product modulus, using its public integer
representative for every Jacobi test. -/
def Passes {k : ℕ} (D : Fin k → ℕ) (u : (ZMod (∏ i, D i))ˣ) : Prop :=
  ∀ i, jacobiSym (u : ZMod (∏ i, D i)).valMinAbs (D i) = 1

/-- Each integer representative gives exactly the same tests. -/
theorem passes_iff {k : ℕ} (D : Fin k → ℕ) (u : (ZMod (∏ i, D i))ˣ)
    (a : ℤ) (rep : (a : ZMod (∏ i, D i)) = u) :
    Passes D u ↔ ∀ i, jacobiSym a (D i) = 1 := by
  apply forall_congr'
  intro i
  have dv : D i ∣ ∏ j, D j := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have z := congrArg (ZMod.castHom dv (ZMod (D i)))
    ((ZMod.coe_valMinAbs (u : ZMod (∏ i, D i))).trans rep.symm)
  simp only [map_intCast] at z
  rw [jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' _ _ _).mp z)]

/-- All supplied roots place the residue of an actual odd divisor in the
same simultaneous class counted below. -/
theorem passes_of_divisor {N d k : ℕ} (D : Fin k → ℕ) (three : ∀ i, D i % 4 = 3)
    (odd : Odd d) (dv : d ∣ N) (cop : N.Coprime (∏ i, D i))
    (sq : ∀ i, IsSquare (-(D i : ZMod N))) :
    Passes D (ZMod.unitOfCoprime d (cop.of_dvd_left dv)) := by
  apply (passes_iff _ _ (d : ℤ) (by simp)).mpr
  intro i
  exact divisor (three i) odd dv
    ((cop.of_dvd_left dv).of_dvd_right (Finset.dvd_prod_of_mem D (Finset.mem_univ i))).symm
    (sq i)

/-- For `k` pairwise coprime discriminants the exact retained fraction among
units of their product is `1/2^k`. -/
theorem count {k : ℕ} (D : Fin k → ℕ) (three : ∀ i, D i % 4 = 3)
    (cop : Pairwise (fun i j => (D i).Coprime (D j))) :
    2^k * Nat.card {u : (ZMod (∏ i, D i))ˣ // Passes D u} =
      (∏ i, D i).totient := by
  classical
  letI : ∀ i, NeZero (D i) := fun i => ⟨by have := three i; omega⟩
  letI : NeZero (∏ i, D i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (D i)⟩
  let r := ZMod.prodEquivPi D cop
  let e : (ZMod (∏ i, D i))ˣ ≃* ((i : Fin k) → (ZMod (D i))ˣ) :=
    (Units.mapEquiv r.toMulEquiv).trans MulEquiv.piUnits
  have passes (u : (ZMod (∏ i, D i))ˣ) :
      Passes D u ↔ ∀ i, sign (e u i : ZMod (D i)) = 1 := by
    apply forall_congr'
    intro i
    have coord : ((u : ZMod (∏ i, D i)).valMinAbs : ZMod (D i)) = e u i := by
      change _ = r (u : ZMod (∏ i, D i)) i
      have z := congrArg r (ZMod.coe_valMinAbs (u : ZMod (∏ i, D i)))
      rw [map_intCast] at z
      exact congrFun z i
    rw [← coord, sign_cast]
  let ep := (e.toEquiv.subtypeEquiv (p := Passes D)
    (q := fun w => ∀ i, sign (w i : ZMod (D i)) = 1) passes).trans
    (Equiv.subtypePiEquivPi (p := fun i (w : (ZMod (D i))ˣ) => sign (w : ZMod (D i)) = 1))
  have a := Nat.card_congr ep
  rw [Nat.card_pi] at a
  have b := Nat.card_congr e.toEquiv
  rw [Nat.card_pi] at b
  calc
    _ = ∏ i : Fin k, 2 * Nat.card {u : (ZMod (D i))ˣ // sign (u : ZMod (D i)) = 1} := by
      rw [a, Finset.prod_mul_distrib]; simp
    _ = ∏ i : Fin k, Nat.card (ZMod (D i))ˣ :=
      Finset.prod_congr rfl fun i _ => half_units (three i)
    _ = _ := by rw [← b, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

end PrimeFactors.ReciprocalDivisorClasses
