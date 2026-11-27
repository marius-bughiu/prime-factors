import PrimeFactors.OppositeKeyPolynomial
import Mathlib.Data.ZMod.Basic

/-! A completed polynomial division trace with a unit leading coefficient gives
the same common-divisor degree at both field coordinates. This rules out
finishing such a trace when opposite roots exist at only one coordinate. -/
namespace PrimeFactors.OppositeKeyDivision
open Polynomial OppositeKeyPolynomial
open scoped Polynomial

/-- Record the exact division identities, ending at a zero remainder. -/
inductive Trace {R : Type*} [CommRing R] : R[X] → R[X] → R[X] → Prop
  | stop (h : R[X]) : Trace h 0 h
  | step {a b r h : R[X]} (quotient : R[X]) (eqn : a = quotient*b+r)
      (rest : Trace b r h) : Trace a b h

/-- At any field coordinate, the last polynomial has exactly the common
divisors of the two initial polynomials. No division over the field is needed. -/
theorem common_iff {R K : Type*} [CommRing R] [Field K] (f : R →+* K)
    {a b h : R[X]} (t : Trace a b h) (d : K[X]) :
    (d ∣ a.map f ∧ d ∣ b.map f) ↔ d ∣ h.map f := by
  induction t with
  | stop h => simp
  | @step a b r h q eqn _ ih =>
    rw [←ih, eqn, Polynomial.map_add, Polynomial.map_mul]
    constructor
    · rintro ⟨full, right⟩
      exact ⟨right, (dvd_add_right (dvd_mul_of_dvd_right right _)).mp full⟩
    · rintro ⟨right, residue⟩
      exact ⟨dvd_add (dvd_mul_of_dvd_right right _) residue, right⟩

private theorem local_degree {R K : Type*} [CommRing R] [Field K] (f : R →+* K)
    {a b h : R[X]} (t : Trace a b h) (unit : IsUnit h.leadingCoeff) :
    (∃ d : K[X], 0 < d.natDegree ∧ d ∣ a.map f ∧ d ∣ b.map f) ↔
      0 < h.natDegree := by
  have nonzero := (unit.map f).ne_zero
  have degree := natDegree_map_of_leadingCoeff_ne_zero f nonzero
  have hn : h.map f ≠ 0 := by
    intro z
    apply nonzero
    rw [←leadingCoeff_map_of_leadingCoeff_ne_zero f nonzero, z, leadingCoeff_zero]
  constructor
  · rintro ⟨d, pos, da, db⟩
    rw [←degree]
    exact pos.trans_le (natDegree_le_of_dvd ((common_iff f t d).mp ⟨da,db⟩) hn)
  · intro pos
    exact ⟨_, degree ▸ pos, (common_iff f t _).mpr (dvd_refl _)⟩

/-- If the two coordinates disagree about opposite roots and contain no zero
root, the terminal leading coefficient of any completed trace is a nonunit. -/
theorem mixed_trace {R K L : Type*} [CommRing R] [Field K] [Field L]
    (f : R →+* K) (g : R →+* L) (kf : (2:K) ≠ 0) (lg : (2:L) ≠ 0)
    {m : ℕ} (v : Fin m → R) (nzf : ∀ i, f (v i) ≠ 0) (nzg : ∀ i, g (v i) ≠ 0)
    {e o h : R[X]} (ef : join (e.map f) (o.map f)=∏ i, (X-C (f (v i))))
    (eg : join (e.map g) (o.map g)=∏ i, (X-C (g (v i))))
    (yes : ∃ i j, f (v i) = -f (v j)) (no : ¬∃ i j, g (v i) = -g (v j))
    (t : Trace e o h) : ¬ IsUnit h.leadingCoeff := by
  intro unit
  have pos := (local_degree f t unit).mp ((opposite_iff kf _ nzf ef).mp yes)
  exact no ((opposite_iff lg _ nzg eg).mpr ((local_degree g t unit).mpr pos))

/-- A failed inversion of a nonzero residue yields a proper divisor of the
public modulus, including when it happens early in the trace. -/
theorem nonunit_gcd {n : ℕ} [NeZero n] {x : ZMod n} (nonzero : x ≠ 0)
    (nonunit : ¬ IsUnit x) :
    1 < x.val.gcd n ∧ x.val.gcd n < n ∧ x.val.gcd n ∣ n := by
  have pos := ZMod.val_pos.mpr nonzero
  have gt := Nat.gcd_pos_of_pos_left n pos
  have ne : x.val.gcd n ≠ 1 := by
    intro eq
    have h := (ZMod.isUnit_iff_coprime x.val n).mpr eq
    exact nonunit (by simpa using h)
  exact ⟨by omega, (Nat.gcd_le_left _ pos).trans_lt x.val_lt, Nat.gcd_dvd_right _ _⟩

end PrimeFactors.OppositeKeyDivision
