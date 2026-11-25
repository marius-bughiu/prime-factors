import PrimeFactors.AffineSlopeClasses
import Mathlib.Tactic.Ring

namespace PrimeFactors.CanonicalWeightSlopes

open Finset

/-- The first differing prime-power digit places the first coordinate below the second. -/
def canonical : List ℤ → Prop
  | [] => True
  | z :: zs => z < 0 ∨ (z = 0 ∧ canonical zs)

theorem either_sign (zs : List ℤ) : canonical zs ∨ canonical (zs.map Neg.neg) := by
  induction zs with
  | nil => exact Or.inl trivial
  | cons z zs ih =>
    simp only [canonical, List.map_cons]
    rcases lt_trichotomy z 0 with h | h | h
    · exact Or.inl (Or.inl h)
    · subst z
      simpa using ih
    · exact Or.inr (Or.inl (by omega))

/-- For nonzero unit digits, reduction of their negatives takes u to m-u. -/
theorem reflected_digit_difference {m u w : ℕ} (hu : u ≤ m) (hw : w ≤ m) :
    ((m-u : ℕ) : ℤ) - (m-w : ℕ) = -((u : ℤ)-w) := by omega

theorem negative_unit_digit {m x : ℤ} (hx : 0 < x) (hm : x < m) :
    (-x) % m = m-x := by
  rw [show -x = (m-x)-m by ring, Int.sub_emod_right]
  exact Int.emod_eq_of_lt (by omega) (by omega)

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
theorem reflected_partner (c e u : G) (he : e^2 = 1) : c/(e*u) = e*(c/u) := by
  have hinv : e⁻¹ = e := by
    apply (mul_left_cancel (a := e))
    simpa [sq] using he.symm
  simp [div_eq_mul_inv, hinv, mul_comm, mul_assoc, mul_left_comm]

/-- Canonical orientations of pairs (u, c/u), recorded by their stationary slope c/u². -/
noncomputable def canonicalSlopes (c : G) (digits : G → List ℤ) : Finset G := by
  classical
  exact (univ.filter fun u ↦ canonical (digits u)).image fun u ↦ c*(u⁻¹)^2

/-- Negation by a square root of unity preserves every slope and reverses the CRT digit
comparisons. Thus selecting one representative per coordinate-swap orbit loses no slope. -/
theorem canonicalSlopes_eq (c e : G) (he : e^2 = 1) (digits : G → List ℤ)
    (flip : ∀ u, digits (e*u) = (digits u).map Neg.neg) :
    canonicalSlopes c digits = AffineSlopeClasses.slopes c := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨u, _, rfl⟩ := mem_image.mp hs
    exact mem_image_of_mem _ (mem_univ u⁻¹)
  · intro hs
    obtain ⟨x, _, rfl⟩ := mem_image.mp hs
    rcases either_sign (digits x⁻¹) with hc | hc
    · exact mem_image.mpr ⟨x⁻¹, mem_filter.mpr ⟨mem_univ _, hc⟩, by simp⟩
    · exact mem_image.mpr ⟨e*x⁻¹, mem_filter.mpr ⟨mem_univ _, by rwa [flip]⟩,
        by simp [mul_pow, inv_pow, he]⟩

theorem canonical_slope_count (c e : G) (he : e^2 = 1) (digits : G → List ℤ)
    (flip : ∀ u, digits (e*u) = (digits u).map Neg.neg) :
    Fintype.card G = (canonicalSlopes c digits).card *
      (univ.filter fun t : G ↦ t^2 = 1).card := by
  rw [canonicalSlopes_eq c e he digits flip, AffineSlopeClasses.slope_count c]

/-- Read the signed differences of the two unit digits in an ordered list of CRT components. -/
def digitDifferences (c : G) (rows : List (ℤ × (G → ℤ))) (u : G) : List ℤ :=
  rows.map fun row ↦ row.2 u - row.2 (c/u)

theorem crt_canonical_slope_count (c e : G) (he : e^2 = 1) (rows : List (ℤ × (G → ℤ)))
    (bounds : ∀ row ∈ rows, ∀ u, 0 < row.2 u ∧ row.2 u < row.1)
    (negates : ∀ row ∈ rows, ∀ u, row.2 (e*u) = (-row.2 u) % row.1) :
    Fintype.card G = (canonicalSlopes c (digitDifferences c rows)).card *
      (univ.filter fun t : G ↦ t^2 = 1).card := by
  apply canonical_slope_count c e he
  intro u
  unfold digitDifferences
  rw [List.map_map]
  apply List.map_congr_left
  intro row hr
  dsimp
  rw [reflected_partner c e u he, negates row hr u, negates row hr (c/u),
    negative_unit_digit (bounds row hr u).1 (bounds row hr u).2,
    negative_unit_digit (bounds row hr (c/u)).1 (bounds row hr (c/u)).2]
  ring

/-- A wrapped two-list sum falls in a width-w interval in exactly these two windows. -/
theorem joined_window {x y m w : ℕ} (hx : x < m) (hy : y < m) :
    (x+y)%m ≤ w ↔ x+y ≤ w ∨ (m ≤ x+y ∧ x+y ≤ m+w) := by
  by_cases h : x+y < m
  · rw [Nat.mod_eq_of_lt h]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : m ≤ x+y), Nat.mod_eq_of_lt (by omega : x+y-m < m)]
    omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- For the midpoint-weight 2048-bit control, R is 59 times the first 94 primes.
Its exact slope count uses one local sign at 2 and two at each of the 93 odd primes. -/
theorem control_slope_cutoff :
    let P := (range 492).filter Nat.Prime
    let R := 59 * ∏ p ∈ P, p
    let S := 59 * (∏ p ∈ P, (p-1)) / 2^93
    P.card = 94 ∧ 2^681 < R ∧ R < 2^682 ∧ 2^585 < S ∧ S < 2^586 := by decide +kernel

end PrimeFactors.CanonicalWeightSlopes
