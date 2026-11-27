import PrimeFactors.PellCycles
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.Nat.Sqrt

/-! Exact small-support obstructions for bounded lists of complete denominators
of the continued fraction of √(4N). A certificate supplies one private
nonsquare factor per row. Its complementary factor in the same row can share
arbitrary primes with the other rows. -/

namespace PrimeFactors.SquareClassPrivateRows

/-- Absolute row norms in the ordinary complete-quotient recurrence. -/
def denominators (rad floorRoot : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | k+1, off, den =>
      let a := (floorRoot + off) / den
      let nextOff := a*den - off
      let nextDen := (rad - nextOff^2) / den
      nextDen :: denominators rad floorRoot k nextOff nextDen

def cfRows (N steps : ℕ) : List ℕ :=
  denominators (4*N) (4*N).sqrt steps 0 1

/-- The certificate identifies a factor from the row by dividing by a small
cofactor, and proves it nonsquare modulo a small test modulus. -/
def RowCheck (total external row : ℕ) (c : ℕ × ℕ) : Prop :=
  let u := row / c.1
  0 < u ∧ u ∣ row ∧ u.Coprime (total/u*external) ∧ 0 < c.2 ∧
    ∀ z ∈ List.range c.2, z^2 % c.2 ≠ u % c.2

noncomputable instance (total external row : ℕ) (c : ℕ × ℕ) : Decidable (RowCheck total external row c) := by
  unfold RowCheck
  infer_instance

/-- Match row and witness lists including their lengths. -/
noncomputable def check (total external : ℕ) : List ℕ → List (ℕ × ℕ) → Bool
  | [], [] => true
  | x :: xs, c :: cs => decide (RowCheck total external x c) && check total external xs cs
  | _, _ => false

private theorem sound {total external : ℕ} (rows : List ℕ) (cs : List (ℕ × ℕ))
    (checked : check total external rows cs = true) :
    ∀ r ∈ rows, ∃ u, 0 < u ∧ u ∣ r ∧ u.Coprime (total/u*external) ∧ ¬ IsSquare u := by
  induction rows generalizing cs with
  | nil => simp
  | cons x xs ih =>
    cases cs with
    | nil => simp [check] at checked
    | cons c cs =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at checked
      obtain ⟨⟨up,dv,cop,mp,absent⟩,ht⟩ := checked
      intro r mem
      rcases List.mem_cons.mp mem with rfl | rest
      · refine ⟨r/c.1, up, dv, cop, ?_⟩
        rintro ⟨v, hv⟩
        apply absent (v % c.2) (List.mem_range.mpr (Nat.mod_lt _ mp))
        rw [hv, ← pow_two, ← Nat.pow_mod]
      · exact ih cs ht _ rest

/-- Every nonempty sublist has a private nonsquare in its product,
even after multiplication by any integer supported on the external base. -/
theorem no_supported_square {rows : List ℕ} {external : ℕ} {cs : List (ℕ × ℕ)}
    (checked : check rows.prod external rows cs = true) {s : List ℕ}
    (sub : s.Sublist rows) (nonempty : s ≠ []) {M k : ℕ} (support : M ∣ external^k) :
    ¬ IsSquare (s.prod * M) := by
  cases s with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs =>
    obtain ⟨u,hpos,divides,cop,non⟩ := sound rows cs checked x (sub.subset (by simp))
    have d : u ∣ (x :: xs).prod := divides.trans (dvd_mul_right _ _)
    obtain ⟨rest,hr⟩ := d
    obtain ⟨other,ho⟩ := sub.prod_dvd_prod
    have dr : rest ∣ rows.prod/u := ⟨other, by rw [ho, hr, Nat.mul_assoc, Nat.mul_div_cancel_left _ hpos]⟩
    obtain ⟨ca,ce⟩ := Nat.coprime_mul_iff_right.mp cop
    rw [hr]
    exact pellCycles_external_private non (ca.of_dvd_right dr) ce support

/-- No selected product has squarefree support confined to the specified
base. This is the integer product identity needed for a projected root. -/
theorem no_supported_remainder {rows : List ℕ} {external : ℕ} {cs : List (ℕ × ℕ)}
    (checked : check rows.prod external rows cs = true) {s : List ℕ}
    (sub : s.Sublist rows) (nonempty : s ≠ []) {M k : ℕ} (support : M ∣ external^k)
    (z : ℕ) : s.prod ≠ M*z^2 := by
  intro h
  apply no_supported_square checked sub nonempty support
  exact ⟨M*z, by rw [h]; ring⟩

end PrimeFactors.SquareClassPrivateRows
