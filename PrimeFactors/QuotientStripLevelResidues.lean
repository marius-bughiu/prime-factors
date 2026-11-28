import PrimeFactors.QuotientStripLevels
import PrimeFactors.OffsetGapLift
import Mathlib.Data.Int.Interval

/-!
# Modulo-eight filter on the five integer strip levels

An odd factor is its own inverse modulo eight. For a true row `x * y = N`,
the projected label `u * x + v * y` is congruent to `x * (u + v * N)`.
All the data needed to filter labels are public. Surviving labels still
require the exact quadratic test.
-/

namespace PrimeFactors.QuotientStripLevelResidues

open Finset

/-- The possible residues, with repetitions removed when the coefficient is even. -/
noncomputable def residues (c : ℤ) : Finset ℤ := {c % 8, (3 * c) % 8, (5 * c) % 8, (7 * c) % 8}

/-- Apply the residue condition to the five consecutive labels starting at L. -/
noncomputable def labels (L c : ℤ) : Finset ℤ :=
  (Icc L (L + 4)).filter fun z => z % 8 ∈ residues c

theorem mem_labels {L c z : ℤ} :
    z ∈ labels L c ↔ (L ≤ z ∧ z ≤ L + 4) ∧ z % 8 ∈ residues c := by
  simp only [labels, mem_filter, mem_Icc]

/-- An odd x gives the partner's residue, also when coordinates are signed. -/
theorem partner_mod_eight {N x y : ℤ} (odd : Odd x) (hit : x * y = N) :
    y ≡ x * N [ZMOD 8] := by
  obtain ⟨k, h⟩ := OffsetGapLift.odd_square odd
  rw [Int.modEq_iff_dvd, ← hit]
  exact ⟨k * y, by linear_combination y * h⟩

theorem level_mod_eight {N x y : ℤ} (u v : ℤ) (odd : Odd x) (hit : x * y = N) :
    (u * x + v * y) % 8 ∈ residues (u + v * N) := by
  let c := u + v * N
  have h : u * x + v * y ≡ (x % 8) * c [ZMOD 8] := calc
    _ ≡ u * x + v * (x * N) [ZMOD 8] :=
      (Int.ModEq.refl _).add ((partner_mod_eight odd hit).mul_left v)
    _ = x * c := by dsimp [c]; ring
    _ ≡ (x % 8) * c [ZMOD 8] := ((Int.mod_modEq x 8).mul_right c).symm
  change (u * x + v * y) % 8 = ((x % 8) * c) % 8 at h
  change (u * x + v * y) % 8 ∈ residues c
  rw [h]
  obtain ⟨k, hk⟩ := odd
  have cases : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  rcases cases with res | res | res | res <;> simp [residues, res]

/-- A genuine odd factor row in the projected interval survives the filter. -/
theorem factor_label {N x y u v low high D : ℤ} (odd : Odd x) (hit : x * y = N)
    (pos : 0 < D) (width : high - low < 5 * D)
    (lower : low ≤ D * (u * x + v * y)) (upper : D * (u * x + v * y) ≤ high) :
    u * x + v * y ∈ labels (-((-low) / D)) (u + v * N) :=
  mem_labels.mpr ⟨QuotientStripLevels.five_labels pos width _ lower upper,
    level_mod_eight u v odd hit⟩

private theorem reduce_coef (c : ℤ) : residues (c % 8) = residues c := by
  have same (a : ℤ) : (a * (c % 8)) % 8 = (a * c) % 8 :=
    (Int.mod_modEq c 8).mul_left a
  simp only [residues, Int.emod_emod, same]

private def phase (z : ℤ) : Fin 8 := ⟨(z % 8).toNat, by omega⟩

private theorem phase_eq (z : ℤ) : ((phase z).val : ℤ) = z % 8 := by
  change (((z % 8).toNat : ℕ) : ℤ) = z % 8
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))

/-- All 64 combinations of the start and coefficient residues. -/
private theorem table : ∀ L c : Fin 8,
    let count := (labels (L.val : ℤ) c.val).card
    count ≤ 3 ∧ (c.val % 2 = 0 → count ≤ 2) ∧ (c.val % 4 = 0 → count ≤ 1) := by
  decide +kernel

/-- At most three labels survive. An even coefficient leaves at most two.
A coefficient divisible by four leaves at most one. -/
theorem card_bounds (L c : ℤ) :
    (labels L c).card ≤ 3 ∧ (Even c → (labels L c).card ≤ 2) ∧
      (4 ∣ c → (labels L c).card ≤ 1) := by
  have shift : (labels L c).card ≤ (labels (L % 8) (c % 8)).card := by
    apply card_le_card_of_injOn (fun z => z - L + L % 8)
    · intro z hz
      obtain ⟨bounds, allowed⟩ := mem_labels.mp hz
      apply mem_labels.mpr
      rw [reduce_coef, show (z - L + L % 8) % 8 = z % 8 by omega]
      exact ⟨by omega, allowed⟩
    · intro x _ y _ eq
      dsimp only at eq
      omega
  obtain ⟨any, even, four⟩ := table (phase L) (phase c)
  simp only [phase_eq] at any even four
  refine ⟨shift.trans any, ?_, ?_⟩
  · rintro ⟨k, hk⟩
    apply shift.trans (even ?_)
    have h := phase_eq c
    omega
  · rintro ⟨k, hk⟩
    apply shift.trans (four ?_)
    have h := phase_eq c
    omega

/-- Each of the three uniform upper bounds is attained. -/
theorem sharp : (labels 1 1).card = 3 ∧ (labels 2 2).card = 2 ∧ (labels 4 4).card = 1 := by
  decide +kernel

/-- For 35 = 5 * 7 and the level x + 2y, 19 is genuine. The same filter
also retains 15, which cannot be the level of any integer factor pair. -/
theorem surviving_miss :
    15 ∈ labels 15 (1 + 2 * 35) ∧ 19 ∈ labels 15 (1 + 2 * 35) ∧
      (5 : ℤ) * 7 = 35 ∧ (5 : ℤ) + 2 * 7 = 19 ∧
      ∀ x y : ℤ, x * y = 35 → x + 2 * y ≠ 15 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro x y product level
  have identity : (x + 2 * y) ^ 2 = (x - 2 * y) ^ 2 + 8 * (x * y) := by ring
  rw [level, product] at identity
  nlinarith only [identity, sq_nonneg (x - 2 * y)]

end PrimeFactors.QuotientStripLevelResidues
