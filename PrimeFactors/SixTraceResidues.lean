import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! A square discriminant at multiplier six forces the trace to be a unit
modulo six. The argument uses only the public input and coprimality. -/
namespace PrimeFactors.SixTraceResidues
open Finset

private theorem reduce_square (m : ℕ) {n s d : ℕ} (h : s^2=24*n+d^2) :
    (s%m)^2 ≡ 24*(n%m)+(d%m)^2 [MOD m] := by
  calc
    (s%m)^2 ≡ s^2 [MOD m] := (Nat.mod_modEq s m).pow 2
    _ = 24*n+d^2 := h
    _ ≡ 24*(n%m)+(d%m)^2 [MOD m] :=
      (((Nat.mod_modEq n m).mul_left 24).add ((Nat.mod_modEq d m).pow 2)).symm

private theorem mod_sixteen : ∀ s d n : Fin 16, (n:ℕ)%2=1 →
    (s:ℕ)^2 ≡ 24*(n:ℕ)+(d:ℕ)^2 [MOD 16] → (s:ℕ)%2=1 := by decide +kernel

private theorem mod_nine : ∀ s d n : Fin 9, (n:ℕ)%3≠0 →
    (s:ℕ)^2 ≡ 24*(n:ℕ)+(d:ℕ)^2 [MOD 9] → (s:ℕ)%3≠0 := by decide +kernel

def admissible (s : ℕ) : Prop := s%6=1 ∨ s%6=5

noncomputable instance (s : ℕ) : Decidable (admissible s) := inferInstanceAs (Decidable (_ ∨ _))

/-- Every genuine integer square passes the wheel, even when its gcd is trivial. -/
theorem of_square {n s d : ℕ} (unit : n.Coprime 6) (h : s^2=24*n+d^2) :
    admissible s := by
  have avoids {p : ℕ} (dvd : p∣6) (large : 1<p) : ¬p∣n := by
    intro div
    have bad := Nat.dvd_gcd div dvd
    rw [unit.gcd_eq_one] at bad
    exact (not_le_of_gt large) (Nat.le_of_dvd (by decide) bad)
  have odd := avoids (by decide : 2∣6) (by decide)
  have three := avoids (by decide : 3∣6) (by decide)
  let atMod (m : ℕ) (hm : 0<m) (x : ℕ) : Fin m := ⟨x%m,Nat.mod_lt _ hm⟩
  have odd' := mod_sixteen (atMod 16 (by decide) s) (atMod 16 (by decide) d)
    (atMod 16 (by decide) n) (by dsimp [atMod]; omega) (reduce_square 16 h)
  have three' := mod_nine (atMod 9 (by decide) s) (atMod 9 (by decide) d)
    (atMod 9 (by decide) n) (by dsimp [atMod]; omega) (reduce_square 9 h)
  dsimp [atMod] at odd' three'
  unfold admissible
  omega

private theorem phased_count : ∀ a : Fin 6, ((range 6).filter (fun i => admissible (a+i))).card=2 := by
  decide +kernel

/-- From any starting label, exactly two of the next six candidates pass. -/
theorem six_consecutive (first : ℕ) :
    ((range 6).filter (fun i => admissible (first+i))).card=2 := by
  have periodic (i : ℕ) : admissible (first%6+i) ↔ admissible (first+i) := by
    unfold admissible
    rw [Nat.mod_add_mod]
  simpa only [periodic] using phased_count ⟨first%6,Nat.mod_lt _ (by decide)⟩

private theorem count_blocks (first blocks : ℕ) :
    ((range (6*blocks)).filter (fun i => admissible (first+i))).card=2*blocks := by
  induction blocks with
  | zero => simp
  | succ k ih =>
    have next := six_consecutive (first+6*k)
    rw [Finset.card_filter] at ih next ⊢
    rw [Nat.mul_succ,Finset.sum_range_add,ih]
    simp only [←Nat.add_assoc,next,Nat.mul_succ]

/-- A budget stated as consecutive integer labels can be converted
to a square-root budget uniformly over the starting phase. -/
theorem prefix_cap (first len : ℕ) :
    ((range len).filter (fun i => admissible (first+i))).card ≤ 2*((len+5)/6) := by
  have cover : len≤6*((len+5)/6) := by omega
  exact (card_le_card (filter_subset_filter _ (range_mono cover))).trans_eq (count_blocks _ _)

theorem cap_50001 (first : ℕ) :
    ((range 50001).filter (fun i => admissible (first+i))).card≤16668 := by
  exact prefix_cap first 50001

end PrimeFactors.SixTraceResidues
