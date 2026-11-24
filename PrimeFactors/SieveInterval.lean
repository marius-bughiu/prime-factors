import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace PrimeFactors

/-- Each complete period contributes every accepted residue once. The right side counts
accepted integers in the half-open interval starting at `start` and having width `W`,
using offsets in `Fin W`. -/
theorem periodic_interval_lower_bound {M : ℕ} (hM : 0 < M) (P : ZMod M → Prop)
    (start W : ℕ) :
    W / M * Nat.card {r : ZMod M // P r} ≤
      Nat.card {k : Fin W // P ((start + k.val : ℕ) : ZMod M)} := by
  letI : NeZero M := ⟨hM.ne'⟩
  let pos (i : Fin (W / M)) (r : ZMod M) := i.val * M + (r - (start : ZMod M)).val
  have in_range (i : Fin (W / M)) (r : ZMod M) : pos i r < W := by
    calc
      pos i r < i.val * M + M := Nat.add_lt_add_left (ZMod.val_lt _) _
      _ = (i.val + 1) * M := (Nat.succ_mul _ _).symm
      _ ≤ (W / M) * M := Nat.mul_le_mul_right M i.isLt
      _ ≤ W := Nat.div_mul_le_self W M
  have place (i : Fin (W / M)) (r : ZMod M) : ((start + pos i r : ℕ) : ZMod M) = r := by
    simp [pos, ZMod.natCast_self, ZMod.natCast_zmod_val]
  let hits := {k : Fin W // P ((start + k.val : ℕ) : ZMod M)}
  let pack (u : Fin (W / M) × {r : ZMod M // P r}) : hits :=
    ⟨⟨pos u.1 u.2.val, in_range _ _⟩, by simpa only [place] using u.2.property⟩
  have injective : Function.Injective pack := by
    rintro ⟨i, r⟩ ⟨j, t⟩ heq
    have hpos := congrArg (fun k : hits => k.val.val) heq
    change pos i r.val = pos j t.val at hpos
    have hres : r.val = t.val := by rw [← place i r.val, hpos, place]
    apply Prod.ext
    · apply Fin.ext
      change i.val * M + _ = j.val * M + _ at hpos
      rw [hres] at hpos
      exact Nat.eq_of_mul_eq_mul_right hM (Nat.add_right_cancel hpos)
    · exact Subtype.ext hres
  have hfin : Nat.card (Fin (W / M)) = W / M := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  simpa only [Nat.card_prod, hfin] using Nat.card_le_card_of_injective pack injective

end PrimeFactors
