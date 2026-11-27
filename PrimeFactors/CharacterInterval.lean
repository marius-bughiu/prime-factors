import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! Count the surviving positions of any fixed modular test on a finite
arithmetic progression, including its final incomplete period. -/
namespace PrimeFactors.CharacterInterval
open Finset

variable {d : ℕ} [NeZero d]

noncomputable def surviving (A : Finset (ZMod d)) (first step len : ℕ) : Finset ℕ := by
  classical exact (range len).filter fun i => (first + step*i : ZMod d) ∈ A

/-- Record the period number and the residue of a surviving position. Each
pair determines at most one position when the stride is invertible. -/
theorem capacity (A : Finset (ZMod d)) (first step len blocks : ℕ)
    (unit : IsUnit (step : ZMod d)) (cover : len ≤ blocks*d) :
    (surviving A first step len).card ≤ blocks*A.card := by
  classical
  let f (i : ℕ) : ℕ × ZMod d := (i/d,first+step*i)
  have sub : (surviving A first step len).image f ⊆ range blocks ×ˢ A := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    obtain ⟨hi,member⟩ := mem_filter.mp hi
    exact mem_product.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul (NeZero.pos d)).mpr
      ((mem_range.mp hi).trans_le cover)), member⟩
  have inj : Function.Injective f := by
    intro i j equal
    have block : i/d=j/d := congrArg Prod.fst equal
    have same : (first : ZMod d) + step*i = first + step*j := congrArg Prod.snd equal
    have residue := (ZMod.natCast_eq_natCast_iff i j d).mp (unit.mul_left_cancel (add_left_cancel same))
    change i%d=j%d at residue
    have hi := Nat.mod_add_div i d
    have hj := Nat.mod_add_div j d
    rw [residue,block,hj] at hi
    exact hi.symm
  calc
    _ = ((surviving A first step len).image f).card := (card_image_of_injective _ inj).symm
    _ ≤ _ := (card_le_card sub).trans_eq (by simp)

/-- Splitting off the unfinished suffix permits the better of the modulus
cap and the actual number of positions left. -/
theorem with_tail (A : Finset (ZMod d)) (first step blocks tail : ℕ)
    (unit : IsUnit (step : ZMod d)) :
    (surviving A first step (blocks*d+tail)).card ≤ blocks*A.card+tail := by
  classical
  have full := capacity A first step (blocks*d) blocks unit le_rfl
  rw [surviving,card_filter,Finset.sum_range_add]
  rw [surviving,card_filter] at full
  exact Nat.add_le_add full (by
    calc
      _ ≤ ∑ _i ∈ range tail, 1 := Finset.sum_le_sum fun _ _ => by split <;> decide
      _ = tail := by simp)

end PrimeFactors.CharacterInterval
