import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- A contiguous window comprising l whole low-digit blocks tests only the
high digit of an arithmetic progression. -/
theorem inverseWindow_high_digit (W B l c s n : ℕ) (positive : 0 < W) :
    (c + W*(s*n)) % (W*B) < W*l ↔ (c/W+s*n) % B < l := by
  rw [Nat.mul_comm W l, ← Nat.div_lt_iff_lt_mul positive,
    Nat.mod_mul_right_div_self, Nat.add_mul_div_left _ _ positive]

private def inverseWindow_zmodFin (B : ℕ) [NeZero B] : Fin B ≃ ZMod B where
  toFun i := (i.val : ZMod B)
  invFun z := ⟨z.val, z.val_lt⟩
  left_inv i := Fin.ext (ZMod.val_natCast_of_lt i.isLt)
  right_inv z := ZMod.natCast_zmod_val z

private theorem inverseWindow_count_one_period {B l c s : ℕ} [NeZero B]
    (unit : s.Coprime B) (fits : l ≤ B) :
    (∑ n : Fin B, if (c+s*n.val)%B < l then 1 else 0) = l := by
  classical
  let low (z : ZMod B) := if z.val < l then 1 else 0
  let e := (inverseWindow_zmodFin B).trans ((ZMod.unitOfCoprime s unit).mulLeft.trans
    (Equiv.addLeft (c : ZMod B)))
  have eval (n : Fin B) : low (e n) = (if (c+s*n.val)%B < l then 1 else 0) := by
    change (if ((c : ZMod B) + ↑(ZMod.unitOfCoprime s unit) * (n.val : ZMod B)).val < l then 1 else 0) = _
    rw [ZMod.coe_unitOfCoprime, ← Nat.cast_mul, ← Nat.cast_add, ZMod.val_natCast]
  let f : {z : ZMod B // z.val < l} ≃ Fin l :=
    { toFun := fun z => ⟨z.val.val,z.property⟩
      invFun := fun i => ⟨(i.val : ZMod B), by simp [ZMod.val_natCast_of_lt (i.isLt.trans_le fits)]⟩
      left_inv := fun z => Subtype.ext (ZMod.natCast_zmod_val z.val)
      right_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt (i.isLt.trans_le fits)) }
  calc
    _ = ∑ n, low (e n) := Finset.sum_congr rfl (fun n _ => (eval n).symm)
    _ = ∑ z, low z := e.sum_comp low
    _ = Fintype.card {z : ZMod B // z.val < l} := by
      rw [Fintype.card_subtype, Finset.card_filter]
    _ = l := (Fintype.card_congr f).trans (Fintype.card_fin l)

/-- Exact number of odd multipliers that put a second point into a translated
window once the first point's local offset u has been fixed. Here M=2*r*B,
the length is 2*r*l, and the inverse-coordinate difference is r*s with s
invertible modulo B. The odd multiplier is 2*n+1. -/
theorem inverseWindow_odd_multiplier_count {r B l s : ℕ} [NeZero B]
    (pos : 0 < r) (unit : s.Coprime B) (fits : l ≤ B) (u : ℕ) :
    (∑ n : Fin (r*B),
      if (u+r*s*(2*n.val+1)) % ((2*r)*B) < (2*r)*l then 1 else 0) = r*l := by
  let F (n : Fin (r*B)) := if (u+r*s*(2*n.val+1)) % ((2*r)*B) < (2*r)*l then 1 else 0
  change ∑ n, F n = r*l
  rw [← finProdFinEquiv.sum_comp F, Fintype.sum_prod_type]
  have inner (i : Fin r) :
      (∑ j : Fin B, F (finProdFinEquiv (i,j))) = l := by
    convert inverseWindow_count_one_period (c := (u+r*s)/(2*r)+s*(B*i.val)) unit fits using 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp [F]
    rw [show u+r*s*(2*(j.val+B*i.val)+1) = (u+r*s)+(2*r)*(s*(j.val+B*i.val)) by ring]
    simp only [inverseWindow_high_digit _ _ _ _ _ _ (by omega : 0 < 2*r),
      show (u+r*s)/(2*r)+s*(j.val+B*i.val) = (u+r*s)/(2*r)+s*(B*i.val)+s*j.val by ring]
  simp [inner]

/-- The translated pair count is L²/2 per pair of distinct inverse slopes
whose difference has the indicated 2-adic order. -/
theorem inverseWindow_joint_count {r B l s : ℕ} [NeZero B]
    (pos : 0 < r) (unit : s.Coprime B) (fits : l ≤ B) :
    (∑ u : Fin (2*r*l), ∑ n : Fin (r*B),
      if (u.val+r*s*(2*n.val+1)) % ((2*r)*B) < (2*r)*l then 1 else 0) =
      (2*r*l)*(r*l) := by
  simp [inverseWindow_odd_multiplier_count pos unit fits]

/-- The inverse-coordinate difference is the source-coordinate difference
multiplied by a unit and a sign. This preserves its dyadic valuation. -/
theorem inverseWindow_unit_difference {R : Type*} [CommRing R] (x y : Rˣ) :
    (↑x⁻¹ : R) - (↑y⁻¹ : R) = (↑x⁻¹ : R)*(↑y⁻¹ : R)*((y : R)-(x : R)) := by
  rw [mul_sub, mul_assoc (↑x⁻¹ : R) _ (↑y : R), y.inv_mul, mul_one,
    mul_right_comm (↑x⁻¹ : R) _ (↑x : R), x.inv_mul, one_mul]

/-- Every translated copy of a dyadic inverse graph can be reconstructed
from its first eighth when the modulus is a multiple of 64. -/
theorem inverseWindow_eighth_translation {h x y N : ℤ} (aligned : 8 ∣ h)
    (odd : Odd x) (point : x*y ≡ N [ZMOD 8*h]) :
    (x+h)*(y-N*h) ≡ N [ZMOD 8*h] := by
  obtain ⟨a, ha⟩ := aligned
  obtain ⟨b, hb⟩ := point.dvd
  have square : (8 : ℤ) ∣ x^2-1 := by
    obtain ⟨k,rfl⟩ := odd
    rcases Int.even_or_odd k with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨2*c^2+c, by rw [hc]; ring⟩
    · exact ⟨2*c^2+3*c+1, by rw [hc]; ring⟩
  obtain ⟨w, hw⟩ := square
  apply Int.modEq_iff_dvd.mpr
  refine ⟨b*(1+x*h)+y*w+N*a, ?_⟩
  linear_combination (1+x*h)*hb + h*y*hw + N*h*ha

/-- A factor rectangle of width L inside [X,2X) spans at most 4XL products. -/
theorem inverseWindow_product_span {x y dx dy X L : ℕ}
    (xhi : x+dx ≤ 2*X) (ylo : y ≤ 2*X) (h₁ : dx ≤ L) (h₂ : dy ≤ L) :
    (x+dx)*(y+dy) ≤ x*y + 4*X*L := by
  calc
    _ = x*y + dx*y + (x+dx)*dy := by ring
    _ ≤ x*y + L*(2*X) + (2*X)*L :=
      Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul h₁ ylo) _) (Nat.mul_le_mul xhi h₂)
    _ = _ := by ring

/-- Only the lifted products in the specified thin strip contribute divisors.
Each positive ordered pair is determined by the strip index and one divisor. -/
theorem inverseWindow_strip_divisors (s : Finset (ℕ × ℕ)) (M N A W : ℕ)
    (base : A ≤ N) (bounds : ∀ v ∈ s, 0 < v.1 ∧ 0 < v.2 ∧ A ≤ v.1*v.2 ∧
      v.1*v.2 ≤ A+W ∧ v.1*v.2 ≡ N [MOD M]) :
    s.card ≤ ∑ j ∈ Finset.range (W/M+1), (A + (N-A)%M + M*j).divisors.card := by
  let key (v : ℕ × ℕ) : Σ _ : ℕ, ℕ := ⟨(v.1*v.2 - A)/M,v.1⟩
  have recover (v : ℕ × ℕ) (hv : v ∈ s) : A+(N-A)%M+M*(key v).1 = v.1*v.2 := by
    obtain ⟨_, _, lo, _, congr⟩ := bounds v hv
    have shifted : v.1*v.2 - A ≡ N-A [MOD M] :=
      Nat.ModEq.add_left_cancel' A (by simpa [Nat.add_sub_of_le lo, Nat.add_sub_of_le base] using congr)
    change (v.1*v.2-A)%M = (N-A)%M at shifted
    rw [← shifted, Nat.add_assoc]
    change A + ((v.1*v.2-A)%M + M*((v.1*v.2-A)/M)) = _
    rw [Nat.mod_add_div, Nat.add_sub_of_le lo]
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn key
  · intro v hv
    obtain ⟨hx, hy, _, hi, _⟩ := bounds v hv
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (show v.1*v.2-A ≤ W by omega))), ?_⟩
    rw [recover v hv]
    exact Nat.mem_divisors.mpr ⟨dvd_mul_right .., (Nat.mul_pos hx hy).ne'⟩
  · intro v hv w hw equal
    have ix := congrArg Sigma.fst equal
    have x := congrArg (fun t : Σ _ : ℕ, ℕ => t.2) equal
    change v.1 = w.1 at x
    have eqprod : v.1*v.2=w.1*w.2 := by rw [← recover v hv, ← recover w hw, ix]
    exact Prod.ext x (Nat.eq_of_mul_eq_mul_left (bounds v hv).1 (x ▸ eqprod))

end PrimeFactors
