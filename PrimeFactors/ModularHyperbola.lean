import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- For prefixes with block length divisible by M, the entire suffix acceptance
set is independent of both prefixes. This gives literal equality of all counts. -/
theorem hyperbola_prefix_filter_invariant (N M L a c : ℕ) (aligned : M ∣ L) :
    ((Finset.range L) ×ˢ (Finset.range L)).filter
      (fun xy => ((a * L + xy.1) * (c * L + xy.2)) % M = N % M) =
    ((Finset.range L) ×ˢ (Finset.range L)).filter
      (fun xy => (xy.1 * xy.2) % M = N % M) := by
  obtain ⟨k, rfl⟩ := aligned
  apply Finset.filter_congr
  intro xy _
  have removePrefix (e t : ℕ) : e * (M * k) + t ≡ t [MOD M] := by
    show (e * (M * k) + t) % M = t % M
    rw [show e * (M * k) + t = t + M * (e * k) by ring]
    simp
  have eqrem := (removePrefix a xy.1).mul (removePrefix c xy.2)
  change _ % M = _ % M at eqrem
  rw [eqrem]

/-- On a fixed low-digit pair, a product test modulo the square of the radix
is a linear congruence in the high digits. The carry d can be negative. -/
theorem hyperbola_square_lift_iff {R N u w d : ℤ} (nonzero : R ≠ 0)
    (carry : N = u * w + R * d) (v z : ℤ) :
    (u + R * v) * (w + R * z) ≡ N [ZMOD R ^ 2] ↔
      u * z + w * v ≡ d [ZMOD R] := by
  rw [carry, Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j + v * z, ?_⟩
    apply mul_left_cancel₀ nonzero
    linear_combination hj
  · rintro ⟨j, hj⟩
    refine ⟨j - v * z, ?_⟩
    linear_combination R * hj

/-- An inverse of the low digit determines the entire affine progression of
possible high partners. No inverse at precision R² is needed. -/
theorem hyperbola_affine_partner_iff {R N u w d i : ℤ} (nonzero : R ≠ 0)
    (carry : N = u * w + R * d) (inverse : u * i ≡ 1 [ZMOD R]) (v z : ℤ) :
    (u + R * v) * (w + R * z) ≡ N [ZMOD R ^ 2] ↔
      z ≡ i * (d - w * v) [ZMOD R] := by
  rw [hyperbola_square_lift_iff nonzero carry]
  constructor
  · intro h
    have shift := h.sub (Int.ModEq.refl (w * v))
    rw [add_sub_cancel_right] at shift
    calc
      z ≡ (u * i) * z [ZMOD R] := by simpa using inverse.symm.mul (Int.ModEq.refl z)
      _ = i * (u * z) := by ring
      _ ≡ i * (d - w * v) [ZMOD R] := (Int.ModEq.refl i).mul shift
  · intro h
    have shift : u * z ≡ d - w * v [ZMOD R] := calc
      _ ≡ u * (i * (d - w * v)) [ZMOD R] := (Int.ModEq.refl u).mul h
      _ = (u * i) * (d - w * v) := by ring
      _ ≡ d - w * v [ZMOD R] := by simpa using inverse.mul (Int.ModEq.refl (d - w * v))
    simpa using shift.add (Int.ModEq.refl (w * v))

private theorem shifted_floor_ediv {R c : ℤ} (pos : 0 < R) (lo : 0 ≤ c)
    (hi : c ≤ R) (d : ℤ) :
    (d + R - c) / R = d / R + (if c ≤ d % R then 1 else 0) := by
  have hm := Int.emod_add_ediv d R
  have hl := Int.emod_nonneg d pos.ne'
  have hh := Int.emod_lt_of_pos d pos
  rw [show d + R - c = (d % R + R - c) + R * (d / R) by omega,
    Int.add_mul_ediv_left _ _ pos.ne', add_comm]
  congr 1
  split_ifs with test
  · apply (Int.ediv_eq_iff_of_pos pos).2
    simp only [one_mul]
    omega
  · apply Int.ediv_eq_zero_of_lt <;> omega

/-- A difference of two floors is exactly the indicator of a half-open
residue interval. Summation counts an affine class without scanning its digits. -/
theorem hyperbola_interval_indicator {R l h : ℤ} (pos : 0 < R) (low : 0 ≤ l)
    (ordered : l ≤ h) (high : h ≤ R) (d : ℤ) :
    (d + R - l) / R - (d + R - h) / R =
      if l ≤ d % R ∧ d % R < h then 1 else 0 := by
  rw [shifted_floor_ediv pos low (le_trans ordered high),
    shifted_floor_ediv pos (le_trans low ordered) high]
  split_ifs <;> omega

/-- Reported points inject into the divisors of the possible lifted products.
This controls all candidates before their final integer product is checked. -/
theorem hyperbola_points_le_divisor_sum (s : Finset (ℕ × ℕ)) (M N U : ℕ)
    (bounds : ∀ xy ∈ s, 0 < xy.1 ∧ 0 < xy.2 ∧ xy.1 * xy.2 ≤ U ∧
      (xy.1 * xy.2) % M = N % M) :
    s.card ≤ ∑ j ∈ Finset.range (U / M + 1), (N % M + M * j).divisors.card := by
  let key (xy : ℕ × ℕ) : Σ _ : ℕ, ℕ := ⟨(xy.1 * xy.2) / M, xy.1⟩
  have recover (xy : ℕ × ℕ) (h : xy ∈ s) :
      N % M + M * (key xy).1 = xy.1 * xy.2 := by
    rw [← (bounds xy h).2.2.2]
    exact Nat.mod_add_div _ _
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn key
  · intro xy h
    obtain ⟨hx, hy, hu, _⟩ := bounds xy h
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hu)), ?_⟩
    rw [recover xy h]
    exact Nat.mem_divisors.mpr ⟨dvd_mul_right .., (Nat.mul_pos hx hy).ne'⟩
  · intro xy hxy xy' hxy' same
    have index := congrArg Sigma.fst same
    have x : xy.1 = xy'.1 := congrArg (fun t : Σ _ : ℕ, ℕ => t.2) same
    have eqprod : xy.1 * xy.2 = xy'.1 * xy'.2 := by
      rw [← recover xy hxy, ← recover xy' hxy', index]
    exact Prod.ext x (Nat.eq_of_mul_eq_mul_left (bounds xy hxy).1 (x ▸ eqprod))

end PrimeFactors
