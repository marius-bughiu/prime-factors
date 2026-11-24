import PrimeFactors.IntervalGap
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

namespace PrimeFactors

/-- The factor pair minimizes a linear objective over all positive integer points
whose product is at least its product. Other points may attain the same minimum. -/
def SupportsFactorPair (s : ℝ) (p q : ℤ) : Prop :=
  ∀ (x y : ℤ), 0 < x → 0 < y → p * q ≤ x * y →
    s * p + q ≤ s * x + y

/-- A rational direction below the objective slope gives a leftward competitor. -/
theorem supportingSlope_left {s : ℝ} {p q a b : ℤ}
    (support : SupportsFactorPair s p q) (hb : b < p) (ha : 0 < q + a)
    (slope : (a : ℝ) < s * b) : a * p - b * q < a * b := by
  by_contra! large
  have feasible : p * q ≤ (p - b) * (q + a) := by nlinarith only [large]
  have cost := support (p - b) (q + a) (by omega) ha feasible
  push_cast at cost
  nlinarith only [cost, slope]

/-- A rational direction above the objective slope gives a rightward competitor. -/
theorem supportingSlope_right {s : ℝ} {p q c d : ℤ}
    (support : SupportsFactorPair s p q) (hd : 0 < p + d) (hc : c < q)
    (slope : s * d < (c : ℝ)) : d * q - c * p < c * d := by
  by_contra! large
  have feasible : p * q ≤ (p + d) * (q - c) := by nlinarith only [large]
  have cost := support (p + d) (q - c) hd (by omega) feasible
  push_cast at cost
  nlinarith only [cost, slope]

/-- An exact factor pair on the first possible integral cost level is a minimizer. -/
theorem supportingSlope_firstLevel {a b p q : ℕ} (hb : 0 < b)
    (level : a * p + b * q = ceilSqrt (4 * a * b * (p * q))) :
    SupportsFactorPair ((a : ℝ) / b) p q := by
  intro x y hx hy feasible
  have hprod : p * q ≤ x.toNat * y.toNat := by
    exact_mod_cast (show (p : ℤ) * q ≤ (x.toNat : ℤ) * (y.toNat : ℤ) by
      simpa [Int.toNat_of_nonneg hx.le, Int.toNat_of_nonneg hy.le] using feasible)
  have bound : 4 * a * b * (p * q) ≤ (a * x.toNat + b * y.toNat) ^ 2 := by
    have h := Nat.mul_le_mul_left (4 * a * b) hprod
    zify at h ⊢
    nlinarith only [h, sq_nonneg ((a : ℤ) * x.toNat - b * y.toNat)]
  have cost := ceilSqrt_le_iff.mpr bound
  rw [← level] at cost
  have realCost : (a : ℝ) * p + b * q ≤ a * (x : ℝ) + b * y := by
    have icost : (a : ℤ) * p + b * q ≤ a * (x.toNat : ℤ) + b * (y.toNat : ℤ) := by
      exact_mod_cast cost
    rw [Int.toNat_of_nonneg hx.le, Int.toNat_of_nonneg hy.le] at icost
    exact_mod_cast icost
  push_cast
  have pos : (0 : ℝ) < b := by exact_mod_cast hb
  field_simp [pos.ne']
  exact div_le_div_of_nonneg_right (by simpa only [mul_comm (q : ℝ), mul_comm (y : ℝ)]
    using realCost) pos.le

/-- The continuous lower bound rounds to 259; the least grid cost is 260. -/
theorem supportingSlope_example :
    (259 - 1 : ℕ) ^ 2 < 4 * 13 * 9 * 143 ∧ 4 * 13 * 9 * 143 ≤ (259 : ℕ) ^ 2 ∧
    (13 : ℕ) * 11 + 9 * 13 = 260 ∧ Nat.Prime 11 ∧ Nat.Prime 13 ∧ 11 * 13 = 143 ∧
    ∀ x y : ℕ, 143 ≤ x * y → 260 ≤ 13 * x + 9 * y := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro x y feasible
  by_cases cheaper : 13 * x + 9 * y < 260
  ·
    have finite : ∀ i : Fin 20, ∀ j : Fin 29, 143 ≤ i.val * j.val →
        260 ≤ 13 * i.val + 9 * j.val := by decide
    exact finite ⟨x, by omega⟩ ⟨y, by omega⟩ feasible
  · omega

/-- Extremal candidates in one product-prefix and ratio interval give an
upper bound on the horizontal span of that cell. -/
theorem supportingSlope_prefixSpan {X p q r t n Δ l u : ℝ}
    (hX : 0 ≤ X) (hp : X ≤ p) (hpr : p ≤ r) (h2 : p ≤ 2 * X)
    (hlo : 1 ≤ l) (hrange : l ≤ u) (hq : q ≤ u * p) (ht : l * r ≤ t)
    (low : n ≤ p * q) (high : r * t ≤ n + Δ) :
    2 * X * (r - p) ≤ Δ + 4 * X ^ 2 * (u - l) := by
  have hp0 : 0 ≤ p := hX.trans hp
  have hr0 : 0 ≤ r := hp0.trans hpr
  have square : 0 ≤ r ^ 2 - p ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hpr) (add_nonneg hr0 hp0)]
  have span : 0 ≤ (r - p) * (r + p - 2 * X) :=
    mul_nonneg (sub_nonneg.mpr hpr) (by linarith)
  have pmax : 0 ≤ 4 * X ^ 2 - p ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ 2 * X + p by linarith)]
  nlinarith only [span, low, high, mul_le_mul_of_nonneg_left hq hp0,
    mul_le_mul_of_nonneg_left ht hr0, mul_nonneg (sub_nonneg.mpr hlo) square,
    mul_nonneg (sub_nonneg.mpr hrange) pmax]

set_option exponentiation.threshold 1024 in
/-- The exact constant comparisons used after dividing by the prime-pair count. -/
theorem supportingSlope_probability_constants :
    2 ^ 460 * 3022 * 710 * 10000 * 57 < (1000 * 22 ^ 2 * 2 ^ 482 : ℕ) ∧
    2 ^ 448 * 472 * 2 * 710 ^ 2 * 10000 < (22 ^ 2 * 2 ^ 482 : ℕ) := by
  decide

end PrimeFactors
