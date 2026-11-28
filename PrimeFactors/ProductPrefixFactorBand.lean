import PrimeFactors.Fermat
import Mathlib.Order.Interval.Finset.Nat

/-! An interval of 1024-bit integers whose pairwise products lie inside one
specified 2048-bit prefix bin. The estimates also hold for unaligned bins. -/

namespace PrimeFactors.ProductPrefixFactorBand

set_option exponentiation.threshold 4096

def B : ℕ := 2^1024
def A (K : ℕ) : ℕ := ceilSqrt K
def W (h : ℕ) : ℕ := 2^(1022-h)

/-- The factor interval has exactly this many integer positions. -/
theorem band_card (K h : ℕ) : (Finset.Ioc (A K) (A K + W h)).card = W h := by
  simp

theorem bin_width {h : ℕ} (cap : h ≤ 1022) : 4 * B * W h = 2^(2048-h) := by
  change (2:ℕ)^2 * 2^1024 * 2^(1022-h) = 2^(2048-h)
  rw [← pow_add, ← pow_add]
  congr 1
  omega

theorem width_floor {h : ℕ} (cap : h ≤ 485) : 2^537 ≤ W h :=
  Nat.pow_le_pow_right (by decide) (by omega : 537 ≤ 1022-h)

theorem width_ceiling {h : ℕ} (hpos : 1 ≤ h) : W h ≤ 2^1021 :=
  Nat.pow_le_pow_right (by decide) (by omega : 1022-h ≤ 1021)

theorem ceil_square_ge (K : ℕ) : K ≤ (A K)^2 := ceilSqrt_le_iff.mp le_rfl

/-- Rounding up to the first square costs strictly less than twice its root. -/
theorem ceil_square_lt {K : ℕ} (pos : 0 < K) : (A K)^2 < K + 2 * A K := by
  have nz : A K ≠ 0 := by
    intro zero
    have low := ceil_square_ge K
    rw [zero] at low
    omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero nz
  have prev : r^2 < K := by
    by_contra! small
    have upper : A K ≤ r := ceilSqrt_le_iff.mpr small
    omega
  rw [hr]
  nlinarith only [prev]

/-- A factor band of width w fits below the upper end of a product band of
width 4Tw whenever the ceiling root and the width are both bounded by T. -/
theorem square_ceiling {K T w : ℕ} (pos : 0 < K) (kcap : K ≤ T^2)
    (wide : 2 ≤ w) (short : w ≤ T) : (A K + w)^2 < K + 4*T*w := by
  have root : A K ≤ T := ceilSqrt_le_iff.mpr kcap
  have rounding := ceil_square_lt pos
  have mixed := Nat.mul_le_mul_right w root
  have square := Nat.mul_le_mul_right w short
  have room := Nat.mul_le_mul_right T wide
  nlinarith only [root, rounding, mixed, square, room]

theorem square_window {K h : ℕ} (hpos : 1 ≤ h) (cap : h ≤ 485)
    (bottom : 2^2047 ≤ K) (top : K + 2^(2048-h) ≤ B^2) :
    (A K + W h)^2 < K + 2^(2048-h) := by
  have pos := lt_of_lt_of_le (by decide +kernel : 0 < (2:ℕ)^2047) bottom
  have kcap := (Nat.le_add_right K (2^(2048-h))).trans top
  have wide := (by decide +kernel : 2 ≤ (2:ℕ)^537).trans (width_floor cap)
  have short := (width_ceiling hpos).trans (by decide +kernel : 2^1021 ≤ B)
  simpa only [bin_width (by omega : h ≤ 1022)] using square_ceiling pos kcap wide short

/-- Every integer in the factor band has 1024 bits. -/
theorem factor_window {K h : ℕ} (hpos : 1 ≤ h) (cap : h ≤ 485)
    (bottom : 2^2047 ≤ K) (top : K + 2^(2048-h) ≤ B^2) :
    2^1023 ≤ A K ∧ A K + W h < B := by
  constructor
  · apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    exact (by decide +kernel : ((2:ℕ)^1023)^2 ≤ 2^2047).trans
      (bottom.trans (ceil_square_ge K))
  · have upper := (square_window hpos cap bottom top).trans_le top
    by_contra! fail
    exact (not_le_of_gt upper) (Nat.pow_le_pow_left fail 2)

/-- Every product of two members lies strictly within the specified prefix bin. -/
theorem product_window {K h p q : ℕ} (hpos : 1 ≤ h) (cap : h ≤ 485)
    (bottom : 2^2047 ≤ K) (top : K + 2^(2048-h) ≤ B^2)
    (pl : A K < p) (pu : p ≤ A K + W h) (ql : A K < q) (qu : q ≤ A K + W h) :
    K < p*q ∧ p*q < K + 2^(2048-h) := by
  constructor
  · calc
      K ≤ A K * A K := by simpa only [pow_two] using ceil_square_ge K
      _ ≤ A K * q := Nat.mul_le_mul_left _ ql.le
      _ < p*q := Nat.mul_lt_mul_of_pos_right pl (Nat.zero_lt_of_lt ql)
  · have high : p*q ≤ (A K + W h)^2 := by
      simpa only [pow_two] using Nat.mul_le_mul pu qu
    exact high.trans_lt (square_window hpos cap bottom top)

end PrimeFactors.ProductPrefixFactorBand
