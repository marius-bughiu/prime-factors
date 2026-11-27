import PrimeFactors.DyadicGenusPrecision
import Mathlib.Data.Real.Pi.Bounds

/-!
# The mean genus coefficient at a dyadic semiprime level

Csirik, Wetherell and Zieve, *On the genera of X₀(N)*, §5
(https://arxiv.org/abs/math/0006096), identify 5/(4π²) as the limiting average
of g₀(n)/n over all positive levels. That external theorem motivates the
coefficient below. Our inequalities follow directly from the genus equation
at the particular level and Mathlib's numerical upper bound on π.
-/

namespace PrimeFactors.DyadicGenusAverage

open DyadicGenusPrecision

def level (a p q : ℕ) : ℕ := 8*a^2*(p*q)

noncomputable def coefficient : ℝ := 5 / (4 * Real.pi^2)

theorem coefficient_lower : (259 : ℝ)/2048 < coefficient := by
  unfold coefficient
  rw [lt_div_iff₀ (by positivity)]
  have hs := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d4
  nlinarith only [hs]

/-- At these levels the normalized genus is at most 257/2048. -/
theorem genus_upper {a p q g : ℕ} (ha : 1 ≤ a) (hp : 1024 ≤ p) (hq : 1024 ≤ q)
    (data : GenusData a p q g) : 2048*g ≤ 257*level a p q := by
  have genus := amplification data
  have gu : g ≤ a^2*((p+1)*(q+1)) := by omega
  have pu : 1024*(p+1) ≤ 1025*p := by omega
  have qu : 1024*(q+1) ≤ 1025*q := by omega
  have product := Nat.mul_le_mul pu qu
  have ratio : 256*((p+1)*(q+1)) ≤ 257*(p*q) := by
    nlinarith only [product, Nat.zero_le (p*q)]
  calc
    2048*g ≤ 2048*(a^2*((p+1)*(q+1))) := Nat.mul_le_mul_left _ gu
    _ = (8*a^2)*(256*((p+1)*(q+1))) := by ring
    _ ≤ (8*a^2)*(257*(p*q)) := Nat.mul_le_mul_left _ ratio
    _ = 257*level a p q := by unfold level; ring

/-- The mean prediction overshoots the actual genus by more than L/1024. -/
theorem mean_gap {a p q g : ℕ} (ha : 1 ≤ a) (hp : 1024 ≤ p) (hq : 1024 ≤ q)
    (data : GenusData a p q g) :
    (level a p q : ℝ)/1024 < coefficient * level a p q - g := by
  have pos : 0 < level a p q := by unfold level; positivity
  have up : 2048*(g : ℝ) ≤ 257*(level a p q : ℝ) := by
    exact_mod_cast genus_upper ha hp hq data
  have lower := mul_lt_mul_of_pos_right coefficient_lower (show 0 < (level a p q : ℝ) by
    exact_mod_cast pos)
  linarith only [up, lower]

private theorem sqrt_comparison {L K : ℝ} (kp : 0 ≤ K) (large : (1024*K)^2 ≤ L) :
    K*Real.sqrt L ≤ L/1024 := by
  have lp := (sq_nonneg (1024*K)).trans large
  have root : 1024*K ≤ Real.sqrt L := (Real.le_sqrt (by positivity) lp).mpr large
  have prod := mul_le_mul_of_nonneg_right root (Real.sqrt_nonneg L)
  nlinarith only [prod, Real.sq_sqrt lp]

/-- For p,q≥1024 even an absolute error of √L is already exceeded. -/
theorem above_sqrt {a p q g : ℕ} (ha : 1 ≤ a) (hp : 1024 ≤ p) (hq : 1024 ≤ q)
    (data : GenusData a p q g) :
    Real.sqrt (level a p q) < coefficient * level a p q - g := by
  have large : 1024^2 ≤ level a p q := by
    unfold level
    calc
      1024^2 ≤ 8*1^2*(1024*1024) := by decide
      _ ≤ 8*a^2*(p*q) := by gcongr
  have cmp := sqrt_comparison (K := 1) (L := (level a p q : ℝ)) (by norm_num)
    (by simpa only [mul_one] using (show (1024 : ℝ)^2 ≤ level a p q by exact_mod_cast large))
  simpa only [one_mul] using cmp.trans_lt (mean_gap ha hp hq data)

/-- At levels at least 2^4100 the overshoot exceeds 2^2040 times √L. -/
theorem full_size {a p q g : ℕ} (ha : 1 ≤ a) (hp : 1024 ≤ p) (hq : 1024 ≤ q)
    (data : GenusData a p q g) (large : 2^4100 ≤ level a p q) :
    (2 : ℝ)^2040 * Real.sqrt (level a p q) < coefficient * level a p q - g := by
  have bound : ((2^4100 : ℕ) : ℝ) ≤ (level a p q : ℝ) := Nat.cast_le.mpr large
  have needed : (1024*(2 : ℝ)^2040)^2 ≤ (level a p q : ℝ) := calc
    (1024*(2 : ℝ)^2040)^2 = (2 : ℝ)^4100 := by
      rw [show (1024 : ℝ) = 2^10 by norm_num, ← pow_add, ← pow_mul]
    _ ≤ (level a p q : ℝ) := by simpa only [Nat.cast_pow, Nat.cast_ofNat] using bound
  exact (sqrt_comparison (by positivity) needed).trans_lt (mean_gap ha hp hq data)

/-- A large one-step discrepancy for a cumulative prediction forces a large
absolute discrepancy at one of the two adjacent endpoints. -/
theorem adjacent_jump {L g before after : ℝ}
    (jump : after-before = g-coefficient*L) (gap : L/1024 < coefficient*L-g) :
    L/2048 < |before| ∨ L/2048 < |after| := by
  by_contra! small
  linarith only [small.1, small.2, le_abs_self before, neg_abs_le after, jump, gap]

end PrimeFactors.DyadicGenusAverage
