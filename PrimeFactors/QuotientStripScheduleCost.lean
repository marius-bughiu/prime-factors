import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Cost of the ascending sixth-root strip schedule

Count the consecutive strips of width twice the nearest sixth root of the
product. The count includes the strip containing the stopping coordinate.
A final partial strip counts as one visit. The bounds concern this schedule
and allow arbitrary savings inside each strip.
-/

namespace PrimeFactors.QuotientStripScheduleCost

set_option exponentiation.threshold 4096

/-- Left endpoint of the balanced search for positive N. -/
def first (n : ℕ) : ℕ := ((n - 1) / 2).sqrt + 1

private theorem exists_root (n : ℕ) : ∃ r : ℕ, 0 < r ∧ 64 * n ≤ (2 * r + 1) ^ 6 := by
  refine ⟨64 * n + 1, by omega, ?_⟩
  exact (show 64 * n ≤ 2 * (64 * n + 1) + 1 by omega).trans
    (Nat.le_self_pow (by decide) _)

/-- The first positive r with N^(1/6) ≤ r + 1/2. -/
noncomputable def roundedSixth (n : ℕ) : ℕ := Nat.find (exists_root n)

/-- The Python schedule partitions the inclusive interval into successive blocks
of this width. -/
noncomputable def width (n : ℕ) : ℕ := 2 * roundedSixth n

/-- Number of strips through an inclusive endpoint in the ascending schedule. -/
noncomputable def visitsThrough (n stop : ℕ) : ℕ :=
  if stop < first n then 0 else (stop - first n) / width n + 1

private theorem root_le {n k : ℕ} (pos : 0 < k) (atK : 64 * n ≤ (2 * k + 1) ^ 6) :
    roundedSixth n ≤ k := Nat.find_min' _ ⟨pos, atK⟩

private theorem root_gt {n k : ℕ} (below : (2 * k + 1) ^ 6 < 64 * n) :
    k < roundedSixth n := by
  by_contra! bad
  have cmp := Nat.pow_le_pow_left (show 2 * roundedSixth n + 1 ≤ 2 * k + 1 by omega) 6
  exact (not_le_of_gt below) ((Nat.find_spec (exists_root n)).2.trans cmp)

private theorem width_pos (n : ℕ) : 0 < width n := by
  have positive : 0 < roundedSixth n := (Nat.find_spec (exists_root n)).1
  unfold width
  omega

private theorem width_upper {n : ℕ} (high : n < 2 ^ 2048) :
    width n ≤ 42 * 2 ^ 337 := by
  have upper := root_le (n := n) (k := 21 * 2 ^ 337) (by decide) <|
    (Nat.mul_le_mul_left 64 high.le).trans (by decide +kernel)
  unfold width
  omega

private theorem width_lower {n : ℕ} (low : 2 ^ 2047 ≤ n) :
    70 * 2 ^ 336 ≤ width n := by
  have lower := root_gt (k := 35 * 2 ^ 336) <|
    (show (2 * (35 * 2 ^ 336) + 1) ^ 6 < 64 * 2 ^ 2047 by decide +kernel).trans_le
      (Nat.mul_le_mul_left 64 low)
  unfold width
  omega

private theorem upper_half_width {n : ℕ} (low : 3 * 2 ^ 2046 ≤ n) :
    38 * 2 ^ 337 ≤ width n := by
  have lower := root_gt (k := 19 * 2 ^ 337) <|
    (show (2 * (19 * 2 ^ 337) + 1) ^ 6 < 64 * (3 * 2 ^ 2046) by decide +kernel).trans_le
      (Nat.mul_le_mul_left 64 low)
  unfold width
  omega

/-- Bounds on the two rounded endpoints, retaining their correlation. -/
private theorem endpoints {n : ℕ} (positive : 0 < n) :
    12 * n.sqrt ≤ 17 * first n ∧ 7 * first n ≤ 5 * (n.sqrt + 1) + 7 := by
  let a := ((n - 1) / 2).sqrt
  let b := n.sqrt
  have left := Nat.sqrt_le' ((n - 1) / 2)
  have next := Nat.lt_succ_sqrt' ((n - 1) / 2)
  have right := Nat.sqrt_le' n
  have last := Nat.lt_succ_sqrt' n
  have half : 2 * ((n - 1) / 2) ≤ n ∧ n ≤ 2 * (((n - 1) / 2) + 1) := by omega
  change a ^ 2 ≤ _ at left
  change _ < (a + 1) ^ 2 at next
  change b ^ 2 ≤ _ at right
  change _ < (b + 1) ^ 2 at last
  change 12 * b ≤ 17 * (a + 1) ∧ 7 * (a + 1) ≤ 5 * (b + 1) + 7
  constructor
  · apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    nlinarith only [next, right, half.2, Nat.zero_le a, Nat.zero_le n]
  · have bound : 7 * a ≤ 5 * (b + 1) := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
      nlinarith only [left, half.1, last, Nat.zero_le n]
    omega

private theorem lower_count {n stop budget : ℕ} (span : first n + budget * width n ≤ stop) :
    budget < visitsThrough n stop := by
  have pos := width_pos n
  rw [visitsThrough, if_neg (by omega)]
  have fit : budget * width n ≤ stop - first n := by omega
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le pos).mpr fit)

private theorem upper_count {n stop budget : ℕ} (positive : 0 < budget)
    (span : stop < first n + (budget - 1) * width n) : visitsThrough n stop < budget := by
  unfold visitsThrough
  split
  · exact positive
  · have steps : (stop - first n) / width n < budget - 1 :=
      (Nat.div_lt_iff_lt_mul (width_pos n)).mpr (by omega)
    omega

/-- Every full sweep of a 2,048-bit product visits strictly between these
successive powers of two, even if every within-strip decision is immediate. -/
theorem full_2048 {n : ℕ} (low : 2 ^ 2047 ≤ n) (high : n < 2 ^ 2048) :
    2 ^ 679 < visitsThrough n n.sqrt ∧ visitsThrough n n.sqrt < 2 ^ 680 := by
  have pos : 0 < n := (by decide : 0 < 2 ^ 2047).trans_le low
  obtain ⟨left, right⟩ := endpoints pos
  have rootLow : 11 * 2 ^ 1020 ≤ n.sqrt := Nat.le_sqrt'.mpr ((by decide +kernel :
    (11 * 2 ^ 1020) ^ 2 ≤ 2 ^ 2047).trans low)
  have upper := Nat.mul_le_mul_left (2 ^ 679) (width_upper high)
  constructor
  · apply lower_count
    omega
  · apply upper_count (by decide)
    by_cases lowerHalf : n < 3 * 2 ^ 2046
    · have rootHigh : n.sqrt < 7 * 2 ^ 1021 := Nat.sqrt_lt'.mpr
        (lowerHalf.trans_le (by decide +kernel))
      have lower := Nat.mul_le_mul_left (2 ^ 680 - 1) (width_lower low)
      omega
    · have rootHigh : n.sqrt < 2 ^ 1024 := Nat.sqrt_lt'.mpr
        (high.trans_le (by decide +kernel))
      have lower := Nat.mul_le_mul_left (2 ^ 680 - 1) (upper_half_width (by omega : 3 * 2 ^ 2046 ≤ n))
      omega

/-- If the larger factor is at most four thirds of the smaller factor, the
ascending sweep must visit more than 2^678 strips to reach the smaller one.
This includes the visit containing p and assumes no prior exit outside the schedule. -/
theorem through_factor_2048 {n p q : ℕ} (product : n = p * q) (ordered : p ≤ q)
    (ratio : 3 * q ≤ 4 * p) (low : 2 ^ 2047 ≤ n) (high : n < 2 ^ 2048) :
    first n ≤ p ∧ p ≤ n.sqrt ∧ 2 ^ 678 < visitsThrough n p := by
  let a := ((n - 1) / 2).sqrt
  have left : a ^ 2 ≤ (n - 1) / 2 := Nat.sqrt_le' _
  have half : 2 * ((n - 1) / 2) ≤ n := by omega
  have ratioProd := Nat.mul_le_mul_left p ratio
  have pLow : 9 * 2 ^ 1020 ≤ p := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    have h : 4 * (9 * 2 ^ 1020) ^ 2 ≤ 3 * 2 ^ 2047 := by decide +kernel
    nlinarith only [product, ratioProd, low, h]
  have frac : 6 * a ≤ 5 * p := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    nlinarith only [left, half, product, ratioProd]
  have start : first n = a + 1 := rfl
  have upper := Nat.mul_le_mul_left (2 ^ 678) (width_upper high)
  refine ⟨by omega, Nat.le_sqrt'.mpr (by nlinarith only [product, Nat.mul_le_mul_left p ordered]), ?_⟩
  apply lower_count
  omega

/-- The equal-width partner bound can discard a whole prefix in one operation.
On the high product range shown here, at least 2^678 *complete* strips lie
strictly below the public restart coordinate. Any pair with the stated
partner bound survives the jump. -/
theorem skip_prefix_2048 {n : ℕ} (low : 3 * 2 ^ 2046 ≤ n) (high : n < 2 ^ 2048) :
    first n + 2 ^ 678 * width n ≤ n / 2 ^ 1024 ∧
      ∀ p q : ℕ, p * q = n → q ≤ 2 ^ 1024 → n / 2 ^ 1024 ≤ p := by
  let a := ((n - 1) / 2).sqrt
  let restart := n / 2 ^ 1024
  have left : a ^ 2 ≤ (n - 1) / 2 := Nat.sqrt_le' _
  have half : 2 * ((n - 1) / 2) ≤ n := by omega
  have restartLow : 3 * 2 ^ 1022 ≤ restart := (Nat.le_div_iff_mul_le (by decide)).mpr
    ((by decide +kernel : 3 * 2 ^ 1022 * 2 ^ 1024 ≤ 3 * 2 ^ 2046).trans low)
  have next : n < (restart + 1) * 2 ^ 1024 := by
    dsimp only [restart]
    omega
  have coefficient : 3 * 2 ^ 1024 ≤ 4 * (restart + 1) := by omega
  have bound : 6 * a ≤ 5 * (restart + 1) := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    have product := Nat.mul_le_mul_left (restart + 1) coefficient
    nlinarith only [left, half, next, product, Nat.zero_le restart]
  have start : first n = a + 1 := rfl
  have upper := Nat.mul_le_mul_left (2 ^ 678) (width_upper high)
  refine ⟨by change first n + _ ≤ restart; omega, ?_⟩
  intro p q hit cap
  rw [← hit]
  exact Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left p cap)

end PrimeFactors.QuotientStripScheduleCost
