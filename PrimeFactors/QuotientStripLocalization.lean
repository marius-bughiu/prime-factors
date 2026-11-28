import PrimeFactors.QuotientSearch
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.IntervalCases

/-!
# Localizing a zero product error from six integer moments

For each indexed strip row write `x` for its first coordinate and `e = x*y-N`
for its product error. The Gram matrix of the rows `(1,x,e)` uses only
the count and the sums of `x`, `e`, `x²`, `x*e`, and `e²`, in that order.
Removing a genuine factor row with first coordinate `k` leaves a Gram matrix
with nonnegative determinant. Completing its quadratic in `k` gives an
integer interval. It can be empty, can contain a single integer, or can leave
several candidates. Candidate coordinates still require a divisibility check.
-/

namespace PrimeFactors.QuotientStripLocalization

open Finset Matrix

/-- Determinant in the six independent entries of a symmetric 3×3 matrix. -/
def det6 (t a b c d h : ℤ) : ℤ := t * c * h + 2 * a * b * d - t * d ^ 2 - c * b ^ 2 - h * a ^ 2

/-- The symmetric matrix with the given six upper-triangular entries. -/
def matrix6 (t a b c d h : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![t, a, b; a, c, d; b, d, h]

theorem det_matrix (t a b c d h : ℤ) : (matrix6 t a b c d h).det = det6 t a b c d h := by
  simp [Matrix.det_fin_three, matrix6, det6]
  ring

private theorem centered {ι : Type*} (s : Finset ι) (f g : ι → ℤ) :
    let n : ℤ := s.card
    let a := ∑ i ∈ s, f i
    let b := ∑ i ∈ s, g i
    ∑ i ∈ s, (n * f i - a) * (n * g i - b) = n * (n * (∑ i ∈ s, f i * g i) - a * b) := by
  let n : ℤ := s.card
  let a := ∑ i ∈ s, f i
  let b := ∑ i ∈ s, g i
  change ∑ i ∈ s, (n * f i - a) * (n * g i - b) = n * (n * (∑ i ∈ s, f i * g i) - a * b)
  calc
    _ = ∑ i ∈ s, ((n ^ 2) * (f i * g i) - (n * b) * (f i) - (n * a) * (g i) + a * b) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      change n ^ 2 * (∑ i ∈ s, f i * g i) - n * b * a - n * a * b + a * (n * b) = _
      ring

/-- The Gram determinant of the three columns `1, x, e` is nonnegative. -/
theorem gram_nonneg {ι : Type*} (s : Finset ι) (x e : ι → ℤ) :
    0 ≤ det6 s.card (∑ i ∈ s, x i) (∑ i ∈ s, e i) (∑ i ∈ s, x i ^ 2)
      (∑ i ∈ s, x i * e i) (∑ i ∈ s, e i ^ 2) := by
  by_cases empty : s = ∅
  · simp [empty, det6]
  let n : ℤ := s.card
  let a := ∑ i ∈ s, x i
  let b := ∑ i ∈ s, e i
  let c := ∑ i ∈ s, x i ^ 2
  let d := ∑ i ∈ s, x i * e i
  let h := ∑ i ∈ s, e i ^ 2
  have np : 0 < n := Int.natCast_pos.mpr (card_pos.mpr (nonempty_iff_ne_empty.mpr empty))
  have cs := sum_mul_sq_le_sq_mul_sq s (fun i => n * x i - a) (fun i => n * e i - b)
  have xx : ∑ i ∈ s, (n * x i - a) ^ 2 = n * (n * c - a * a) := by
    simpa only [c, a, n, pow_two] using centered s x x
  have ee : ∑ i ∈ s, (n * e i - b) ^ 2 = n * (n * h - b * b) := by
    simpa only [h, b, n, pow_two] using centered s e e
  have xe : ∑ i ∈ s, (n * x i - a) * (n * e i - b) = n * (n * d - a * b) := centered s x e
  rw [xx, ee, xe] at cs
  have poly : (n * (n * c - a * a)) * (n * (n * h - b * b)) - (n * (n * d - a * b)) ^ 2 =
      n ^ 3 * det6 n a b c d h := by
    unfold det6
    ring
  have nonneg : 0 ≤ n ^ 3 * det6 n a b c d h := poly ▸ sub_nonneg.mpr cs
  exact nonneg_of_mul_nonneg_right nonneg (pow_pos np _)

/-- After deleting the row (1,k,0), the determinant is a quadratic in k. -/
def deletion (t a b c d h k : ℤ) : ℤ :=
  det6 t a b c d h - (c * h - d ^ 2) + 2 * (a * h - b * d) * k - (t * h - b ^ 2) * k ^ 2

theorem rank_one_identity (t a b c d h k : ℤ) :
    (matrix6 t a b c d h - matrix6 1 k 0 (k ^ 2) 0 0).det = deletion t a b c d h k := by
  simp [Matrix.det_fin_three, matrix6, deletion, det6]
  ring

/-- Rows are indexed, so two rows with the same coordinates can be counted separately. -/
theorem deletion_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (x e : ι → ℤ)
    {i : ι} (mem : i ∈ s) (zero : e i = 0) :
    0 ≤ deletion s.card (∑ j ∈ s, x j) (∑ j ∈ s, e j) (∑ j ∈ s, x j ^ 2)
      (∑ j ∈ s, x j * e j) (∑ j ∈ s, e j ^ 2) (x i) := by
  have erase_sum (f : ι → ℤ) : ∑ j ∈ s.erase i, f j = (∑ j ∈ s, f j) - f i := by
    have h := s.add_sum_erase f mem
    omega
  have card : ((s.erase i).card : ℤ) = s.card - 1 := by
    have h := s.card_erase_add_one mem
    omega
  have pos := gram_nonneg (s.erase i) x e
  simp only [erase_sum, card, zero, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at pos
  unfold deletion det6 at *
  convert pos using 1
  ring

/-- The same constraint as a square, valid even when the coefficient vanishes. -/
theorem completed_square (t a b c d h k : ℤ)
    (det : 0 ≤ deletion t a b c d h k) (weight : 0 ≤ t * h - b ^ 2) :
    ((t * h - b ^ 2) * k - (a * h - b * d)) ^ 2 ≤ det6 t a b c d h * (t * h - b ^ 2 - h) := by
  have margin := mul_nonneg weight det
  unfold deletion det6 at *
  nlinarith only [margin]

/-- A zero-error row can be omitted in Cauchy–Schwarz without changing either error moment. -/
theorem weight_ge {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℤ)
    {i : ι} (mem : i ∈ s) (zero : e i = 0) :
    let h := ∑ j ∈ s, e j ^ 2
    h ≤ (s.card : ℤ) * h - (∑ j ∈ s, e j) ^ 2 := by
  have bound := quotient_zero_moment_bound s e mem zero
  dsimp only
  linarith only [bound]

/-- A genuine zero row satisfies the squared bound from the six original moments. -/
theorem localize {ι : Type*} [DecidableEq ι] (s : Finset ι) (x e : ι → ℤ)
    {i : ι} (mem : i ∈ s) (zero : e i = 0) :
    let t : ℤ := s.card
    let a := ∑ j ∈ s, x j
    let b := ∑ j ∈ s, e j
    let c := ∑ j ∈ s, x j ^ 2
    let d := ∑ j ∈ s, x j * e j
    let h := ∑ j ∈ s, e j ^ 2
    ((t * h - b ^ 2) * x i - (a * h - b * d)) ^ 2 ≤ det6 t a b c d h * (t * h - b ^ 2 - h) := by
  have hpos : 0 ≤ ∑ j ∈ s, e j ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  exact completed_square _ _ _ _ _ _ _ (deletion_nonneg s x e mem zero)
    (hpos.trans (weight_ge s e mem zero))

/-- Integer equality of the weighted center in the singular case. If at least
one row has a nonzero error, its coefficient is strictly positive. -/
theorem singular {ι : Type*} [DecidableEq ι] (s : Finset ι) (x e : ι → ℤ)
    {i u : ι} (mem : i ∈ s) (zero : e i = 0) (sample : u ∈ s) (nonzero : e u ≠ 0)
    (rank : det6 s.card (∑ j ∈ s, x j) (∑ j ∈ s, e j) (∑ j ∈ s, x j ^ 2)
      (∑ j ∈ s, x j * e j) (∑ j ∈ s, e j ^ 2) = 0) :
    let h := ∑ j ∈ s, e j ^ 2
    let b := ∑ j ∈ s, e j
    let w := (s.card : ℤ) * h - b ^ 2
    0 < w ∧ w * x i = (∑ j ∈ s, x j) * h - b * (∑ j ∈ s, x j * e j) := by
  have hpos := (sq_pos_of_ne_zero nonzero).trans_le
    (single_le_sum (f := fun j => e j ^ 2) (fun _ _ => sq_nonneg _) sample)
  refine ⟨hpos.trans_le (weight_ge s e mem zero), ?_⟩
  have loc := localize s x e mem zero
  dsimp only at loc ⊢
  rw [rank, zero_mul] at loc
  nlinarith only [loc]

/-- If the certified diameter is below one, every surviving integer is
uniquely determined by the six moments. -/
theorem unique_below_unit {t a b c d h k l : ℤ} (pos : 0 < t * h - b ^ 2)
    (narrow : 4 * (det6 t a b c d h * (t * h - b ^ 2 - h)) < (t * h - b ^ 2) ^ 2)
    (first : 0 ≤ deletion t a b c d h k) (second : 0 ≤ deletion t a b c d h l) : k = l := by
  let w := t * h - b ^ 2
  let center := a * h - b * d
  let radius := det6 t a b c d h * (w - h)
  have positive : 0 < w := pos
  have small : 4 * radius < w ^ 2 := narrow
  have bracket (z : ℤ) (bound : (w * z - center) ^ 2 ≤ radius) :
      -w < 2 * (w * z - center) ∧ 2 * (w * z - center) < w := by
    constructor
    · by_contra! bad
      have order : w ≤ -(2 * (w * z - center)) := by linarith only [bad]
      have square := pow_le_pow_left₀ positive.le order 2
      nlinarith only [square, small, bound]
    · by_contra! bad
      have square := pow_le_pow_left₀ positive.le bad 2
      nlinarith only [square, small, bound]
  obtain ⟨kl, kh⟩ := bracket k (completed_square _ _ _ _ _ _ _ first pos.le)
  obtain ⟨ll, lh⟩ := bracket l (completed_square _ _ _ _ _ _ _ second pos.le)
  rcases lt_trichotomy k l with lt | eqn | gt
  · have step := mul_le_mul_of_nonneg_left (show k + 1 ≤ l by omega) positive.le
    linarith only [step, kh, ll, kl, lh]
  · exact eqn
  · have step := mul_le_mul_of_nonneg_left (show l + 1 ≤ k by omega) positive.le
    linarith only [step, kh, ll, kl, lh]

/-- Sum of row outer products in raw integer coordinates. -/
theorem gram_as_sums {ι : Type*} (s : Finset ι) (x e : ι → ℤ) :
    (∑ j ∈ s, Matrix.vecMulVec ![1, x j, e j] ![1, x j, e j]) =
      matrix6 s.card (∑ j ∈ s, x j) (∑ j ∈ s, e j) (∑ j ∈ s, x j ^ 2)
        (∑ j ∈ s, x j * e j) (∑ j ∈ s, e j ^ 2) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [matrix6, Matrix.sum_apply, Matrix.vecMulVec_apply, pow_two, mul_comm]

theorem outer_zero (k : ℤ) : Matrix.vecMulVec ![1, k, 0] ![1, k, 0] = matrix6 1 k 0 (k ^ 2) 0 0 := by
  ext u v
  fin_cases u <;> fin_cases v <;> simp [matrix6, Matrix.vecMulVec_apply, pow_two]

/-- Specialization to a true product on an arbitrary indexed strip of integer points. -/
theorem strip {ι : Type*} [DecidableEq ι] (n : ℤ) (s : Finset ι) (x y : ι → ℤ)
    {i : ι} (mem : i ∈ s) (trueRow : x i * y i = n) :
    let v (j : ι) := ![(1 : ℤ), x j, x j * y j - n]
    0 ≤ ((∑ j ∈ s, Matrix.vecMulVec (v j) (v j)) - Matrix.vecMulVec (v i) (v i)).det := by
  let e (j : ι) := x j * y j - n
  have zero : e i = 0 := sub_eq_zero.mpr trueRow
  change 0 ≤ ((∑ j ∈ s, Matrix.vecMulVec ![1, x j, e j] ![1, x j, e j]) -
    Matrix.vecMulVec ![1, x i, e i] ![1, x i, e i]).det
  rw [gram_as_sums s x e, zero, outer_zero, rank_one_identity]
  exact deletion_nonneg s x e mem zero

/-- The marginal x-coordinate interval charges all rows at their multiplicity. -/
theorem marginal_window {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℤ) {t : ι}
    (member : t ∈ s) :
    ((s.card : ℤ) * x t - ∑ i ∈ s, x i) ^ 2 ≤
      (s.card - 1 : ℤ) * ((s.card : ℤ) * (∑ i ∈ s, x i * x i) - (∑ i ∈ s, x i) ^ 2) := by
  have count : ((s.erase t).card : ℤ) = (s.card : ℤ) - 1 := by
    have := card_erase_add_one member
    omega
  have split (f : ι → ℤ) : ∑ i ∈ s.erase t, f i = (∑ i ∈ s, f i) - f t :=
    eq_sub_of_add_eq (sum_erase_add s f member)
  have cs := sum_mul_sq_le_sq_mul_sq (s.erase t) (fun _ => (1 : ℤ)) x
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, count, sq, split] at cs
  nlinarith only [mul_le_mul_of_nonneg_left cs (show (0 : ℤ) ≤ s.card by positivity)]

/-- With zero residual variance, a genuine zero row forces the residual sum and
second moment to vanish. -/
theorem zero_variance {c se ee : ℤ} (constant : c * ee = se ^ 2) (nonneg : 0 ≤ ee)
    (keep : se ^ 2 ≤ (c - 1) * ee) : ee = 0 ∧ se = 0 := by
  have h : ee = 0 := by nlinarith
  rw [h, mul_zero] at constant
  exact ⟨h, by nlinarith only [constant]⟩

/-- For a strip containing a zero row, zero weight means every row has zero error.
In this case the determinant after deletion vanishes at every proposed coordinate. -/
theorem zero_weight {ι : Type*} [DecidableEq ι] (s : Finset ι) (x e : ι → ℤ)
    {i : ι} (mem : i ∈ s) (zero : e i = 0)
    (weight : (s.card : ℤ) * (∑ j ∈ s, e j ^ 2) - (∑ j ∈ s, e j) ^ 2 = 0) :
    (∀ j ∈ s, e j = 0) ∧
      ∀ k, deletion s.card (∑ j ∈ s, x j) (∑ j ∈ s, e j) (∑ j ∈ s, x j ^ 2)
        (∑ j ∈ s, x j * e j) (∑ j ∈ s, e j ^ 2) k = 0 := by
  obtain ⟨hZero, bZero⟩ := zero_variance (sub_eq_zero.mp weight)
    (sum_nonneg fun _ _ => sq_nonneg _) (quotient_zero_moment_bound s e mem zero)
  have allZero (j) (hj : j ∈ s) : e j = 0 := by
    have bound := single_le_sum (f := fun j => e j ^ 2) (fun _ _ => sq_nonneg _) hj
    rw [hZero] at bound
    by_contra nonzero
    exact (not_lt_of_ge bound) (sq_pos_of_ne_zero nonzero)
  refine ⟨allZero, fun k => ?_⟩
  have mixed : ∑ j ∈ s, x j * e j = 0 :=
    sum_eq_zero fun j hj => by rw [allZero j hj, mul_zero]
  simp [deletion, det6, hZero, bZero, mixed]

/-- The signed endpoint rounding used by the integer square-root scan. -/
theorem rounded_window {a b k R : ℤ} (ap : 0 < a) :
    (a * k + b) ^ 2 ≤ R ↔ 0 ≤ R ∧ -((b + R.toNat.sqrt) / a) ≤ k ∧ k ≤ (R.toNat.sqrt - b) / a := by
  by_cases pos : 0 ≤ R
  · have conv : ((R.toNat : ℕ) : ℤ) = R := Int.toNat_of_nonneg pos
    have square : (a * k + b) ^ 2 ≤ R ↔ (a * k + b).natAbs ^ 2 ≤ R.toNat := by
      rw [← conv]
      have h := Int.natAbs_sq (a * k + b)
      rw [← h]
      norm_cast
    rw [square, ← Nat.le_sqrt', ← Nat.cast_le (α := ℤ), Int.natCast_natAbs, abs_le]
    have low : -((b + R.toNat.sqrt) / a) ≤ k ↔ (-k) * a ≤ b + R.toNat.sqrt := calc
      _ ↔ -k ≤ (b + R.toNat.sqrt) / a := by omega
      _ ↔ _ := Int.le_ediv_iff_mul_le ap
    rw [and_iff_right pos, low, Int.le_ediv_iff_mul_le ap]
    constructor <;> rintro ⟨l, h⟩ <;> constructor <;> nlinarith only [l, h]
  · simp [pos, (sq_nonneg (a * k + b)).trans_lt' (lt_of_not_ge pos)]

/-- The two forms of the deletion filter are equivalent at positive weight. -/
theorem deletion_iff_square {t a b c d h k : ℤ} (positive : 0 < t * h - b ^ 2) :
    0 ≤ deletion t a b c d h k ↔
      ((t * h - b ^ 2) * k - (a * h - b * d)) ^ 2 ≤ det6 t a b c d h * (t * h - b ^ 2 - h) := by
  constructor
  · exact fun bound => completed_square _ _ _ _ _ _ _ bound positive.le
  · intro bound
    apply nonneg_of_mul_nonneg_right (a := t * h - b ^ 2) _ positive
    unfold deletion det6 at *
    nlinarith only [bound]

/-- The full set of integer strip rows over [91,99] for N = 97 * 131. -/
noncomputable def exampleRows : Finset (ℤ × ℤ) := {(96, 132), (97, 131), (98, 129), (99, 128)}

theorem example_12707_rows (x y : ℤ) :
    (91 ≤ x ∧ x ≤ 99 ∧ 12707 * (2 * 91 - x) ≤ y * 91 ^ 2 ∧ y * 91 * 99 ≤ 12707 * (91 + 99 - x)) ↔
      (x, y) ∈ exampleRows := by
  simp only [exampleRows, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨lo, hi, lower, upper⟩
    interval_cases x <;> norm_num at lower upper ⊢ <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

/-- The coordinates are noncollinear, and the moments are computed from all four rows. -/
theorem example_12707_moments :
    let e (p : ℤ × ℤ) := p.1 * p.2 - 12707
    let s := exampleRows
    (97 - 96 : ℤ) * (129 - 132) ≠ (98 - 96) * (131 - 132) ∧
      (s.card, ∑ p ∈ s, p.1, ∑ p ∈ s, e p, ∑ p ∈ s, p.1 ^ 2,
        ∑ p ∈ s, p.1 * e p, ∑ p ∈ s, (e p) ^ 2) =
      (4, 390, -135, 38030, -13195, 6675) ∧
      det6 4 390 (-135) 38030 (-13195) 6675 = 38150 := by
  decide +kernel

/-- The marginal bound allows 96 through 99. The six moments isolate 97. -/
theorem example_12707_window (k : ℤ) :
    ((4 * k - 390) ^ 2 ≤ (4 - 1) * (4 * 38030 - 390 ^ 2) ↔ 96 ≤ k ∧ k ≤ 99) ∧
      (0 ≤ deletion 4 390 (-135) 38030 (-13195) 6675 k ↔ k = 97) ∧
      97 * 131 = (12707 : ℤ) := by
  have marginal := rounded_window (a := 4) (b := -390) (k := k) (R := 60) (by decide)
  have weighted := rounded_window (a := 8475) (b := -821925) (k := k) (R := 68670000) (by decide)
  have smallRoot : (60 : ℤ).toNat.sqrt = 7 := (Nat.eq_sqrt.mpr (by decide)).symm
  have largeRoot : (68670000 : ℤ).toNat.sqrt = 8286 := (Nat.eq_sqrt.mpr (by decide)).symm
  rw [smallRoot] at marginal
  rw [largeRoot] at weighted
  change ((4 * k + -390) ^ 2 ≤ 60 ↔ _) ∧ _ ∧ _
  constructor
  · rw [marginal]
    omega
  refine ⟨?_, by decide⟩
  rw [deletion_iff_square (by decide)]
  change (8475 * k + -821925) ^ 2 ≤ 68670000 ↔ k = 97
  rw [weighted]
  omega

end PrimeFactors.QuotientStripLocalization
