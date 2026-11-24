import PrimeFactors.PhaseSeparation
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PrimeFactors

/-- Folded phases away from the two stationary points enjoy a linear inverse
bound. Only the true phase `x` must satisfy the margin. -/
theorem phasePrecision_cosine {x y μ : ℝ} (margin : 0 ≤ μ) (lo : μ ≤ x)
    (hi : x ≤ 1/2-μ) (ylo : 0 ≤ y) (yhi : y ≤ 1/2) :
    8*μ*|x-y| ≤ |Real.cos (2*Real.pi*x)-Real.cos (2*Real.pi*y)| := by
  have s := phase_sine_floor margin (show μ ≤ x+y by linarith)
    (show μ ≤ 1-(x+y) by linarith)
  have d : 2*|x-y| ≤ |Real.sin (Real.pi*(x-y))| := by
    rcases le_total y x with order | order
    · rw [abs_of_nonneg (sub_nonneg.mpr order)]
      exact phase_sine_floor (sub_nonneg.mpr order) le_rfl (by linarith)
    · rw [abs_of_nonpos (sub_nonpos.mpr order),
        show Real.pi*(x-y) = -(Real.pi*(y-x)) by ring, Real.sin_neg, abs_neg, neg_sub]
      exact phase_sine_floor (sub_nonneg.mpr order) le_rfl (by linarith)
  have bound := mul_le_mul s d (mul_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _)
  rw [Real.cos_sub_cos, abs_mul, abs_mul,
    show (2*Real.pi*x+2*Real.pi*y)/2 = Real.pi*(x+y) by ring,
    show (2*Real.pi*x-2*Real.pi*y)/2 = Real.pi*(x-y) by ring]
  norm_num
  linarith only [bound]

/-- Each inverse numerator falls on one of four affine branches at distance
`d` in units of half a residue spacing from an integer or half-integer. -/
noncomputable def phasePrecisionLevel (q z : ℤ) : ℤ := min (2*z) (min |2*z-q| (2*(q-z)))

private theorem phasePrecision_short_unique {p r X q : ℕ}
    (lp : X ≤ p) (up : p < 2*X) (lr : X ≤ r) (ur : r < 2*X) (span : X ≤ q)
    (same : p ≡ r [MOD q]) : p = r := by
  rcases lt_trichotomy p r with h | h | h
  · have := Nat.le_of_dvd (Nat.sub_pos_of_lt h) ((Nat.modEq_iff_dvd' h.le).mp same)
    omega
  · exact h
  · have := Nat.le_of_dvd (Nat.sub_pos_of_lt h) ((Nat.modEq_iff_dvd' h.le).mp same.symm)
    omega

/-- At each fixed level and fixed prime `q`, at most four candidate partners
in the whole dyadic interval can give that level. -/
theorem phasePrecision_row_fiber {row : Finset ℕ} {q X : ℕ} {d : ℤ}
    (label : ℕ → ℕ) (span : X ≤ q) (box : ∀ p ∈ row, X ≤ p ∧ p < 2*X)
    (unit : ∀ p ∈ row, q.Coprime (label p))
    (inverse : ∀ p ∈ row, label p*p ≡ 2 [MOD q])
    (level : ∀ p ∈ row, phasePrecisionLevel q (label p) = d) : row.card ≤ 4 := by
  let targets : Finset ℤ := {d, (q:ℤ)-d, (q:ℤ)+d, 2*(q:ℤ)-d}
  have count : targets.card ≤ 4 := by
    dsimp [targets]
    have h₁ := Finset.card_insert_le d ({(q:ℤ)-d, (q:ℤ)+d, 2*(q:ℤ)-d} : Finset ℤ)
    have h₂ := Finset.card_insert_le ((q:ℤ)-d) ({(q:ℤ)+d, 2*(q:ℤ)-d} : Finset ℤ)
    have h₃ := Finset.card_insert_le ((q:ℤ)+d) ({2*(q:ℤ)-d} : Finset ℤ)
    simp only [Finset.card_singleton] at h₃
    omega
  apply le_trans _ count
  apply Finset.card_le_card_of_injOn (fun p : ℕ => 2*(label p:ℤ))
  · intro p hp
    have e := level p hp
    unfold phasePrecisionLevel at e
    simp only [targets, Finset.mem_insert, Finset.mem_singleton]
    rw [abs_eq_max_neg] at e
    omega
  · intro p hp r hr eq
    change 2*(label p:ℤ) = 2*(label r:ℤ) at eq
    have eq' : label p = label r := by omega
    have a := inverse p hp
    have b := inverse r hr
    rw [←eq'] at b
    exact phasePrecision_short_unique (box p hp).1 (box p hp).2
      (box r hr).1 (box r hr).2 span (Nat.ModEq.cancel_left_of_coprime (unit p hp) (a.trans b.symm))

/-- Moving from `z/q` to `(pz-1)/(pq)` costs at most two units in the doubled
numerator. The exact margin remains at least half its inverse-grid estimate. -/
theorem phasePrecision_grid_margin {p q z : ℤ} (large : 4 ≤ p)
    (nonzero : 1 ≤ phasePrecisionLevel q z) :
    p*phasePrecisionLevel q z ≤ 2*phasePrecisionLevel (p*q) (p*z-1) := by
  let D := phasePrecisionLevel q z
  have a : D ≤ 2*z := min_le_left ..
  have b : D ≤ |2*z-q| := (min_le_right ..).trans (min_le_left ..)
  have c : D ≤ 2*(q-z) := (min_le_right ..).trans (min_le_right ..)
  have positive : 0 ≤ p := by omega
  have big : 4 ≤ p*D := by nlinarith only [Int.mul_le_mul_of_nonneg_left nonzero positive, large]
  have b' := abs_sub_abs_le_abs_sub (p*(2*z-q)) (2*(p*z-1)-p*q)
  rw [abs_mul, abs_of_nonneg positive, show p*(2*z-q)-(2*(p*z-1)-p*q)=2 by ring] at b'
  norm_num at b'
  have bound : p*D-2 ≤ phasePrecisionLevel (p*q) (p*z-1) := by
    apply le_min
    · nlinarith only [mul_le_mul_of_nonneg_left a positive]
    apply le_min
    · linarith only [mul_le_mul_of_nonneg_left b positive, b']
    · nlinarith only [mul_le_mul_of_nonneg_left c positive]
  change p*D ≤ _
  omega

/-- Summing a cost bounded by a reciprocal level gives at most four copies of
each term, using the finite row multiplicity. -/
theorem phasePrecision_harmonic {row : Finset ℕ} {levels : Finset ℕ}
    (level : ℕ → ℕ) (weight : ℕ → ℝ) (cost : ℕ → ℝ)
    (covers : ∀ p ∈ row, level p ∈ levels) (pos : ∀ j ∈ levels, 0 ≤ weight j)
    (major : ∀ p ∈ row, cost p ≤ weight (level p))
    (four : ∀ j ∈ levels, (row.filter (fun p => level p = j)).card ≤ 4) :
    ∑ p ∈ row, cost p ≤ 4*∑ j ∈ levels, weight j := by
  rw [← Finset.sum_fiberwise_of_maps_to covers, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  calc
    _ ≤ ∑ _p ∈ row.filter (fun p => level p = j), weight j := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨mem, same⟩ := Finset.mem_filter.mp hp
      simpa [same] using major p mem
    _ ≤ 4*weight j := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast four j hj) (pos j hj)

/-- The finite success bound, after inserting the prime-count estimates. -/
theorem phasePrecision_finite_bounds :
    (1511/1000:ℚ)*9*710/(22/100)^2 < 2^18 ∧
    (1511/1000:ℚ)*32*710*711/(22/100)^2 < 2^29 := by norm_num

/-- On this twin-prime example a half-width reading rounds to four throughout
an interval longer than three square-root widths. -/
theorem phasePrecision_flat_example {t : ℝ} (lo : 0 ≤ t) (hi : t ≤ 7000) :
    |2*Real.cos (2*Real.pi/4112783)+2*Real.cos (2*Real.pi*t/4112783)-4| < 1/4096 := by
  let a := 2*Real.pi/4112783
  let b := 2*Real.pi*t/4112783
  have piUpper : Real.pi ≤ 4 := Real.pi_le_four
  have a₀ : 0 ≤ a := by dsimp [a]; positivity
  have b₀ : 0 ≤ b := by dsimp [b]; positivity
  have a₁ : a ≤ 8/4112783 := by dsimp [a]; linarith
  have b₁ : b ≤ 8*7000/4112783 := by
    dsimp [b]; nlinarith only [mul_le_mul piUpper hi lo (by norm_num : (0:ℝ) ≤ 4)]
  have ca := Real.one_sub_sq_div_two_le_cos (x := a)
  have cb := Real.one_sub_sq_div_two_le_cos (x := b)
  change |2*Real.cos a+2*Real.cos b-4| < _
  apply abs_lt.mpr
  constructor
  · nlinarith only [ca, cb, sq_le_sq' (by linarith : -(8/4112783:ℝ) ≤ a) a₁,
      sq_le_sq' (by linarith : -(8*7000/4112783:ℝ) ≤ b) b₁]
  · linarith only [Real.cos_le_one a, Real.cos_le_one b]

theorem phasePrecision_flat_product : 2027*2029=4112783 ∧ 2028^2=4112783+1 ∧
    Nat.Prime 2027 ∧ Nat.Prime 2029 ∧ 9*4112783 < 7000^2 := by decide +kernel

end PrimeFactors
