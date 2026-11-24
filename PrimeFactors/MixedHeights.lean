import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace PrimeFactors

/-- Frequencies of a nonadaptive experiment. All heights are integers. -/
noncomputable def mixedHeights (K : ℕ) : Finset ℕ :=
  let I := Finset.range (K + 1)
  (I.image (2 ^ ·)) ∪ ((I ×ˢ I).image fun ij => 2 ^ ij.1 + 2 ^ ij.2)

theorem mixedHeights_card_le (K : ℕ) :
    (mixedHeights K).card ≤ K + 1 + (K + 1) ^ 2 := by
  unfold mixedHeights
  refine (Finset.card_union_le _ _).trans ?_
  simpa [pow_two] using Nat.add_le_add
    (Finset.card_image_le (s := Finset.range (K+1)) (f := fun i => (2:ℕ)^i))
    (Finset.card_image_le (s := Finset.range (K+1) ×ˢ Finset.range (K+1))
      (f := fun ij : ℕ × ℕ => (2:ℕ)^ij.1 + 2^ij.2))

private theorem find_phase_band (K : ℕ) {x : ℝ} (small : x ≤ Real.pi / 3)
    (reaches : Real.pi / 6 ≤ 2 ^ K * x) :
    ∃ k ≤ K, Real.pi / 6 ≤ 2 ^ k * x ∧ 2 ^ k * x ≤ Real.pi / 3 := by
  induction K with
  | zero => exact ⟨0, le_rfl, reaches, by simpa using small⟩
  | succ K ih =>
    by_cases previous : Real.pi / 6 ≤ 2 ^ K * x
    · obtain ⟨i, hi, h⟩ := ih previous
      exact ⟨i, Nat.le_succ_of_le hi, h⟩
    · refine ⟨K + 1, le_rfl, reaches, ?_⟩
      rw [pow_succ]
      linarith

private theorem sin_band {x : ℝ} (lo : Real.pi / 6 ≤ x) (hi : x ≤ 2 * Real.pi / 3) :
    1 / 2 ≤ Real.sin x := by
  rw [← Real.sin_pi_div_six]
  have start : -(Real.pi / 2) ≤ Real.pi / 6 := by linarith [Real.pi_pos]
  by_cases half : x ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two start half lo
  · rw [← Real.sin_pi_sub x]
    apply Real.sin_le_sin_of_le_of_le_pi_div_two start <;> linarith [Real.pi_pos]

private theorem sin_separated {x h : ℝ} (shift : 1 / 2 ≤ Real.sin h) :
    1 / 4 ≤ |Real.sin x| ∨ 1 / 4 ≤ |Real.sin (x+h)| := by
  have bound : |Real.sin h| ≤ |Real.sin (x+h)| + |Real.sin x| := by
    calc
      _ = |Real.sin (x+h) * Real.cos x - Real.cos (x+h) * Real.sin x| := by
        rw [← Real.sin_sub, add_sub_cancel_left]
      _ ≤ _ := (abs_sub _ _).trans (by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (by simpa using mul_le_mul_of_nonneg_left (abs_le.mpr
            ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩) (abs_nonneg (Real.sin (x+h))))
          (by simpa using mul_le_mul_of_nonneg_right (abs_le.mpr
            ⟨Real.neg_one_le_cos (x+h), Real.cos_le_one (x+h)⟩) (abs_nonneg (Real.sin x))))
  by_contra! small
  linarith [le_abs_self (Real.sin h)]

private theorem cos_gap {t m d : ℝ} (mid : 1 / 4 ≤ |Real.sin (t*m)|)
    (gap : 1 / 2 ≤ Real.sin (t*d)) :
    1 / 4 ≤ |Real.cos (t*(m-d)) - Real.cos (t*(m+d))| := by
  rw [mul_sub, mul_add, Real.cos_sub, Real.cos_add,
    show ∀ a b : ℝ, a+b-(a-b) = 2*b by intros; ring, abs_mul, abs_mul]
  have half : 1/2 ≤ |Real.sin (t*d)| := gap.trans (le_abs_self _)
  have prod := mul_le_mul mid half (by norm_num) (abs_nonneg _)
  norm_num
  linarith

/-- Any two log-ratios separated by at least π/(3·2^K) differ at one
preselected height by at least one quarter, also near zero. -/
theorem mixedHeights_separate {K : ℕ} {u v : ℝ}
    (low : 0 ≤ u) (ordered : u ≤ v) (high : v ≤ Real.pi / 6)
    (gap : Real.pi / 6 ≤ 2 ^ K * ((v-u)/2)) :
    ∃ t ∈ mixedHeights K, 1/4 ≤ |Real.cos (t*u) - Real.cos (t*v)| := by
  let d := (v-u)/2
  let m := (v+u)/2
  have d₀ : 0 ≤ d := by dsimp [d]; linarith
  have dm : d ≤ m := by dsimp [d,m]; linarith
  have mhi : m ≤ Real.pi / 3 := by dsimp [m]; linarith [Real.pi_pos]
  obtain ⟨k, hk, dk, dk'⟩ := find_phase_band K (dm.trans mhi) gap
  obtain ⟨j, hj, mj, mj'⟩ := find_phase_band k mhi
    (dk.trans (mul_le_mul_of_nonneg_left dm (by positivity)))
  let t : ℝ := 2^k
  let h : ℝ := 2^j
  have ht : h ≤ t := by
    dsimp [h,t]
    exact pow_le_pow_right₀ (by norm_num) hj
  have hu : u = m-d := by dsimp [m,d]; ring
  have hv : v = m+d := by dsimp [m,d]; ring
  have shifted := sin_separated (x := t*m) (h := h*m) (sin_band mj (by linarith [Real.pi_pos]))
  rcases shifted with first | mixed
  · refine ⟨2^k, Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨k, Finset.mem_range.mpr (by omega), rfl⟩), ?_⟩
    push_cast
    rw [hu, hv]
    exact cos_gap first (sin_band dk (by linarith [Real.pi_pos]))
  · refine ⟨2^k+2^j, Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(k,j), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Finset.mem_range.mpr (by omega)⟩, rfl⟩), ?_⟩
    change 1/4 ≤ |Real.sin (t*m+h*m)| at mixed
    rw [← add_mul] at mixed
    have hd₀ : 0 ≤ h*d := mul_nonneg (by dsimp [h]; positivity) d₀
    have hd : h*d ≤ t*d := mul_le_mul_of_nonneg_right ht d₀
    change Real.pi/6 ≤ t*d at dk
    change t*d ≤ Real.pi/3 at dk'
    have good := sin_band (show Real.pi/6 ≤ (t+h)*d by rw [add_mul]; linarith)
      (show (t+h)*d ≤ 2*Real.pi/3 by rw [add_mul]; linarith)
    push_cast
    rw [hu,hv]
    exact cos_gap mixed good

/-- With noise at most 1/10 in each wave sample, one transcript cannot
fit two separated inputs. This applies to a continuous relaxation. -/
theorem mixedHeights_resolution {K : ℕ} {u v : ℝ} (low : 0 ≤ u) (ordered : u ≤ v)
    (high : v ≤ Real.pi / 6) (y : ℕ → ℝ)
    (fitU : ∀ t ∈ mixedHeights K, |Real.cos (t*u)-y t| ≤ 1/10)
    (fitV : ∀ t ∈ mixedHeights K, |Real.cos (t*v)-y t| ≤ 1/10) :
    2 ^ K * ((v-u)/2) < Real.pi/6 := by
  by_contra! overlap
  obtain ⟨t, ht, far⟩ := mixedHeights_separate low ordered high overlap
  have near := abs_sub_le (Real.cos (t*u)) (y t) (Real.cos (t*v))
  rw [abs_sub_comm (y t)] at near
  linarith [fitU t ht, fitV t ht]

/-- A fixed pair of positive log-ratios under one half. Even infinitely
many unshifted dyadic heights cannot distinguish them with error 1/128. -/
theorem dyadic_reflection_alias (k : ℕ) :
    |Real.cos (2^k * (Real.pi/16 - 1/1024)) -
      Real.cos (2^k * (Real.pi/16 + 1/1024))| ≤ 1/64 := by
  rw [mul_sub, mul_add, Real.cos_sub, Real.cos_add,
    show ∀ a b : ℝ, a+b-(a-b) = 2*b by intros; ring, abs_mul, abs_mul]
  by_cases early : k < 4
  · have bound : (2 : ℝ)^k ≤ 2^3 := pow_le_pow_right₀ (by norm_num) (by omega)
    have slope := Real.abs_sin_le_abs (x := (2 : ℝ)^k * (1/1024))
    rw [abs_of_nonneg (show 0 ≤ (2 : ℝ)^k * (1/1024) by positivity)] at slope
    have unit : |Real.sin ((2 : ℝ)^k * (Real.pi/16))| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have prod := mul_le_mul_of_nonneg_right unit (abs_nonneg (Real.sin ((2:ℝ)^k * (1/1024))))
    norm_num at bound ⊢
    linarith
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (by omega : 4 ≤ k)
    have phase : (2 : ℝ)^k * (Real.pi/16) = ((2^j : ℕ) : ℝ) * Real.pi := by
      rw [hj, pow_add]
      push_cast
      ring
    rw [phase, Real.sin_nat_mul_pi]
    norm_num

end PrimeFactors
