import PrimeFactors.QuotientStripWideSlopeGeometry
import PrimeFactors.QuotientStripTailCost

namespace PrimeFactors.QuotientStripSlopeAlignment
open QuotientStripScheduleCost QuotientStripWideSlopeGeometry

set_option exponentiation.threshold 4096

/-- Two-sided comparability of the rounded sixth root cubed and the real square root. -/
theorem rounded_comparability {n : ℕ} (lo : 2^2047 ≤ n) (hi : n < 2^2048) :
    (roundedSixth n : ℝ)^3 ≤ 2 * Real.sqrt n ∧
    Real.sqrt n ≤ 2 * (roundedSixth n : ℝ)^3 := by
  classical
  obtain ⟨sqrtLo, _, rlo, _⟩ := QuotientStripTailCost.root_bounds lo hi
  have rhi : roundedSixth n ≤ 21 * 2^337 := by
    unfold roundedSixth
    apply Nat.find_min'
    exact ⟨by decide, (Nat.mul_le_mul_left 64 hi.le).trans (by decide +kernel)⟩
  have h₁ : (roundedSixth n)^3 ≤ 2*n.sqrt :=
    (Nat.pow_le_pow_left rhi 3).trans ((by decide +kernel :
      (21*2^337)^3 ≤ 2*(11*2^1020)).trans (Nat.mul_le_mul_left 2 sqrtLo))
  have h₂ : 2^1024 ≤ 2*(roundedSixth n)^3 :=
    (by decide +kernel : 2^1024 ≤ 2*(2^341)^3).trans
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left rlo 3))
  have sq : (n.sqrt : ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' n)
  have upper : Real.sqrt (n:ℝ) ≤ 2^1024 := Real.sqrt_le_iff.mpr ⟨by positivity, by
    exact_mod_cast (hi.le.trans (by decide +kernel : 2^2048 ≤ (2^1024)^2))⟩
  exact ⟨(show (roundedSixth n : ℝ)^3 ≤ 2*(n.sqrt:ℝ) by exact_mod_cast h₁).trans
    (mul_le_mul_of_nonneg_left sq (by norm_num)), upper.trans (by exact_mod_cast h₂)⟩

/-- Consecutive full blocks covering the interior of a sufficiently wide real interval. -/
theorem align_grid {f w t L : ℝ} (hp : 0 < w) (space : f ≤ t-L) (wide : 2*w ≤ L) :
    ∃ i k : ℕ, f+i*w ≤ t-L+w ∧ t-2*w ≤ f+(i+k:ℕ)*w+w-1 ∧
      ∀ j ≤ k, t-L ≤ f+(i+j:ℕ)*w ∧ f+(i+j:ℕ)*w+w-1 ≤ t := by
  let i := ⌈(t-L-f)/w⌉₊
  have il : t-L-f ≤ (i:ℝ)*w := (div_le_iff₀ hp).mp (Nat.le_ceil _)
  have iu : (i:ℝ)*w < t-L-f+w := by
    have b := Nat.ceil_lt_add_one (div_nonneg (by linarith : 0≤t-L-f) hp.le)
    have b' := mul_lt_mul_of_pos_right b hp
    rwa [add_mul, div_mul_cancel₀ _ hp.ne', one_mul] at b'
  let k := ⌊(t-f-i*w-w+1)/w⌋₊
  have kl : (k:ℝ)*w ≤ t-f-i*w-w+1 := (le_div_iff₀ hp).mp
    (Nat.floor_le (div_nonneg (by linarith) hp.le))
  have ku : t-f-i*w-w+1 < ((k:ℝ)+1)*w := (div_lt_iff₀ hp).mp (Nat.lt_floor_add_one _)
  refine ⟨i,k,by linarith,?_,?_⟩
  · push_cast
    nlinarith only [ku,hp]
  · intro j hj
    have h := mul_le_mul_of_nonneg_right (show (j:ℝ)≤k by exact_mod_cast hj) hp.le
    have z : 0 ≤ (j:ℝ)*w := by positivity
    push_cast
    constructor <;> nlinarith only [il,kl,h,z]

end PrimeFactors.QuotientStripSlopeAlignment
