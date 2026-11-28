import PrimeFactors.CyclotomicLogUpper

/-! A reference reading from the public product and a degree cutoff.
Below N the formal log coefficients can be replaced by ordinary gcds.
The dense approximation is specified in exact real arithmetic. -/
namespace PrimeFactors.PublicCyclotomicLogReading

open Finset Real CyclotomicLogTail CyclotomicProductCurve

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

noncomputable def dense (N B K : ℕ) : ℝ := exp (-∑ m∈Icc 1 K,
  (if N.gcd m=1 then 0 else (N.gcd m:ℝ)) * exp (-((m:ℝ)/(8*B)))/m)

theorem agrees {p q B K : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q) (before : K<p*q) :
    dense (p*q) B K=approx B p q K := by
  rw [dense,approx,←dense_prefix hp hq order]
  congr 2
  apply sum_congr rfl
  intro m hm
  obtain ⟨pos,bound⟩ := mem_Icc.mp hm
  have proper : ¬ p*q∣m := fun h => Nat.not_le_of_gt (bound.trans_lt before) (Nat.le_of_dvd pos h)
  rw [CyclotomicLogCoefficients.at_proper hp hq order pos proper]
  split_ifs <;> push_cast <;> rfl

private theorem past_cutoff {p q : ℕ} (lo : 2^1023≤p) (order : p<q) :
    5768*2^1023 < p*q := by
  have big : 5768 < (2:ℕ)^1023 := by decide +kernel
  have pos : 0<(2:ℕ)^1023 := by positivity
  exact (Nat.mul_lt_mul_of_pos_right big pos).trans_le (Nat.mul_le_mul lo (lo.trans order.le))

theorem insufficient {p q K : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q)
    (lo : 2^1023≤p) (hi : q<2^1024) (cut : K≤2^1034) :
    1/(8192*(2:ℝ)^1023)<dense (p*q) (2^1023) K-reading (p*q) ((2:ℝ)^1023) := by
  have upper : K≤5768*2^1023 := cut.trans (by decide +kernel)
  rw [agrees hp hq order (upper.trans_lt (past_cutoff lo order))]
  exact CyclotomicLogTail.full_width hp hq order lo hi cut

/-- This explicit cutoff stays below the product. Only public gcds and
elementary real values occur on the input side of the inequality. -/
theorem sufficient {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q) (lo : 2^1023≤p) :
    |dense (p*q) (2^1023) (5768*2^1023)-reading (p*q) ((2:ℝ)^1023)| <
      1/(8192*(2:ℝ)^1023) := by
  rw [agrees hp hq order (past_cutoff lo order)]
  exact CyclotomicLogUpper.full_width hp hq order lo le_rfl

end PrimeFactors.PublicCyclotomicLogReading
