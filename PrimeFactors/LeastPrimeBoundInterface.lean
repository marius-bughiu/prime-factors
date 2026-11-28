import PrimeFactors.Subgroup
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Convert a real bound on a prime outside a proper subgroup to an
integer bound. The analytic least-prime theorem is an explicit argument.
The threshold and prime-divisor bounds for the full-width case are elementary. -/
namespace PrimeFactors.LeastPrimeBoundInterface

open Real
set_option exponentiation.threshold 4096

/-- The fixed-modulus witness property with a real cutoff. -/
def RealOutside (n : ℕ) (x : ℝ) : Prop :=
  ∀ H : Subgroup (ZMod n)ˣ, H≠⊤ →
    ∃ a : ℕ, a.Prime ∧ ∃ h : a.Coprime n, ZMod.unitOfCoprime a h∉H ∧ (a:ℝ)≤x

/-- A nonnegative real cutoff gives exactly the same integer witnesses as its floor. -/
theorem floor_iff {n : ℕ} {x : ℝ} (nonneg : 0≤x) :
    RealOutside n x ↔ SmallPrimeOutside n ⌊x⌋₊ := by
  constructor <;> intro property H proper
  · obtain ⟨a,prime,cop,miss,le⟩ := property H proper
    exact ⟨a,prime,(Nat.le_floor_iff nonneg).mpr le,cop,miss⟩
  · obtain ⟨a,prime,le,cop,miss⟩ := property H proper
    exact ⟨a,prime,cop,miss,(Nat.le_floor_iff nonneg).mp le⟩

private theorem log_lt_width {n k : ℕ} (pos : 0<n) (width : n<2^k) :
    log n < (k:ℝ)*log 2 := by
  have lt := Real.log_lt_log (by exact_mod_cast pos : 0<(n:ℝ))
    (by exact_mod_cast width : (n:ℝ)<(2:ℝ)^k)
  rwa [Real.log_pow] at lt

theorem log_sq_le_size_sq (n : ℕ) : log n ^ 2 ≤ (n.size:ℝ)^2 := by
  rcases n.eq_zero_or_pos with zero|pos
  · simp [zero]
  have bound := (log_lt_width pos (Nat.lt_size_self n)).le
  have log_two : log 2 ≤ (1:ℝ) := by linarith only [Real.log_two_lt_d9]
  have scaled := mul_le_mul_of_nonneg_left log_two (Nat.cast_nonneg n.size : (0:ℝ)≤n.size)
  rw [mul_one] at scaled
  exact pow_le_pow_left₀ (Real.log_natCast_nonneg n) (bound.trans scaled) 2

/-- The bit-length-squared cutoff used by the local subgroup interface. -/
theorem at_size {n : ℕ} (outside : RealOutside n (log n ^ 2)) :
    SmallPrimeOutside n (n.size^2) := by
  intro H proper
  obtain ⟨a,prime,cop,miss,le⟩ := outside H proper
  exact ⟨a,prime,by exact_mod_cast le.trans (log_sq_le_size_sq n),cop,miss⟩

/-- The real cutoff lies strictly below 2,015,166 throughout the 2048-bit range. -/
theorem full_log_bound {n : ℕ} (width : n<2^2048) : log n ^ 2 < 2015166 := by
  rcases n.eq_zero_or_pos with zero|pos
  · simp [zero]
  have lt : log n < (2048:ℝ)*log 2 := by exact_mod_cast log_lt_width pos width
  have top := lt.trans (mul_lt_mul_of_pos_left Real.log_two_lt_d9 (by norm_num : (0:ℝ)<2048))
  exact (pow_lt_pow_left₀ top (Real.log_natCast_nonneg n) (by decide : (2:ℕ)≠0)).trans
    (by norm_num)

/-- Prime factors of a product of two large primes automatically exceed
the squared logarithm required in LLS Theorem 1.1(2). -/
theorem full_rough {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (width : p*q<2^2048) :
    3000≤p*q ∧ ∀ r : ℕ, r.Prime → r∣p*q → log (p*q:ℕ)^2≤(r:ℝ) := by
  have size : 3000≤p := (by decide +kernel : 3000≤2^1023).trans pl
  refine ⟨size.trans (Nat.le_mul_of_pos_right p qp.pos),?_⟩
  intro r rp divides
  have big : 2^1023≤r := by
    rcases rp.dvd_mul.mp divides with left|right
    · rwa [(Nat.prime_dvd_prime_iff_eq rp pp).mp left]
    · rwa [(Nat.prime_dvd_prime_iff_eq rp qp).mp right]
  have cap : 2015166≤r := (by decide +kernel : 2015166≤2^1023).trans big
  exact (full_log_bound width).le.trans (by exact_mod_cast cap)

/-- Specialize a supplied least-prime theorem at the fixed product.
The prime returned at the real cutoff is at most 2,015,165. -/
theorem full_size {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (width : p*q<2^2048)
    (least : 3000≤p*q → (∀ r : ℕ,r.Prime → r∣p*q → log (p*q:ℕ)^2≤(r:ℝ)) →
      RealOutside (p*q) (log (p*q:ℕ)^2)) :
    SmallPrimeOutside (p*q) 2015165 := by
  obtain ⟨size,rough⟩ := full_rough pp qp pl ql width
  intro H proper
  obtain ⟨a,prime,cop,miss,le⟩ := least size rough H proper
  have lt : a<2015166 := by exact_mod_cast le.trans_lt (full_log_bound width)
  exact ⟨a,prime,by omega,cop,miss⟩

end PrimeFactors.LeastPrimeBoundInterface
