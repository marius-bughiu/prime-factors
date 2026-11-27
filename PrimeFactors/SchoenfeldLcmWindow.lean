import PrimeFactors.LcmConvergentObstruction
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Using Schoenfeld's Chebyshev bound to bracket the last LCM prefix

The MIT Short GRH end-to-end release publishes `schoenfeld_strict_bound` in
Lean 4.35 with Mathlib at 56a00585. Its statement is an explicit hypothesis
here. The local Chebyshev sum uses the same interval and von Mangoldt function.
The inputs in this file are the public integer ceiling and candidate prefix
indices. They require no information about the ceiling's factors.

Upstream statement and comparison logs: <https://math.mit.edu/~drew/shortgrh/>.
The definition of ψ follows `Mathlib/NumberTheory/Chebyshev.lean` by Alastair
Irving, Terry Tao and Ruben Van de Velde (Apache 2.0), at commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The proof below uses this
project's recursive LCM and Mathlib 4.19's von Mangoldt divisor sum.
-/
namespace PrimeFactors.SchoenfeldLcmWindow

open LcmConvergentObstruction
open scoped BigOperators

/-- The Chebyshev function in the upstream bound, expressed in Lean 4.19. -/
noncomputable def psi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n

/-- Statement of the external theorem, explicit at each use. -/
def Schoenfeld : Prop :=
  ∀ x : ℝ, 73.2 ≤ x → |psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)

private theorem primePower_dvd_prefix {n j : ℕ} (h : IsPrimePow n) :
    n ∣ prefixLCM j ↔ n ≤ j := by
  constructor
  · obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff _).mp h
    induction j with
    | zero =>
      intro d
      exact (not_le.mpr h.one_lt (Nat.le_of_dvd Nat.one_pos d)).elim
    | succ j ih =>
      intro d
      rw [prefixLCM, hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero (prefix_pos j).ne'
        (Nat.succ_ne_zero j)), Nat.factorization_lcm (prefix_pos j).ne' (Nat.succ_ne_zero j)] at d
      change k ≤ max _ _ at d
      rcases le_max_iff.mp d with d|d
      · exact (ih ((hp.pow_dvd_iff_le_factorization (prefix_pos j).ne').mpr d)).trans (by omega)
      · exact Nat.le_of_dvd (Nat.succ_pos j) ((hp.pow_dvd_iff_le_factorization
          (Nat.succ_ne_zero j)).mpr d)
  · intro bound
    have direct : n ∣ prefixLCM n := by
      cases n with
      | zero => exact (h.pos.false).elim
      | succ t => exact Nat.dvd_lcm_right _ _
    exact direct.trans (prefix_dvd bound)

/-- The exact bridge from the Chebyshev sum to the project's recursive LCM. -/
theorem psi_eq_log_prefix (j : ℕ) : psi j = Real.log (prefixLCM j) := by
  classical
  have trim (s : Finset ℕ) : ∑ n ∈ s.filter IsPrimePow, ArithmeticFunction.vonMangoldt n =
      ∑ n ∈ s, ArithmeticFunction.vonMangoldt n :=
    Finset.sum_filter_of_ne fun _ _ hn => ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn
  rw [psi, Nat.floor_natCast, ← ArithmeticFunction.vonMangoldt_sum,
    ← trim (Finset.Ioc 0 j), ← trim (prefixLCM j).divisors]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
  exact ⟨fun ⟨⟨_, hj⟩, h⟩ => ⟨⟨(primePower_dvd_prefix h).mpr hj, (prefix_pos j).ne'⟩, h⟩,
         fun ⟨⟨hd, _⟩, h⟩ => ⟨⟨h.pos, (primePower_dvd_prefix h).mp hd⟩, h⟩⟩

/-- Find the unique last admissible prefix within any interval separated by
the two analytic inequalities. The weak endpoint comparisons suffice because
Schoenfeld's error is strictly bounded. -/
theorem last_in_window (bound : Schoenfeld) {N a b : ℕ} (positive : 0 < N)
    (ha : 73.2 ≤ (a : ℝ)) (hb : 73.2 ≤ (b : ℝ))
    (left : a + Real.sqrt a * Real.log a ^ 2 / (8 * Real.pi) ≤ Real.log N)
    (right : Real.log N ≤ b - Real.sqrt b * Real.log b ^ 2 / (8 * Real.pi)) :
    ∃ J : ℕ, a ≤ J ∧ J < b ∧ ∀ j, prefixLCM j ≤ N ↔ j ≤ J := by
  have low := (abs_lt.mp (bound a ha)).2
  have high := (abs_lt.mp (bound b hb)).1
  rw [psi_eq_log_prefix] at low high
  have an : prefixLCM a ≤ N := by
    exact_mod_cast ((Real.log_lt_log_iff (Nat.cast_pos.mpr (prefix_pos a))
      (Nat.cast_pos.mpr positive)).mp (by linarith : Real.log (prefixLCM a) < Real.log N)).le
  have bn : N < prefixLCM b := by
    exact_mod_cast (Real.log_lt_log_iff (Nat.cast_pos.mpr positive)
      (Nat.cast_pos.mpr (prefix_pos b))).mp (by linarith : Real.log N < Real.log (prefixLCM b))
  have below (j : ℕ) (fits : prefixLCM j ≤ N) : j < b :=
    lt_of_not_ge fun hj => (bn.trans_le ((monotone hj).trans fits)).false
  let J := Nat.findGreatest (fun j => prefixLCM j ≤ N) b
  have fitsJ : prefixLCM J ≤ N := Nat.findGreatest_spec (P := fun j => prefixLCM j ≤ N) (below a an).le an
  exact ⟨J, Nat.le_findGreatest (below a an).le an, below J fitsJ, fun j =>
    ⟨fun fits => Nat.le_findGreatest (below j fits).le fits, fun hj => (monotone hj).trans fitsJ⟩⟩

/-- A width-only test applies unchanged to every ceiling in the dyadic bin. -/
theorem width_window (bound : Schoenfeld) {w N a b : ℕ} (lo : 2^w ≤ N) (hi : N < 2^(w+1))
    (ha : 73.2 ≤ (a : ℝ)) (hb : 73.2 ≤ (b : ℝ))
    (left : a + Real.sqrt a * Real.log a ^ 2 / (8 * Real.pi) ≤ w * Real.log 2)
    (right : (w+1 : ℕ) * Real.log 2 ≤ b - Real.sqrt b * Real.log b ^ 2 / (8 * Real.pi)) :
    ∃ J : ℕ, a ≤ J ∧ J < b ∧ ∀ j, prefixLCM j ≤ N ↔ j ≤ J := by
  have pc : 0 < N := (pow_pos (by decide : 0 < (2:ℕ)) w).trans_le lo
  have low : (2:ℝ)^w ≤ N := by exact_mod_cast lo
  have high : (N:ℝ) ≤ (2:ℝ)^(w+1) := by exact_mod_cast hi.le
  have lh := Real.log_le_log (by positivity) low
  have rh := Real.log_le_log (Nat.cast_pos.mpr pc) high
  rw [Real.log_pow] at lh rh
  exact last_in_window bound pc ha hb (left.trans lh) (rh.trans right)

private theorem radius_le {x s l : ℝ} (hx : 1 ≤ x) (log_hi : Real.log x ≤ l)
    (root : Real.sqrt x ≤ s) :
    Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) ≤ s * l^2 / (8*3.14) := by
  have hs : 0 ≤ s := (Real.sqrt_nonneg x).trans root
  have hl : 0 ≤ l := (Real.log_nonneg hx).trans log_hi
  have sq := pow_le_pow_left₀ (Real.log_nonneg hx) log_hi 2
  have num := mul_le_mul root sq (sq_nonneg _) hs
  exact (div_le_div_of_nonneg_right num (by positivity)).trans
    (div_le_div_of_nonneg_left (mul_nonneg hs (sq_nonneg l)) (by norm_num)
      (by linarith [Real.pi_gt_d2]))

private theorem dyadic_log {x : ℝ} {k t : ℕ} (positive : 0 < x) (power : x^k ≤ 2^t) :
    (k : ℝ) * Real.log x ≤ t * Real.log 2 := by
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos positive _) power

set_option exponentiation.threshold 4096 in
/-- All 2048-bit caps have the last admissible prefix in [1343,1502] from
the analytic envelope alone. The independent exact LCM calculation in
`LcmConvergentObstruction.admissible` gives J = 1432. -/
theorem full_size (bound : Schoenfeld) {N : ℕ} (lo : 2^2047 ≤ N) (hi : N < 2^2048) :
    ∃ J : ℕ, 1343 ≤ J ∧ J < 1503 ∧ ∀ j, prefixLCM j ≤ N ↔ j ≤ J := by
  apply width_window bound (w := 2047) lo hi (by norm_num) (by norm_num)
  · have power := dyadic_log (x := 1343) (k := 23) (t := 239) (by norm_num) (by norm_num)
    norm_num only [Nat.cast_ofNat] at power ⊢
    have r := radius_le (x := 1343) (s := 36.65) (l := 7.203) (by norm_num)
      (by linarith [Real.log_two_lt_d9]) ((Real.sqrt_le_left (by norm_num)).mpr (by norm_num))
    linarith [Real.log_two_gt_d9]
  · have power := dyadic_log (x := 1503) (k := 9) (t := 95) (by norm_num) (by norm_num)
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at power ⊢
    have r := radius_le (x := 1503) (s := 38.77) (l := 7.317) (by norm_num)
      (by linarith [Real.log_two_lt_d9]) ((Real.sqrt_le_left (by norm_num)).mpr (by norm_num))
    linarith [Real.log_two_lt_d9]

end PrimeFactors.SchoenfeldLcmWindow
