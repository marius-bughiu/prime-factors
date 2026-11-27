import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A finite lower bound on the odd-prime weights in the larger sieve. -/
namespace PrimeFactors.IntervalSievePrimeWeights

open Finset Real

/-- Odd primes through the supplied endpoint, inclusive. -/
noncomputable def primes (Q : ℕ) : Finset ℕ := (Icc 3 Q).filter Nat.Prime

private theorem log_increment {x : ℝ} (hx : 0 < x) :
    x * (log (x+1) - log x) ≤ 1 := by
  have h := log_le_sub_one_of_pos (div_pos (by linarith : 0 < x+1) hx)
  rw [log_div (by linarith) hx.ne'] at h
  have v := mul_le_mul_of_nonneg_right h hx.le
  simp only [sub_mul, div_mul_cancel₀ _ hx.ne', one_mul] at v
  linarith

private theorem factorial_lower (Q : ℕ) (hQ : 1 ≤ Q) :
    (Q : ℝ) * (log Q - 1) ≤ log Q.factorial := by
  induction Q, hQ using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h := log_increment pos
    rw [Nat.factorial_succ, Nat.cast_mul, log_mul (by positivity) (by positivity), Nat.cast_succ]
    linarith

private noncomputable def tail (x : ℕ) : ℝ := 2 * (log x + 1) / ((x : ℝ) - 1)

private theorem correction (n : ℕ) (hn : 3 ≤ n) :
    log n / ((n : ℝ)-1) - log n / ((n : ℝ)+1) ≤ tail n - tail (n+1) := by
  have x : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have pos : (0 : ℝ) < n := by linarith
  have den : (0 : ℝ) < n-1 := by linarith
  have ln := log_nonneg (show (1 : ℝ) ≤ n by linarith)
  have less : log n / ((n : ℝ)-1) - log n / ((n : ℝ)+1) =
      2 * log n / (((n : ℝ)-1)*(n+1)) := by field_simp; ring
  rw [less]
  calc
    _ ≤ 2 * log n / (((n : ℝ)-1)*n) := by gcongr; linarith
    _ ≤ tail n - tail (n+1) := by
      unfold tail
      rw [Nat.cast_add_one, add_sub_cancel_right]
      have step := log_increment pos
      have inc := log_le_log pos (show (n : ℝ) ≤ n+1 by linarith)
      rw [le_sub_iff_add_le]
      calc
        _ = (2*log n + 2*(log (n+1)+1)*((n:ℝ)-1)) / (((n:ℝ)-1)*n) := by
          field_simp [den.ne', pos.ne']; ring
        _ ≤ (2*(log n+1)*n) / (((n:ℝ)-1)*n) := by
          apply div_le_div_of_nonneg_right _ (mul_pos den pos).le
          nlinarith
        _ = _ := by field_simp [den.ne', pos.ne']; ring

private theorem tail_nonneg {n : ℕ} (hn : 3 ≤ n) : 0 ≤ tail n := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (by linarith [log_nonneg (show (1 : ℝ) ≤ n by linarith)]) (by linarith)

private theorem correction_nonneg {n : ℕ} (hn : 3 ≤ n) :
    0 ≤ log n / ((n : ℝ)-1) - log n / ((n : ℝ)+1) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  apply sub_nonneg.mpr
  gcongr <;> first | exact log_nonneg (by linarith) | linarith

private theorem tail_sum (b : ℕ) (hb : 3 ≤ b) :
    ∑ n ∈ Ico 3 b, (tail n - tail (n+1)) = tail 3 - tail b := by
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [sum_Ico_succ_top hn, ih]; ring

private theorem comparison (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ p ∈ primes Q, log p / ((p : ℝ)-1)) ≤
      (∑ p ∈ primes Q, log p / ((p : ℝ)+1)) + tail 3 := by
  suffices h : (∑ p ∈ primes Q, log p / ((p : ℝ)-1)) -
      (∑ p ∈ primes Q, log p / ((p : ℝ)+1)) ≤ tail 3 by linarith
  rw [← sum_sub_distrib]
  have sub : primes Q ⊆ Ico 3 (Q+1) := by
    intro p hm
    obtain ⟨bounds, _⟩ := mem_filter.mp hm
    exact mem_Ico.mpr ⟨(mem_Icc.mp bounds).1, Nat.lt_succ_of_le (mem_Icc.mp bounds).2⟩
  calc
    _ ≤ ∑ p ∈ Ico 3 (Q+1), (log p / ((p : ℝ)-1) - log p / ((p : ℝ)+1)) :=
      sum_le_sum_of_subset_of_nonneg sub (fun p hm _ => correction_nonneg (mem_Ico.mp hm).1)
    _ ≤ ∑ p ∈ Ico 3 (Q+1), (tail p - tail (p+1)) :=
      sum_le_sum fun p hm => correction p (mem_Ico.mp hm).1
    _ ≤ _ := by rw [tail_sum _ (by omega)]; linarith [tail_nonneg (n:=Q+1) (by omega)]

private theorem factorial_upper (Q : ℕ) (hQ : 2 ≤ Q) :
    log Q.factorial ≤ Q * (log 2 + ∑ p ∈ primes Q, log p / ((p : ℝ)-1)) := by
  have factors : Q.factorial.primeFactors = insert 2 (primes Q) := by
    ext p
    rw [Nat.mem_primeFactors, mem_insert, primes, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hp, div, _⟩
      have lo := hp.two_le
      have hi := hp.dvd_factorial.mp div
      by_cases two : p = 2
      · exact Or.inl two
      · exact Or.inr ⟨⟨by omega, hi⟩, hp⟩
    · rintro (rfl | ⟨⟨_, hi⟩, hp⟩)
      · exact ⟨Nat.prime_two, Nat.prime_two.dvd_factorial.mpr hQ, Nat.factorial_ne_zero _⟩
      · exact ⟨hp, hp.dvd_factorial.mpr hi, Nat.factorial_ne_zero _⟩
  have localBound (p : ℕ) (hp : p ∈ Q.factorial.primeFactors) :
      (Q.factorial.factorization p : ℝ) * log p ≤ (Q : ℝ) * (log p / ((p : ℝ)-1)) := by
    have prime := Nat.prime_of_mem_primeFactors hp
    letI : Fact p.Prime := ⟨prime⟩
    have big := prime.two_le
    have big' : (2 : ℝ) ≤ p := by exact_mod_cast big
    have den : (0 : ℝ) < p-1 := by linarith
    have valuation : (p-1) * Q.factorial.factorization p ≤ Q := by
      rw [Nat.factorization_def _ prime, sub_one_mul_padicValNat_factorial]
      exact Nat.sub_le _ _
    have cast : ((p : ℝ)-1) * Q.factorial.factorization p ≤ Q := by
      rw [← Nat.cast_one (R:=ℝ), ← Nat.cast_sub (show 1 ≤ p by omega)]
      exact_mod_cast valuation
    rw [← mul_div_assoc]
    apply (le_div_iff₀ den).mpr
    nlinarith [mul_le_mul_of_nonneg_right cast (log_nonneg (show (1:ℝ)≤p by linarith))]
  rw [log_nat_eq_sum_factorization]
  change (∑ p ∈ Q.factorial.primeFactors, _) ≤ _
  calc
    _ ≤ ∑ p ∈ Q.factorial.primeFactors, (Q : ℝ) * (log p / ((p : ℝ)-1)) := sum_le_sum localBound
    _ = _ := by
      rw [← mul_sum, factors, sum_insert (by simp [primes])]
      norm_num

/-- For every finite endpoint the explicit loss is at most four natural logarithm units. -/
theorem lower {Q : ℕ} (hQ : 2 ≤ Q) :
    log Q - 4 ≤ ∑ p ∈ primes Q, log p / ((p : ℝ)+1) := by
  have pos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have lowerBound := factorial_lower Q (by omega)
  have upperBound := factorial_upper Q hQ
  have divide := (mul_le_mul_iff_of_pos_left pos).mp (lowerBound.trans upperBound)
  have comp := comparison Q hQ
  have two := Real.log_two_lt_d9
  have three := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3/2)
  rw [log_div (by norm_num) (by norm_num)] at three
  norm_num [tail] at comp
  linarith

/-- In particular a dyadic endpoint loses at most six binary logarithm units. -/
theorem dyadic {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℝ)-6) * log 2 ≤ ∑ p ∈ primes (2^k), log p / ((p : ℝ)+1) := by
  have h := lower (Q:=2^k) (by simpa using Nat.pow_le_pow_right (by decide : 0<2) hk)
  rw [Nat.cast_pow, Nat.cast_ofNat, log_pow] at h
  linarith [Real.log_two_gt_d9]

end PrimeFactors.IntervalSievePrimeWeights
