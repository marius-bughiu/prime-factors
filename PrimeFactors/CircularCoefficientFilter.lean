import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# Reading a divisor sum by sampling on a circle

Equally spaced samples preserve every coefficient in one congruence class.
For the divisor-sum series, even removing all terms with a small divisor or a
small cofactor leaves large coefficients on either side of a full-size target.

The geometric-sum filter is classical. For the numerical setting see Folkmar
Bornemann, *Accuracy and Stability of Computing High-Order Derivatives of Analytic
Functions by Cauchy Integrals*, https://doi.org/10.1007/s10208-010-9075-z .
The finite arithmetic bounds below are independent of analytic hypotheses.
-/

namespace PrimeFactors.CircularCoefficientFilter

open Finset

private theorem kernel {M : ℕ} {z : ℂ} (hz : IsPrimitiveRoot z M) (e : ℕ) :
    ∑ j ∈ range M, (z ^ e) ^ j = if M ∣ e then (M : ℂ) else 0 := by
  by_cases m : M ∣ e
  · simp [m, (hz.pow_eq_one_iff_dvd e).mpr m]
  · rw [if_neg m, geom_sum_eq (fun h => m ((hz.pow_eq_one_iff_dvd e).mp h))]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow, sub_self, zero_div]

/-- Choose s congruent to −N modulo M to retain every exponent congruent to N. -/
theorem finite_filter {M : ℕ} {z : ℂ} (hz : IsPrimitiveRoot z M)
    (S : Finset ℕ) (a : ℕ → ℂ) (r : ℂ) (s : ℕ) :
    ∑ j ∈ range M, (z ^ j) ^ s * (∑ n ∈ S, a n * (r * z ^ j) ^ n) =
      (M : ℂ) * ∑ n ∈ S.filter (fun n => M ∣ n + s), a n * r ^ n := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  calc
    _ = ∑ j ∈ range M, (a n * r ^ n) * (z ^ (n + s)) ^ j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← pow_mul z j s, mul_pow, ← pow_mul z j n, ← pow_mul z (n + s) j,
        Nat.add_mul, pow_add, Nat.mul_comm j s, Nat.mul_comm j n]
      ring
    _ = _ := by
      rw [← Finset.mul_sum, kernel hz]
      split_ifs <;> ring

/-- Keep a divisor only when both it and its cofactor exceed B. -/
noncomputable def retained (B n : ℕ) : ℕ :=
  (n.divisors.filter (fun w => B < w ∧ B < n / w)).sum id

theorem retained_mul {B d w : ℕ} (hd : B < d) (hw : B < w) :
    w ≤ retained B (d * w) := by
  have hwp : 0 < w := by omega
  have hdp : 0 < d := by omega
  apply Finset.single_le_sum (f := id) (fun x _ => Nat.zero_le x)
  refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_mul_left w d, by positivity⟩, hw, ?_⟩
  simpa [Nat.mul_div_cancel _ hwp] using hd

/-- At the product of two distinct primes above the cutoff the coefficient is their sum. -/
theorem target {p q B : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p ≠ q)
    (bp : 1 ≤ B) (pb : B < p) (qb : B < q) : retained B (p * q) = p + q := by
  have nz : p * q ≠ 0 := Nat.mul_ne_zero hp.ne_zero hq.ne_zero
  have hf : (p * q).divisors.filter (fun w => B < w ∧ B < (p * q) / w) = {p, q} := by
    ext w
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨dvd, _⟩, bw, wb⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.mp dvd
      rcases (Nat.dvd_prime hp).mp ha with rfl | rfl <;>
        rcases (Nat.dvd_prime hq).mp hb with rfl | rfl <;> simp_all
      rw [Nat.div_self (Nat.mul_pos hp.pos hq.pos)] at wb
      omega
    · rintro (h | h) <;> subst w
      · exact ⟨⟨dvd_mul_right p q, nz⟩, pb, by simpa [Nat.mul_div_cancel_left _ hp.pos] using qb⟩
      · exact ⟨⟨dvd_mul_left q p, nz⟩, qb, by simpa [Nat.mul_div_cancel _ hq.pos] using pb⟩
  simp [retained, hf, diff]

/-- In either direction from N, at most d steps of size M suffice to reach a multiple
of d when d = 1 + sM. -/
theorem neighbours {N M s d : ℕ} (shape : d = 1 + s * M) (room : d * M ≤ N) :
    ∃ j k : ℕ, 1 ≤ j ∧ j ≤ d ∧ 1 ≤ k ∧ k ≤ d ∧ d ∣ N - j * M ∧ d ∣ N + k * M := by
  have dp : 0 < d := by omega
  let r := (N * s) % d
  have hr : r < d := Nat.mod_lt _ dp
  let k := if r = 0 then d else r
  have hk : 1 ≤ k ∧ k ≤ d := by
    dsimp [k]
    split_ifs <;> omega
  have dr : (d : ZMod d) = 0 := ZMod.natCast_self d
  have cr : (r : ZMod d) = (N : ZMod d) * s := by simp [r]
  have ck : (k : ZMod d) = (N : ZMod d) * s := by
    dsimp [k]
    split_ifs with h
    · rw [← cr, h]
      simp [dr]
    · exact cr
  have cd : (1 : ZMod d) + (s : ZMod d) * M = 0 := by
    simpa only [shape, Nat.cast_add, Nat.cast_one, Nat.cast_mul] using dr
  refine ⟨d - r, k, by omega, Nat.sub_le .., hk.1, hk.2, ?_, ?_⟩
  · apply (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp
    rw [Nat.cast_sub (le_trans (Nat.mul_le_mul_right M (Nat.sub_le d r)) room),
      Nat.cast_mul, Nat.cast_sub hr.le, dr, cr]
    linear_combination (N : ZMod d) * cd
  · apply (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp
    rw [Nat.cast_add, Nat.cast_mul, ck]
    linear_combination (N : ZMod d) * cd

/-- Two coefficients in the same congruence class have large surviving divisors. -/
theorem nearby_retained {B N M : ℕ} (bp : 1 ≤ B) (mp : 1 ≤ M)
    (space : (B + M) * (B + M) < N) :
    ∃ d j k w v : ℕ, B < d ∧ d ≤ B + M ∧ 1 ≤ j ∧ j ≤ d ∧ 1 ≤ k ∧ k ≤ d ∧
      N - j * M = d * w ∧ N + k * M = d * v ∧ B < w ∧ B < v ∧
      w ≤ retained B (N - j * M) ∧ v ≤ retained B (N + k * M) := by
  let s := (B - 1) / M + 1
  let d := 1 + s * M
  have hd : B < d ∧ d ≤ B + M := by
    have h1 := Nat.mod_add_div (B - 1) M
    have h2 := Nat.mod_lt (B - 1) (by omega : 0 < M)
    dsimp [d, s]
    rw [Nat.add_mul, one_mul, Nat.mul_comm ((B - 1) / M)]
    omega
  have hm := Nat.mul_le_mul_right (B + M) hd.2
  have hM : d * M ≤ d * (B + M) := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨j, k, hj, ju, hk, ku, ⟨w, hw⟩, ⟨v, hv⟩⟩ :=
    neighbours (N := N) (M := M) (s := s) (d := d) rfl (by omega)
  have jm := Nat.mul_le_mul_right M ju
  rw [Nat.mul_add] at hm
  have wb : B < w := Nat.lt_of_mul_lt_mul_left (by omega : d * B < d * w)
  have vb : B < v := Nat.lt_of_mul_lt_mul_left (by omega : d * B < d * v)
  exact ⟨d, j, k, w, v, hd.1, hd.2, hj, ju, hk, ku, hw, hv, wb, vb,
    hw ▸ retained_mul hd.1 wb, hv ▸ retained_mul hd.1 vb⟩

/-- A grid and divisor cutoff bounded by 2^40 leave these coefficients within 2^81
positions on either side of every 2048-bit input. -/
theorem full_size {N B M : ℕ} (width : 2 ^ 2047 ≤ N) (bp : 1 ≤ B) (bmax : B ≤ 2 ^ 40)
    (mp : 1 ≤ M) (mmax : M ≤ 2 ^ 40) :
    ∃ j k : ℕ, 1 ≤ j ∧ j * M ≤ 2 ^ 81 ∧ 1 ≤ k ∧ k * M ≤ 2 ^ 81 ∧
      2 ^ 2005 < retained B (N - j * M) ∧ 2 ^ 2006 ≤ retained B (N + k * M) := by
  have sum_le : B + M ≤ 2 ^ 41 := by omega
  have room := Nat.mul_le_mul sum_le sum_le
  obtain ⟨d, j, k, w, v, _, du, hj, ju, hk, ku, hw, hv, _, _, wl, vl⟩ :=
    nearby_retained bp mp (by omega : (B + M) * (B + M) < N)
  have dcap := le_trans du sum_le
  have jm := Nat.mul_le_mul (le_trans ju dcap) mmax
  have km := Nat.mul_le_mul (le_trans ku dcap) mmax
  refine ⟨j, k, hj, by simpa using jm, hk, by simpa using km, ?_, ?_⟩
  · by_contra! bad
    have := Nat.mul_le_mul dcap (le_trans wl bad)
    omega
  · by_contra! bad
    have := Nat.mul_le_mul dcap (show v ≤ 2 ^ 2006 - 1 by omega)
    omega

/-- Normalizing the sum by r^N gives an earlier nonnegative coefficient at least
its original weight. -/
theorem earlier_term {N h a : ℕ} {r : ℝ} (rp : 0 < r) (r1 : r ≤ 1) :
    (a : ℝ) ≤ (a * r ^ (N - h)) / r ^ N := by
  apply (le_div_iff₀ (pow_pos rp N)).mpr
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one rp.le r1 (Nat.sub_le N h)) (by positivity)

/-- A positive upper coefficient forces damping at distance h. If evaluating each
sample with absolute error at most 2^(-b) is to give a worst-case certificate,
the normalization also constrains r^N. -/
theorem precision {N h b c K : ℕ} {r : ℝ} (rp : 0 < r) (r1 : r ≤ 1)
    (kp : 0 < K) (depth : h * K ≤ N)
    (damping : r ^ h * 2 ^ c < 1) (accuracy : 1 < r ^ N * 2 ^ b) : c * K < b := by
  have fall : r ^ N ≤ r ^ (h * K) := pow_le_pow_of_le_one rp.le r1 depth
  have small : r ^ (h * K) * 2 ^ (c * K) < 1 := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact pow_lt_one₀ (by positivity) damping kp.ne'
  by_cases bad : b ≤ c * K
  · have grow : (2 : ℝ) ^ b ≤ 2 ^ (c * K) := pow_le_pow_right₀ (by norm_num) bad
    have contrad := mul_le_mul fall grow (by positivity) (by positivity)
    linarith
  · omega

theorem full_precision {N h b : ℕ} {r : ℝ} (rp : 0 < r) (r1 : r ≤ 1)
    (width : 2 ^ 2047 ≤ N) (near : h ≤ 2 ^ 81)
    (upper_term : (2 : ℝ) ^ 2006 * r ^ h < 1 / 2)
    (accuracy : 1 < r ^ N * 2 ^ b) : 2007 * 2 ^ 1966 < b := by
  refine precision (N := N) (h := h) (c := 2007) (K := 2 ^ 1966)
    rp r1 (by positivity) ?_ ?_ accuracy
  · exact (Nat.mul_le_mul_right (2 ^ 1966) near).trans (by omega)
  · rw [show (2007 : ℕ) = 2006 + 1 by decide, pow_succ]
    calc
      _ = (2 ^ 2006 * r ^ h) * 2 := by ring
      _ < (1 / 2 : ℝ) * 2 := by gcongr
      _ = 1 := by norm_num

theorem example_coefficients :
    retained 2 77 = 18 ∧ retained 2 65 = 18 ∧ retained 2 85 = 22 := by decide +kernel

end PrimeFactors.CircularCoefficientFilter
