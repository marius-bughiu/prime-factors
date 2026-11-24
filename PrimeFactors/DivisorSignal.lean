import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime

namespace PrimeFactors

open Complex

/-- The positive fundamental height of the missing Euler factor indexed by x > 1. -/
noncomputable def eulerHeight (x : ℝ) : ℝ := 2 * Real.pi / Real.log x

private theorem euler_factor_zero_iff {r : ℕ} (hr : 1 < r) (t : ℝ) :
    1 - (r : ℂ) ^ (-((t : ℂ) * I)) = 0 ↔
      ∃ k : ℤ, t * Real.log r = k * (2 * Real.pi) := by
  have nonzero : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  rw [sub_eq_zero, eq_comm, Complex.cpow_def_of_ne_zero nonzero,
    ← Complex.natCast_log, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have eqn := congrArg Complex.im hk
    simp [-Complex.natCast_log, Complex.mul_im, Complex.mul_re] at eqn
    push_cast
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    apply Complex.ext
    · simp [-Complex.natCast_log, Complex.mul_re, Complex.mul_im]
    · simp [-Complex.natCast_log, Complex.mul_im, Complex.mul_re]
      linarith

private theorem zeta_ne_zero_at_positive_height {t : ℝ} (ht : 0 < t) :
    riemannZeta ((t : ℂ) * I) ≠ 0 := by
  let s := (t : ℂ) * I
  have hs : ∀ n : ℕ, s ≠ -n := by
    intro n eqn
    have bad := congrArg Complex.im eqn
    simp [s] at bad
    linarith
  have hs' : s ≠ 1 := by
    intro eqn
    have bad := congrArg Complex.re eqn
    simp [s] at bad
  intro zero
  apply riemannZeta_ne_zero_of_one_le_re (s := 1 - s) (by simp [s])
  rw [riemannZeta_one_sub hs hs', show riemannZeta s = 0 from zero, mul_zero]

/-- Every positive boundary zero of the actual principal-character L-function
comes from a prime divisor and is an integral multiple of its fundamental height. -/
theorem principal_boundary_zero_iff (n : ℕ) [NeZero n] {t : ℝ} (ht : 0 < t) :
    DirichletCharacter.LFunctionTrivChar n ((t : ℂ) * I) = 0 ↔
      ∃ r ∈ n.primeFactors, ∃ k : ℤ, t * Real.log r = k * (2 * Real.pi) := by
  have hs : (t : ℂ) * I ≠ 1 := by
    intro eqn
    have bad := congrArg Complex.re eqn
    simp at bad
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs, mul_eq_zero,
    or_iff_left (zeta_ne_zero_at_positive_height ht), Finset.prod_eq_zero_iff]
  exact exists_congr fun r => and_congr_right fun hr =>
    euler_factor_zero_iff (Nat.prime_of_mem_primeFactors hr).one_lt t

/-- The first positive boundary zero explicitly determines the largest prime factor.
The theorem covers arbitrary positive moduli with a prime factor, including prime powers. -/
theorem first_boundary_zero_of_largest_prime {n q : ℕ} [NeZero n]
    (hq : q ∈ n.primeFactors) (largest : ∀ r ∈ n.primeFactors, r ≤ q) :
    IsLeast {t : ℝ | 0 < t ∧ DirichletCharacter.LFunctionTrivChar n ((t : ℂ) * I) = 0}
      (eulerHeight q) := by
  have qlarge : (1 : ℝ) < q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_lt
  have H := Real.log_pos qlarge
  have Ht : 0 < eulerHeight q := div_pos (by positivity) H
  constructor
  · refine ⟨Ht, (principal_boundary_zero_iff n Ht).2 ⟨q, hq, 1, ?_⟩⟩
    simp [eulerHeight, H.ne']
  · intro t ht
    obtain ⟨ht, zero⟩ := ht
    obtain ⟨r, hr, k, heq⟩ := (principal_boundary_zero_iff n ht).1 zero
    have rlarge : (1 : ℝ) < r := by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).one_lt
    have positive : 0 < (k : ℝ) * (2 * Real.pi) := heq ▸ mul_pos ht (Real.log_pos rlarge)
    have hk : 0 < k := by exact_mod_cast (pos_of_mul_pos_left positive (by positivity))
    have one : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have rq : Real.log r ≤ Real.log q := Real.log_le_log (by linarith) (by exact_mod_cast largest r hr)
    unfold eulerHeight
    apply (div_le_iff₀ H).2
    calc
      2 * Real.pi ≤ (k : ℝ) * (2 * Real.pi) := le_mul_of_one_le_left (by positivity) one
      _ = t * Real.log r := heq.symm
      _ ≤ t * Real.log q := mul_le_mul_of_nonneg_left rq ht.le

/-- Invert the fundamental boundary height to recover the integer factor. -/
theorem exp_inv_eulerHeight {x : ℝ} (hx : 1 < x) :
    Real.exp (2 * Real.pi / eulerHeight x) = x := by
  unfold eulerHeight
  rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ (by positivity : 2 * Real.pi ≠ 0),
    Real.exp_log (by linarith)]

/-- The spacing of heights for neighbouring integer candidates has scale
1/(x log² x). The bounds concern height-only resolution and make no assumptions
about the cost of evaluating the L-function to that precision. -/
theorem eulerHeight_spacing {x : ℝ} (hx : 1 < x) :
    let c := 2 * Real.pi / (Real.log x * Real.log (x + 1))
    c / (x + 1) ≤ eulerHeight x - eulerHeight (x + 1) ∧
      eulerHeight x - eulerHeight (x + 1) ≤ c / x := by
  have h₀ : 0 < x := by linarith
  have h₁ : 0 < x + 1 := by linarith
  have log₀ := Real.log_pos hx
  have log₁ := Real.log_pos (show 1 < x + 1 by linarith)
  let c := 2 * Real.pi / (Real.log x * Real.log (x + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  have delta : eulerHeight x - eulerHeight (x + 1) = c * Real.log ((x + 1) / x) := by
    rw [Real.log_div h₁.ne' h₀.ne']
    dsimp [eulerHeight, c]
    field_simp
    ring
  change c / (x + 1) ≤ _ ∧ _ ≤ c / x
  rw [delta, div_eq_mul_one_div c (x + 1), div_eq_mul_one_div c x]
  constructor
  · apply mul_le_mul_of_nonneg_left _ hc.le
    calc
      1 / (x + 1) = 1 - ((x + 1) / x)⁻¹ := by field_simp
      _ ≤ Real.log ((x + 1) / x) := Real.one_sub_inv_le_log_of_pos (div_pos h₁ h₀)
  · apply mul_le_mul_of_nonneg_left _ hc.le
    calc
      Real.log ((x + 1) / x) ≤ (x + 1) / x - 1 := Real.log_le_sub_one_of_pos (div_pos h₁ h₀)
      _ = 1 / x := by field_simp

/-- At every positive index below the smaller prime, the coefficients of the
principal Dirichlet series are identically one, independently of the factors. -/
theorem principal_coeff_before_factor {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p ≤ q) (pos : 0 < k) (early : k < p) :
    (1 : DirichletCharacter ℂ (p * q)) (k : ZMod (p * q)) = 1 := by
  apply MulChar.one_apply
  apply (ZMod.isUnit_iff_coprime _ _).2
  exact Nat.coprime_mul_iff_right.mpr
    ⟨(hp.coprime_iff_not_dvd.mpr (fun h => (not_le_of_gt early) (Nat.le_of_dvd pos h))).symm,
      (hq.coprime_iff_not_dvd.mpr (fun h => (not_le_of_gt (early.trans_le ordered)) (Nat.le_of_dvd pos h))).symm⟩

private theorem log_grid_not_integer {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (distinct : p ≠ q) (hk : 0 < k) (d : ℤ) :
    (k : ℝ) * Real.log p / Real.log ((p : ℝ) * q) ≠ d := by
  have hP : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hQ : 1 < (q : ℝ) := by exact_mod_cast hq.one_lt
  have hN : 1 < (p : ℝ) * q := one_lt_mul_of_lt_of_le hP hQ.le
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have positive := div_pos (mul_pos hkR (Real.log_pos hP)) (Real.log_pos hN)
  intro eqn
  have dpos : 0 < d := by exact_mod_cast (eqn ▸ positive : 0 < (d : ℝ))
  lift d to ℕ using dpos.le with m
  have mpos : m ≠ 0 := by omega
  have scale := (div_eq_iff (Real.log_pos hN).ne').mp eqn
  have logs : Real.log ((p : ℝ) ^ k) = Real.log (((p : ℝ) * q) ^ m) := by
    simpa only [Real.log_pow, Int.cast_natCast] using scale
  have eqR : (p : ℝ) ^ k = ((p : ℝ) * q) ^ m :=
    Real.strictMonoOn_log.injOn (pow_pos (show 0 < (p : ℝ) by linarith) _)
      (pow_pos (show 0 < (p : ℝ) * q by linarith) _) logs
  have eqN : p ^ k = (p * q) ^ m := by exact_mod_cast eqR
  have divides : q ∣ p ^ k := eqN ▸ (dvd_mul_left q p).trans (dvd_pow_self _ mpos)
  exact distinct ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow divides)).symm

/-- At the product-selected height 2πk/log N, the sum of the counts of the two
Euler-factor zero progressions is always k−1 for distinct primes. -/
theorem boundary_grid_count {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (distinct : p ≠ q) (hk : 0 < k) :
    ⌊(k : ℝ) * Real.log p / Real.log ((p : ℝ) * q)⌋ +
      ⌊(k : ℝ) * Real.log q / Real.log ((p : ℝ) * q)⌋ = (k : ℤ) - 1 := by
  let x := (k : ℝ) * Real.log p / Real.log ((p : ℝ) * q)
  let y := (k : ℝ) * Real.log q / Real.log ((p : ℝ) * q)
  change ⌊x⌋ + ⌊y⌋ = (k : ℤ) - 1
  have hP : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hQ : 1 < (q : ℝ) := by exact_mod_cast hq.one_lt
  have H := Real.log_pos (one_lt_mul_of_lt_of_le hP hQ.le)
  have sum : x + y = k := by
    dsimp [x, y]
    rw [← add_div, ← mul_add, ← Real.log_mul (by linarith : (p : ℝ) ≠ 0)
      (by linarith : (q : ℝ) ≠ 0), mul_div_cancel_right₀ _ H.ne']
  have low := Int.le_floor_add_floor x y
  rw [sum, Int.floor_natCast] at low
  have strictX : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x)
    (fun e => log_grid_not_integer hp hq distinct hk ⌊x⌋ e.symm)
  have upper : ⌊x⌋ + ⌊y⌋ < (k : ℤ) := by
    exact_mod_cast (show (⌊x⌋ : ℝ) + (⌊y⌋ : ℝ) < k by linarith [Int.floor_le y])
  omega

/-- The toy product's boundary height recovers its larger prime divisor. -/
theorem boundary_example_34387 :
    IsLeast {t : ℝ | 0 < t ∧ DirichletCharacter.LFunctionTrivChar 34387 ((t : ℂ) * I) = 0}
      (eulerHeight 251) := by
  have factors : (34387 : ℕ).primeFactors = {137, 251} := by
    rw [show (34387 : ℕ) = 137 * 251 by decide, Nat.primeFactors_mul (by decide) (by decide),
      (by norm_num : Nat.Prime 137).primeFactors, (by norm_num : Nat.Prime 251).primeFactors]
    decide
  apply first_boundary_zero_of_largest_prime (q := 251)
  · simp [factors]
  · intro r hr
    simp only [factors, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> decide

/-- Real dephasing of the principal-character correction at an imaginary height.
All quantities on the right of this definition use the product alone. -/
noncomputable def boundaryProbe (n : ℕ) [NeZero n] (t : ℝ) : ℝ :=
  (Complex.exp (((t * Real.log n / 2 : ℝ) : ℂ) * I) *
    (DirichletCharacter.LFunctionTrivChar n ((t : ℂ) * I) / riemannZeta ((t : ℂ) * I))).re

private theorem dephase_one_factor {r : ℕ} (hr : r.Prime) (t : ℝ) :
    let a : ℂ := (t * Real.log r / 2 : ℝ)
    Complex.exp (a * I) * (1 - (r : ℂ) ^ (-((t : ℂ) * I))) =
      2 * Complex.sin a * I := by
  dsimp only
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne_zero), ← Complex.natCast_log,
    mul_sub, mul_one, ← Complex.exp_add]
  have phase : (((t * Real.log r / 2 : ℝ) : ℂ) * I + (Real.log r : ℂ) * -(t * I)) =
      -((t * Real.log r / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [phase, Complex.sin]
  linear_combination -(Complex.exp (-((t * Real.log r / 2 : ℝ) : ℂ) * I) -
    Complex.exp (((t * Real.log r / 2 : ℝ) : ℂ) * I)) * Complex.I_mul_I

/-- The real probe is a signed product of two ordinary sines. -/
theorem boundaryProbe_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (different : p ≠ q)
    [NeZero (p * q)] {t : ℝ} (ht : 0 < t) :
    boundaryProbe (p * q) t =
      -4 * Real.sin (t * Real.log p / 2) * Real.sin (t * Real.log q / 2) := by
  have hs : (t : ℂ) * I ≠ 1 := by
    intro h
    have eqn := congrArg Complex.re h
    simp at eqn
  have factors := Nat.primeFactors_mul hp.ne_zero hq.ne_zero
  rw [hp.primeFactors, hq.primeFactors] at factors
  have pair : ({p} ∪ {q} : Finset ℕ) = {p, q} := by ext; simp
  rw [pair] at factors
  unfold boundaryProbe
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs,
    mul_div_cancel_right₀ _ (zeta_ne_zero_at_positive_height ht), factors,
    Finset.prod_insert (by simpa using different), Finset.prod_singleton]
  have logsum : (((t * Real.log (↑(p * q) : ℝ) / 2 : ℝ) : ℂ) * I) =
      (((t * Real.log p / 2 : ℝ) : ℂ) * I) + (((t * Real.log q / 2 : ℝ) : ℂ) * I) := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
    push_cast
    ring
  rw [logsum, Complex.exp_add, mul_mul_mul_comm, dephase_one_factor hp, dephase_one_factor hq]
  simp only [← Complex.ofReal_sin]
  rw [show ∀ a b : ℂ, 2 * a * I * (2 * b * I) = -4 * a * b from fun a b => by
    linear_combination 4 * a * b * Complex.I_mul_I]
  norm_cast

/-- A single certified sign at x compares the larger factor with x. The domain
x > √N is expressed as x > 1 and N < x², using only the given product. -/
theorem boundaryProbe_compare {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p < q) [NeZero (p * q)] {x : ℝ} (hx : 1 < x) (window : (p : ℝ) * q < x ^ 2) :
    let b := boundaryProbe (p * q) (eulerHeight x)
    ((q : ℝ) < x → b < 0) ∧ ((q : ℝ) = x → b = 0) ∧ (x < q → 0 < b) := by
  dsimp only
  have hx₀ : 0 < x := by linarith
  have lp := Real.log_pos (show 1 < (p : ℝ) by exact_mod_cast hp.one_lt)
  have lq := Real.log_pos (show 1 < (q : ℝ) by exact_mod_cast hq.one_lt)
  have lx := Real.log_pos hx
  have pr : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have qr : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have px : (p : ℝ) < x := by
    by_contra! bad
    have pq : (p : ℝ) < q := by exact_mod_cast ordered
    nlinarith [mul_le_mul bad (le_trans bad pq.le) hx₀.le (by linarith : (0 : ℝ) ≤ p)]
  have qx₂ : (q : ℝ) < x ^ 2 := by nlinarith [mul_pos (sub_pos.mpr pr) qr]
  have lpx := Real.log_lt_log (show 0 < (p : ℝ) by linarith) px
  have lqx := Real.log_lt_log qr qx₂
  rw [Real.log_pow] at lqx
  have tpos : 0 < eulerHeight x := by unfold eulerHeight; positivity
  rw [boundaryProbe_semiprime hp hq ordered.ne tpos]
  let scale := Real.pi / Real.log x
  have scalePos : 0 < scale := div_pos Real.pi_pos lx
  have scaleLog : scale * Real.log x = Real.pi := div_mul_cancel₀ _ lx.ne'
  have angle (y : ℝ) : eulerHeight x * y / 2 = scale * y := by
    dsimp [eulerHeight, scale]; ring
  rw [angle, angle]
  have sinP := Real.sin_pos_of_pos_of_lt_pi (mul_pos scalePos lp)
    ((mul_lt_mul_of_pos_left lpx scalePos).trans_eq scaleLog)
  have sinQlo := mul_pos scalePos lq
  constructor
  · intro qx
    have upper := (mul_lt_mul_of_pos_left (Real.log_lt_log qr qx) scalePos).trans_eq scaleLog
    exact mul_neg_of_neg_of_pos (by linarith) (Real.sin_pos_of_pos_of_lt_pi sinQlo upper)
  constructor
  · intro qx
    rw [qx, scaleLog, Real.sin_pi, mul_zero]
  · intro xq
    have past := (mul_lt_mul_of_pos_left (Real.log_lt_log hx₀ xq) scalePos)
    rw [scaleLog] at past
    have bound := mul_lt_mul_of_pos_left lqx scalePos
    have angleBound : scale * Real.log q < 2 * Real.pi := by
      push_cast at bound
      linarith [show scale * (2 * Real.log x) = 2 * Real.pi by linarith [scaleLog]]
    have negSin := Real.sin_neg_of_neg_of_neg_pi_lt
      (show scale * Real.log q - 2 * Real.pi < 0 by linarith)
      (show -Real.pi < scale * Real.log q - 2 * Real.pi by linarith)
    rw [Real.sin_sub_two_pi] at negSin
    exact mul_pos_of_neg_of_neg (by linarith) negSin

private theorem log_gap_of_unit_step {a b X : ℝ} (ha : 0 < a) (step : a + 1 ≤ b)
    (size : b ≤ 2 * X) : 1 / (2 * X) ≤ Real.log b - Real.log a := by
  have hb : 0 < b := by linarith
  calc
    1 / (2 * X) ≤ 1 / b := one_div_le_one_div_of_le hb size
    _ ≤ (b - a) / b := (div_le_div_iff_of_pos_right hb).2 (by linarith)
    _ = 1 - (b / a)⁻¹ := by field_simp
    _ ≤ Real.log (b / a) := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
    _ = _ := Real.log_div hb.ne' ha.ne'

private theorem threshold_sine_margin {r x : ℕ} (large : 4 ≤ x) (hr : 0 < r)
    (low : x ≤ 2 * r) (high : r ≤ 2 * x) (distinct : r ≠ x) :
    1 / ((x : ℝ) * Real.log x) ≤ |Real.sin (eulerHeight x * Real.log r / 2)| := by
  have xlarge : (4 : ℝ) ≤ x := by exact_mod_cast large
  have hx : 0 < (x : ℝ) := by linarith
  have hR : 0 < (r : ℝ) := by exact_mod_cast hr
  have lx := Real.log_pos (show 1 < (x : ℝ) by linarith)
  have log4 : 2 * Real.log 2 ≤ Real.log x := by
    have t := Real.log_le_log (by norm_num : 0 < (2 : ℝ)^2) (by norm_num; exact large : (2 : ℝ)^2 ≤ x)
    simpa [Real.log_pow] using t
  have lower := Real.log_le_log hx (by exact_mod_cast low : (x : ℝ) ≤ 2 * r)
  have upper := Real.log_le_log hR (by exact_mod_cast high : (r : ℝ) ≤ 2 * x)
  rw [Real.log_mul (by norm_num) hR.ne'] at lower
  rw [Real.log_mul (by norm_num) hx.ne'] at upper
  have close : |Real.log r - Real.log x| ≤ Real.log x / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have gap : 1 / (2 * (x : ℝ)) ≤ |Real.log r - Real.log x| := by
    rcases lt_or_gt_of_ne distinct with h | h
    · rw [abs_of_neg (sub_neg.mpr (Real.log_lt_log hR (by exact_mod_cast h))), neg_sub]
      exact log_gap_of_unit_step hR (by exact_mod_cast (show r + 1 ≤ x by omega)) (by linarith)
    · rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log hx (by exact_mod_cast h)))]
      exact log_gap_of_unit_step hx (by exact_mod_cast (show x + 1 ≤ r by omega)) (by exact_mod_cast high)
  let s := Real.pi / Real.log x
  let u := s * (Real.log r - Real.log x)
  have hs : 0 < s := div_pos Real.pi_pos lx
  have hu : |u| = s * |Real.log r - Real.log x| := by rw [show u = _ from rfl, abs_mul, abs_of_pos hs]
  have half : s * (Real.log x / 2) = Real.pi / 2 := by dsimp [s]; field_simp
  have angle : eulerHeight x * Real.log r / 2 = u + Real.pi := by
    dsimp [u, s, eulerHeight]
    field_simp
    ring
  have chord := Real.mul_abs_le_abs_sin ((hu ▸ (mul_le_mul_of_nonneg_left close hs.le).trans_eq half) :
    |u| ≤ Real.pi / 2)
  rw [angle, Real.sin_add_pi, abs_neg]
  rw [hu] at chord
  calc
    1 / ((x : ℝ) * Real.log x) = 2 / Real.pi * (s * (1 / (2 * x))) := by
      dsimp [s]; field_simp; ring
    _ ≤ 2 / Real.pi * (s * |Real.log r - Real.log x|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left gap hs.le) (by positivity)
    _ ≤ _ := chord

/-- A certified error smaller than the displayed margin preserves the comparison.
The integer threshold is in the balanced upper-factor interval and passes an
initial divisibility test. -/
theorem boundaryProbe_margin {p q x : ℕ} (hp : p.Prime) (hq : q.Prime) (ordered : p < q)
    (balance : q ≤ 2 * p) [NeZero (p * q)] (large : 4 ≤ x)
    (lo : p * q < x ^ 2) (hi : x ^ 2 ≤ 2 * (p * q)) (miss : ¬ x ∣ p * q) :
    4 / ((x : ℝ) * Real.log x)^2 ≤ |boundaryProbe (p * q) (eulerHeight x)| := by
  have px : p ≤ x := Nat.mul_self_le_mul_self_iff.mp (by
    nlinarith only [lo, Nat.mul_le_mul_left p ordered.le])
  have xp : x ≤ 2 * p := Nat.mul_self_le_mul_self_iff.mp (by
    nlinarith only [hi, Nat.mul_le_mul_left p balance])
  have pBound := threshold_sine_margin large hp.pos xp (by omega : p ≤ 2 * x)
    (fun eqn : p = x => miss (eqn ▸ dvd_mul_right p q))
  have qBound := threshold_sine_margin large hq.pos (by omega : x ≤ 2 * q) (by omega : q ≤ 2 * x)
    (fun eqn : q = x => miss (eqn ▸ dvd_mul_left q p))
  have lx := Real.log_pos (show 1 < (x : ℝ) by exact_mod_cast (show 1 < x by omega))
  have H : 0 < eulerHeight x := by unfold eulerHeight; positivity
  rw [boundaryProbe_semiprime hp hq ordered.ne H, abs_mul, abs_mul]
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
  have bound := mul_le_mul pBound qBound (by positivity) (abs_nonneg _)
  calc
    _ = 4 * (1 / ((x : ℝ) * Real.log x) * (1 / ((x : ℝ) * Real.log x))) := by ring
    _ ≤ _ := by linarith

end PrimeFactors
