import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic

namespace PrimeFactors.SelbergMultipleCoefficients

open ArithmeticFunction
open scoped ArithmeticFunction

/-- Selberg's second generalized von Mangoldt coefficient, in convolution form. -/
noncomputable def second (n : ℕ) : ℝ :=
  Λ n * Real.log n + (Λ * Λ) n

/-- Multiply an arithmetic function pointwise by the natural logarithm. -/
noncomputable def logWeight (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => Real.log n * f n, by simp⟩

private theorem logWeight_mul (f g : ArithmeticFunction ℝ) :
    logWeight (f*g) = logWeight f * g + f * logWeight g := by
  ext n
  change Real.log n * (f*g) n = _
  rw [ArithmeticFunction.add_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨h, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hz
  have hz₁ : z.1 ≠ 0 := fun he => hn (h.symm.trans (by simp [he]))
  have hz₂ : z.2 ≠ 0 := fun he => hn (h.symm.trans (by simp [he]))
  change Real.log n * (f z.1 * g z.2) =
    Real.log z.1 * f z.1 * g z.2 + f z.1 * (Real.log z.2 * g z.2)
  rw [← h, Nat.cast_mul, Real.log_mul (by exact_mod_cast hz₁) (by exact_mod_cast hz₂)]
  ring

/-- The convolution form is the Möbius transform of the squared logarithm,
the Dirichlet coefficient convention used for the second generalized von Mangoldt function. -/
theorem second_eq_moebius {n : ℕ} : second n = (logWeight log * μ) n := by
  have hζ : logWeight (ζ : ArithmeticFunction ℝ) = log := by
    ext k
    by_cases hk : k = 0 <;> simp [logWeight, natCoe_apply, zeta_apply, hk]
  have h : logWeight log * μ = logWeight Λ + Λ * Λ := by
    calc
      logWeight log * μ = logWeight (Λ * ζ) * μ := by rw [vonMangoldt_mul_zeta]
      _ = (logWeight Λ * ζ) * μ + (Λ * log) * μ := by rw [logWeight_mul, hζ, add_mul]
      _ = logWeight Λ + Λ * Λ := by rw [mul_assoc, coe_zeta_mul_coe_moebius, mul_one,
                                          mul_assoc, log_mul_moebius_eq_vonMangoldt]
  rw [h, ArithmeticFunction.add_apply]
  simp [second, logWeight, mul_comm]

private theorem prime_options {p r s i j : ℕ} (hp : p.Prime) (hr : r.Prime) (hs : s.Prime)
    (h : p ∣ r ^ i * s ^ j) : p = r ∨ p = s := by
  rcases hp.dvd_mul.mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp hs).mp (hp.dvd_of_dvd_pow h))

private theorem not_power {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (dp : p ∣ n) (dq : q ∣ n) : ¬IsPrimePow n := by
  intro hn
  obtain ⟨_, _, h⟩ := isPrimePow_iff_unique_prime_dvd.mp hn
  exact hne ((h p ⟨hp, dp⟩).trans (h q ⟨hq, dq⟩).symm)

private theorem same_exponents {p q i j a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (h : p^i * q^j = p^a * q^b) : i = a ∧ j = b := by
  have h₁ := congrArg (fun n : ℕ => n.factorization p) h
  have h₂ := congrArg (fun n : ℕ => n.factorization q) h
  simp [Nat.factorization_mul, hp.ne_zero, hq.ne_zero, hp.factorization_pow, hq.factorization_pow,
    Finsupp.single_apply, hne, Ne.symm hne] at h₁ h₂
  exact ⟨h₁, h₂⟩

private theorem orientations {p q x y a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (ha : 0 < a) (hb : 0 < b) (hxy : x*y = p^a * q^b) (hx : IsPrimePow x)
    (hy : IsPrimePow y) : (x,y) = (p^a,q^b) ∨ (x,y) = (q^b,p^a) := by
  obtain ⟨r,i,hr,_,rfl⟩ := (isPrimePow_nat_iff _).mp hx
  obtain ⟨s,j,hs,_,rfl⟩ := (isPrimePow_nat_iff _).mp hy
  have dp : p ∣ r^i*s^j := hxy ▸ dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _
  have dq : q ∣ r^i*s^j := hxy ▸ dvd_mul_of_dvd_right (dvd_pow_self q hb.ne') _
  rcases prime_options hp hr hs dp with pr | ps <;> rcases prime_options hq hr hs dq with qr | qs
  · exact (hne (pr.trans qr.symm)).elim
  · subst r; subst s
    obtain ⟨rfl,rfl⟩ := same_exponents hp hq hne hxy
    exact Or.inl rfl
  · subst s; subst r
    rw [mul_comm (q^i) (p^j)] at hxy
    obtain ⟨rfl,rfl⟩ := same_exponents hp hq hne hxy
    exact Or.inr rfl
  · exact (hne (ps.trans qs.symm)).elim

/-- At a product of two distinct positive prime powers, the coefficient is
independent of both exponents. -/
theorem second_two_powers {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (ha : 0 < a) (hb : 0 < b) :
    second (p^a*q^b) = 2 * Real.log p * Real.log q := by
  classical
  let pairs : Finset (ℕ × ℕ) := {(p^a,q^b),(q^b,p^a)}
  have dp : p ∣ p^a*q^b := dvd_mul_of_dvd_left (dvd_pow_self _ ha.ne') _
  have dq : q ∣ p^a*q^b := dvd_mul_of_dvd_right (dvd_pow_self _ hb.ne') _
  have nz : p^a*q^b ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
  have distinct : p^a ≠ q^b := by
    intro h
    have d : p ∣ q^b := h ▸ dvd_pow_self p ha.ne'
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow d))
  have sub : pairs ⊆ (p^a*q^b).divisorsAntidiagonal := by
    intro z hz
    simp only [pairs, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [Nat.mem_divisorsAntidiagonal, nz, mul_comm]
  have outside (z : ℕ × ℕ) (hz : z ∈ (p^a*q^b).divisorsAntidiagonal) (h : z ∉ pairs) :
      Λ z.1 * Λ z.2 = 0 := by
    by_contra hnon
    have hx := vonMangoldt_ne_zero_iff.mp (left_ne_zero_of_mul hnon)
    have hy := vonMangoldt_ne_zero_iff.mp (right_ne_zero_of_mul hnon)
    exact h (by simpa [pairs] using orientations hp hq hne ha hb (Nat.mem_divisorsAntidiagonal.mp hz).1 hx hy)
  rw [second, vonMangoldt_eq_zero_iff.mpr (not_power hp hq hne dp dq), zero_mul, zero_add,
    ArithmeticFunction.mul_apply, ← Finset.sum_subset sub outside]
  simp [pairs, distinct, vonMangoldt_apply_pow ha.ne', vonMangoldt_apply_pow hb.ne',
    vonMangoldt_apply_prime hp, vonMangoldt_apply_prime hq]
  ring

/-- A third distinct prime divisor makes every convolution summand zero. -/
theorem second_three_divisors {p q r n : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (dp : p ∣ n) (dq : q ∣ n) (dr : r ∣ n) :
    second n = 0 := by
  rw [second, vonMangoldt_eq_zero_iff.mpr (not_power hp hq hpq dp dq), zero_mul, zero_add,
    ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro z hz
  by_contra hnon
  have hx := vonMangoldt_ne_zero_iff.mp (left_ne_zero_of_mul hnon)
  have hy := vonMangoldt_ne_zero_iff.mp (right_ne_zero_of_mul hnon)
  obtain ⟨u,i,hu,_,hu'⟩ := (isPrimePow_nat_iff _).mp hx
  obtain ⟨v,j,hv,_,hv'⟩ := (isPrimePow_nat_iff _).mp hy
  have eqn := (Nat.mem_divisorsAntidiagonal.mp hz).1
  rw [← hu', ← hv'] at eqn
  rw [← eqn] at dp dq dr
  rcases prime_options hp hu hv dp with h₁ | h₁ <;>
    rcases prime_options hq hu hv dq with h₂ | h₂ <;>
    rcases prime_options hr hu hv dr with h₃ | h₃ <;> omega

/-- After removing whole copies of the modulus, a coprime remainder determines
the result of the multiplied query using only the original coefficient. -/
theorem coprime_remainder {p q j u : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hu : Nat.Coprime u (p*q)) :
    second ((p*q)^j * u * (p*q)) = if u = 1 then second (p*q) else 0 := by
  by_cases one : u = 1
  · subst u
    simp only [mul_one, if_true]
    rw [← pow_succ, mul_pow]
    have b := second_two_powers hp hq hne (a := 1) (b := 1) (by decide) (by decide)
    simpa only [pow_one] using
      (second_two_powers hp hq hne (a := j+1) (b := j+1) (by omega) (by omega)).trans b.symm
  · rw [if_neg one]
    let r := u.minFac
    have hr : r.Prime := Nat.minFac_prime one
    have dr : r ∣ u := Nat.minFac_dvd u
    have avoid (s : ℕ) (hs : s ∣ p*q) : s ≠ r := by
      rintro rfl
      have h := Nat.dvd_gcd dr hs
      rw [hu.gcd_eq_one] at h
      exact hr.ne_one (Nat.dvd_one.mp h)
    apply second_three_divisors hp hq hr hne
      (avoid p (dvd_mul_right _ _)) (avoid q (dvd_mul_left _ _))
      (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
      (dvd_mul_of_dvd_right (dvd_mul_left _ _) _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right dr _) _)

/-- Every positive multiplier has a publicly computable reduced remainder.
Its gcd with the input either splits the input or leaves just the single
original coefficient or zero. -/
theorem multiplier_trichotomy {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hk : 0 < k) :
    ∃ j u : ℕ, k = (p*q)^j*u ∧ ¬p*q ∣ u ∧
      ((1 < u.gcd (p*q) ∧ u.gcd (p*q) < p*q ∧ u.gcd (p*q) ∣ p*q) ∨
       (u.Coprime (p*q) ∧ second (k*(p*q)) = if u = 1 then second (p*q) else 0)) := by
  have hN : 1 < p*q := Nat.one_lt_mul_iff.mpr ⟨hp.pos, hq.pos, Or.inl hp.one_lt⟩
  obtain ⟨j,u,hd,rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' (p*q) (by omega)
  refine ⟨j, u, rfl, hd, ?_⟩
  by_cases hc : u.Coprime (p*q)
  · exact Or.inr ⟨hc, coprime_remainder hp hq hne hc⟩
  · apply Or.inl
    have hgu := Nat.gcd_dvd_left u (p*q)
    have hgn := Nat.gcd_dvd_right u (p*q)
    have hpos := Nat.gcd_pos_of_pos_right u (by omega : 0 < p*q)
    have hle := Nat.le_of_dvd (by omega : 0 < p*q) hgn
    have hlt : u.gcd (p*q) ≠ p*q := fun he => hd (he ▸ hgu)
    change u.gcd (p*q) ≠ 1 at hc
    exact ⟨by omega, by omega, hgn⟩

/-- The coefficient determines the squared logarithmic ratio of the factors. -/
theorem logarithmic_gap {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    (Real.log (p*q : ℕ))^2 - 2*second (p*q) = (Real.log q - Real.log p)^2 := by
  have h := second_two_powers hp hq hne (a := 1) (b := 1) (by decide) (by decide)
  simp only [pow_one] at h
  rw [h, Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  ring

/-- A supplied exact coefficient and the public product determine the smaller prime. -/
theorem recover_smaller {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p < q) :
    Real.exp ((Real.log (p*q : ℕ) -
      Real.sqrt ((Real.log (p*q : ℕ))^2 - 2*second (p*q))) / 2) = p := by
  have ppos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have qpos : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  have cmp := Real.log_le_log ppos (show (p : ℝ) ≤ q by exact_mod_cast lt.le)
  rw [logarithmic_gap hp hq lt.ne, Real.sqrt_sq (by linarith), Nat.cast_mul,
    Real.log_mul ppos.ne' qpos.ne']
  convert Real.exp_log ppos using 2
  ring

/-- Predicted coefficient for a positive candidate smaller factor. -/
noncomputable def predicted (n x : ℝ) : ℝ := 2 * Real.log x * (Real.log n - Real.log x)

/-- Over the balanced smaller-factor interval, the coefficient changes by at
most twice the candidate displacement divided by the smaller candidate. -/
theorem candidate_spacing {n x y : ℝ} (hx : 0 < x) (xy : x ≤ y)
    (hy : y*y ≤ n) (hb : n ≤ 2*x*x) :
    0 ≤ predicted n y - predicted n x ∧ predicted n y - predicted n x ≤ 2*(y-x)/x := by
  have yp : 0 < y := hx.trans_le xy
  have np : 0 < n := (mul_pos yp yp).trans_le hy
  have xyp := mul_pos hx yp
  let a := Real.log (y/x)
  let b := Real.log (n/(x*y))
  have az : 0 ≤ a := Real.log_nonneg ((one_le_div hx).mpr xy)
  have bz : 0 ≤ b := Real.log_nonneg ((one_le_div xyp).mpr
    ((mul_le_mul_of_nonneg_right xy yp.le).trans hy))
  have amax : a ≤ y/x - 1 := Real.log_le_sub_one_of_pos (div_pos yp hx)
  have ratio : n/(x*y) ≤ 2 := (div_le_iff₀ xyp).mpr
    (by nlinarith [mul_le_mul_of_nonneg_left xy hx.le])
  have bmax : b ≤ 1 := (Real.log_le_sub_one_of_pos (div_pos np xyp)).trans (by linarith)
  have eqn : predicted n y - predicted n x = 2*a*b := by
    dsimp [predicted,a,b]
    rw [Real.log_div yp.ne' hx.ne', Real.log_div np.ne' xyp.ne', Real.log_mul hx.ne' yp.ne']
    ring
  rw [eqn]
  refine ⟨by positivity, ?_⟩
  calc
    2*a*b ≤ 2*a*1 := mul_le_mul_of_nonneg_left bmax (by positivity)
    _ ≤ 2*(y/x-1) := by linarith
    _ = 2*(y-x)/x := by field_simp

/-- At full size two adjacent odd candidate positions have readings separated
by at most 2⁻¹⁰²¹ whenever both are in the balanced smaller-factor interval. -/
theorem adjacent_full_size {n x : ℝ} (hx : (2:ℝ)^1023 ≤ x)
    (hy : (x+2)*(x+2) ≤ n) (hb : n ≤ 2*x*x) :
    predicted n (x+2) - predicted n x ≤ 1/(2:ℝ)^1021 := by
  have xpos : 0 < x := (pow_pos (by norm_num : 0 < (2:ℝ)) _).trans_le hx
  calc
    _ ≤ 2*((x+2)-x)/x := (candidate_spacing xpos (by linarith) hy hb).2
    _ = 4/x := by ring
    _ ≤ 1/(2:ℝ)^1021 := by
      have bp : 0 < (2:ℝ)^1021 := by positivity
      apply (div_le_div_iff₀ xpos bp).mpr
      norm_num at hx ⊢
      exact hx

end PrimeFactors.SelbergMultipleCoefficients
