import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# A single modular cyclotomic evaluation determines a balanced prime sum

The derivative identity is classical (D. H. Lehmer, 1966, or
A. Herrera-Poyatos and P. Moree, <https://arxiv.org/abs/1805.05207>).
The reduction below concerns exact evaluation of the cyclotomic polynomial
whose index is the public product. Computing that value is part of the cost.
-/
namespace PrimeFactors.CyclotomicSumDigit

open Polynomial
open scoped BigOperators Polynomial

private theorem prime_slope {p : ℕ} (hp : p.Prime) :
    2 * (cyclotomic p ℤ).derivative.eval 1 = (p:ℤ) * (p-1) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [cyclotomic_prime]
  simp only [derivative_sum, derivative_X_pow, eval_finset_sum, eval_mul, eval_C, eval_pow,
    eval_X, one_pow, mul_one]
  have g := Finset.sum_range_id_mul_two p
  have hi : ((∑ i ∈ Finset.range p, i : ℕ) : ℤ) * 2 = (p:ℤ) * (p-1) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hp.one_le, Nat.cast_one] using
      congrArg (fun z : ℕ => (z:ℤ)) g
  push_cast at hi
  linarith

/-- The value and the first derivative at 1, specialized to distinct primes. -/
theorem at_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p ≠ q) :
    (cyclotomic (p*q) ℤ).eval 1 = 1 ∧
    2 * (cyclotomic (p*q) ℤ).derivative.eval 1 = ((p:ℤ)-1)*((q:ℤ)-1) := by
  letI : Fact p.Prime := ⟨hp⟩
  have nd : ¬ q ∣ p := fun h => diff ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  have prod := cyclotomic_expand_eq_cyclotomic_mul hq nd ℤ
  have e := congrArg (eval (1:ℤ)) prod
  simp only [expand_eval, one_pow, eval_mul, eval_one_cyclotomic_prime] at e
  have pn : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have val : (cyclotomic (p*q) ℤ).eval 1 = 1 :=
    mul_right_cancel₀ pn (by simpa only [one_mul] using e.symm)
  refine ⟨val, ?_⟩
  have s := congrArg (fun f : ℤ[X] => f.derivative.eval 1) prod
  simp only [derivative_expand, derivative_mul, eval_add, eval_mul, eval_pow, eval_X,
    one_pow, expand_eval, eval_natCast, mul_one, eval_one_cyclotomic_prime, val, one_mul] at s
  apply mul_right_cancel₀ pn
  linear_combination ((q:ℤ)-1) * prime_slope hp - 2*s

/-- First-order Taylor evaluation with an explicit integral remainder. -/
private theorem first_order (f : ℤ[X]) (m : ℤ) :
    ∃ z : ℤ, f.eval (1+m) = f.eval 1 + m*f.derivative.eval 1 + m^2*z := by
  obtain ⟨g, hg⟩ := X_sub_C_dvd_sub_C_eval (p := f) (a := 1)
  have hd := congrArg (fun f : ℤ[X] => f.derivative.eval 1) hg
  have hv := congrArg (eval (1+m)) hg
  simp at hd hv
  obtain ⟨z, hz⟩ := sub_dvd_eval_sub (1+m) 1 g
  refine ⟨z, ?_⟩
  simp at hz
  linear_combination hv + m*hz - m*hd

/-- Given the factors, the desired modular value takes only ordinary
multiplication and division by two. This also certifies bounded examples. -/
theorem evaluation_mod {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (neq : p ≠ q) (m : ℤ) :
    (cyclotomic (p*q) ℤ).eval (1+m) ≡
      1 + m * ((((p:ℤ)-1)*((q:ℤ)-1))/2) [ZMOD m^2] := by
  obtain ⟨one, slope⟩ := at_one hp hq neq
  obtain ⟨z, hz⟩ := first_order (cyclotomic (p*q) ℤ) m
  rw [one] at hz
  rw [← slope, Int.mul_ediv_cancel_left _ (by decide : (2:ℤ) ≠ 0)]
  exact Int.modEq_iff_dvd.mpr ⟨-z, by linear_combination -hz⟩

/-- Computing the full integer before reducing it requires an output larger
in magnitude than M^((p-1)(q-1)), even though the modular query is small. -/
theorem integer_output {p q M : ℕ} (hp : p.Prime) (hq : q.Prime) (neq : p ≠ q)
    (hm : 0 < M) : M^((p-1)*(q-1)) < ((cyclotomic (p*q) ℤ).eval (1+(M:ℤ))).natAbs := by
  have large : 1 < p*q := by nlinarith [hp.two_le, hq.two_le]
  have v := sub_one_pow_totient_lt_natAbs_cyclotomic_eval (n := p*q) (q := 1+M)
    large (by omega)
  rw [Nat.totient_mul (hp.coprime_iff_not_dvd.mpr fun h => neq
    ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)), Nat.totient_prime hp, Nat.totient_prime hq] at v
  simpa using v

/-- A public modular evaluation supplies this digit without materializing the
integer value. A representative need only agree modulo m². -/
def digit (value m : ℤ) := (value-1)/m % m

theorem digit_of_evaluation {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (neq : p ≠ q)
    {m value : ℤ} (hm : 0 < m)
    (supplied : value ≡ (cyclotomic (p*q) ℤ).eval (1+m) [ZMOD m^2]) :
    ∃ c : ℤ, (p:ℤ)*q + 1 - 2*digit value m = p + q + 2*m*c := by
  obtain ⟨z, hz⟩ := first_order (cyclotomic (p*q) ℤ) m
  obtain ⟨one, slope⟩ := at_one hp hq neq
  rw [one] at hz
  obtain ⟨w, hw⟩ := Int.modEq_iff_dvd.mp supplied
  let d := (cyclotomic (p*q) ℤ).derivative.eval 1
  have base : value - 1 = m*(d + m*(z-w)) := by
    dsimp [d]
    linear_combination hz - hw
  have dig : digit value m = d % m := by
    rw [digit, base, Int.mul_ediv_cancel_left _ hm.ne', Int.add_mul_emod_self_left]
  refine ⟨d/m, ?_⟩
  rw [dig]
  change 2*d = _ at slope
  have decomp := Int.emod_add_ediv d m
  linear_combination -slope - 2*decomp

/-- The public lower endpoint is one past the integer square root of 4N.
For factors in [8M,16M), the next 2M consecutive integers cover their sum. -/
theorem sum_interval {p q M : ℕ} (low : 8*M ≤ p) (ord : p < q) (high : q < 16*M) :
    Nat.sqrt (4*(p*q)) < p+q ∧ p+q ≤ Nat.sqrt (4*(p*q)) + 2*M := by
  have qdiff : 0 < q-p := by omega
  have gap : q-p < 8*M := by omega
  have linear : 2*(q-p) ≤ p+q-M := by omega
  have width : (q-p)^2 ≤ 4*M*(p+q-M) := calc
    (q-p)^2 ≤ 8*M*(q-p) := by simpa only [pow_two] using Nat.mul_le_mul_right (q-p) gap.le
    _ = 4*M*(2*(q-p)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ linear
  have diff_sum : q-p+p = q := by omega
  have a : Nat.sqrt (4*(p*q)) < p+q := Nat.sqrt_lt'.mpr (by nlinarith [sq_pos_of_pos qdiff])
  have h₁ : M ≤ p+q := by omega
  have h₂ : 2*M ≤ p+q := by omega
  have l : (p+q-2*M)^2 ≤ 4*(p*q) := by
    zify [h₁, h₂, ord.le] at width ⊢
    nlinarith
  exact ⟨a, by have := Nat.le_sqrt'.mpr l; omega⟩

/-- Reconstruct the exact prime sum from the modular representative and
the public integers N and M. -/
def recoverSum (N M : ℕ) (value : ℤ) : ℤ :=
  let low : ℤ := Nat.sqrt (4*N) + 1
  low + ((N:ℤ) + 1 - 2*digit value M - low) % (2*(M:ℤ))

theorem recover {p q M : ℕ} (hp : p.Prime) (hq : q.Prime)
    (low : 8*M ≤ p) (ord : p < q) (high : q < 16*M) {value : ℤ}
    (supplied : value ≡ (cyclotomic (p*q) ℤ).eval (1+M) [ZMOD (M:ℤ)^2]) :
    recoverSum (p*q) M value = p+q := by
  obtain ⟨c, hc⟩ := digit_of_evaluation hp hq ord.ne (m := (M:ℤ))
    (by exact_mod_cast (by omega : 0 < M)) supplied
  obtain ⟨lh, rh⟩ := sum_interval low ord high
  let L : ℤ := (Nat.sqrt (4*(p*q)):ℤ) + 1
  have h0 : 0 ≤ (p:ℤ) + q - L := by dsimp [L]; omega
  have h1 : (p:ℤ) + q - L < 2*(M:ℤ) := by dsimp [L]; omega
  change L + (↑(p*q) + 1 - 2*digit value M - L) % (2*(M:ℤ)) = _
  rw [Nat.cast_mul, hc]
  rw [show (p:ℤ)+q+2*(M:ℤ)*c-L = (p+q-L)+(2*(M:ℤ))*c by ring,
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]
  ring

/-- One 1020-bit digit, from a residue modulo 2^2040, suffices for two
distinct ordered 1024-bit primes. -/
theorem equal_1024 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (low : 2^1023 ≤ p) (ord : p < q) (high : q < 2^1024) {value : ℤ}
    (supplied : value ≡ (cyclotomic (p*q) ℤ).eval (1+2^1020) [ZMOD (2:ℤ)^2040]) :
    recoverSum (p*q) (2^1020) value = p+q := by
  have a : 8*2^1020 = (2:ℕ)^1023 := by decide +kernel
  have b : 16*2^1020 = (2:ℕ)^1024 := by decide +kernel
  apply recover (M := 2^1020) hp hq (a.le.trans low) ord (lt_of_lt_of_eq high b.symm)
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  simpa only [← pow_mul] using supplied

/-- At N=9017 the residue modulo 64 is 17. Its upper base-8 digit is 2. -/
theorem worked_example :
    (cyclotomic 9017 ℤ).eval 9 % 64 = 17 ∧ recoverSum 9017 8 17 = 198 ∧
    Nat.Prime 71 ∧ Nat.Prime 127 ∧ 71*127 = 9017 := by
  have e := evaluation_mod (p := 71) (q := 127) (by decide) (by decide) (by decide) 8
  have v : (cyclotomic 9017 ℤ).eval 9 ≡ 17 [ZMOD 64] := e.trans (by decide)
  have r := recover (M := 8) (p := 71) (q := 127) (by decide) (by decide)
    (by decide) (by decide) (by decide) v.symm
  change (cyclotomic 9017 ℤ).eval 9 % 64 = 17 % 64 at v
  exact ⟨v, r, by decide, by decide, by decide⟩

/-- The low-degree coefficients seen before the smaller prime are exactly
those of 1-X. At the smaller prime itself the coefficient equals one. -/
theorem first_coefficients {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p < q) :
    (∀ j < p, (cyclotomic (p*q) ℤ).coeff j = (1-X : ℤ[X]).coeff j) ∧
    (cyclotomic (p*q) ℤ).coeff p = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let f := cyclotomic (p*q) ℤ
  have nd : ¬ q ∣ p := fun d => (not_le.mpr ord) (Nat.le_of_dvd hp.pos d)
  have geo : cyclotomic p ℤ * (X-1) = X^p-1 := by rw [cyclotomic_prime, geom_sum_mul]
  obtain ⟨g, hg⟩ : X ∣ cyclotomic p ℤ - 1 := X_dvd_iff.mpr (by simp [cyclotomic_coeff_zero ℤ hp.one_lt])
  have ex := congrArg (expand ℤ q) hg
  simp only [map_sub, map_one, map_mul, expand_X, cyclotomic_expand_eq_cyclotomic_mul hq nd] at ex
  have obstruction : X^q ∣ f * X^p - f - (X-1) := by
    refine ⟨(expand ℤ q g)*(X-1), ?_⟩
    calc
      _ = f*(X^p-1) - (X-1) := by ring
      _ = (f*cyclotomic p ℤ-1)*(X-1) := by rw [← geo]; ring
      _ = _ := by rw [show f*cyclotomic p ℤ-1 = X^q*expand ℤ q g from ex]; ring
  have coeff (j : ℕ) (ltq : j < q) := X_pow_dvd_iff.mp obstruction j ltq
  constructor
  · intro j ltj
    have h := coeff j (ltj.trans ord)
    simp only [coeff_sub, coeff_mul_X_pow', if_neg (not_le.mpr ltj)] at h ⊢
    dsimp only [f] at h
    linarith
  · have h := coeff p ord
    have hn := cyclotomic_coeff_zero ℤ (n := p*q) (by nlinarith [hp.two_le, hq.two_le])
    have pn : p ≠ 1 := hp.ne_one
    simp [f, coeff_mul_X_pow', pn, hp.ne_zero, hn, coeff_X, coeff_one] at h
    rw [if_neg (Ne.symm pn)] at h
    linarith

end PrimeFactors.CyclotomicSumDigit
