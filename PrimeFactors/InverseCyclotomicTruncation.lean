import PrimeFactors.InverseCyclotomicMeasurements

/-! Error of evaluating the ordinary Taylor polynomial at zero of the
scaled inverse cyclotomic polynomial. The estimates concern direct coefficient
prefixes, with no assumption about other ways of obtaining a polynomial value. -/

namespace PrimeFactors.InverseCyclotomicTruncation

open Finset Polynomial BoundedPowerMeasurement InverseCyclotomicMeasurements

/-- Value of the Taylor polynomial through degree `k`, including degree zero. -/
noncomputable def prefixValue (N k : ℕ) (x : ℚ) : ℚ :=
  ∑ j ∈ range (k + 1), ((polynomial N).coeff j : ℚ) * x ^ j

theorem prefix_formula {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (pq : p < q)
    (k : ℕ) (x : ℚ) :
    prefixValue (p*q) k x =
      1 - (if p ≤ k then x^p else 0) - (if q ≤ k then x^q else 0) +
        (if p+q ≤ k then x^(p+q) else 0) := by
  have expand : polynomial (p*q) = X^0-X^p-X^q+X^(p+q) := by
    rw [sparse hp hq pq, pow_add, pow_zero]
    ring
  simp only [prefixValue, expand, coeff_add, coeff_sub, coeff_X_pow, coeff_one, Int.cast_add,
    Int.cast_sub, apply_ite (fun n : ℤ => (n : ℚ)), Int.cast_one, Int.cast_zero,
    add_mul, sub_mul, ite_mul, one_mul, zero_mul, sum_add_distrib, sum_sub_distrib,
    sum_ite_eq', mem_range, Nat.lt_succ_iff, Nat.zero_le, if_true, pow_zero]

theorem exact_from_sum {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (pq : p < q)
    (complete : p+q ≤ k) (x : ℚ) : prefixValue (p*q) k x = value (p*q) x := by
  rw [prefix_formula hp hq pq, value_eq hp hq pq, if_pos (by omega : p ≤ k),
    if_pos (by omega : q ≤ k), if_pos complete, pow_add]
  ring

/-- The first B terms of the geometric sum already force 1−r^p ≥ 1/9. -/
theorem missing_factor {B p : ℕ} (pos : 0 < B) (lower : B ≤ p) :
    (1:ℚ)/9 ≤ 1-base B^p := by
  let r := base B
  have bound := bounds pos
  have bp : (0:ℚ) < B := by exact_mod_cast pos
  have pb : (B:ℚ) ≤ p := by exact_mod_cast lower
  have power : 0 ≤ r^p := pow_nonneg bound.1 p
  have each : ∀ i ∈ range p, r^p ≤ r^i := fun i hi =>
    pow_le_pow_of_le_one bound.1 bound.2 (mem_range.mp hi).le
  have all := sum_le_sum each
  simp only [sum_const, card_range, nsmul_eq_mul] at all
  have partialSum : (B:ℚ)*r^p ≤ ∑ i ∈ range p, r^i :=
    (mul_le_mul_of_nonneg_right pb power).trans all
  have total := mul_le_mul_of_nonneg_right partialSum (sub_nonneg.mpr bound.2)
  have step : 1-r = 1/(8*(B:ℚ)) := by dsimp [r, base]; ring
  have scale : (B:ℚ)*(1-r) = 1/8 := by rw [step]; field_simp; ring
  have geom := geom_sum_mul r p
  change (1:ℚ)/9 ≤ 1-r^p
  nlinarith only [total, geom, congrArg (fun t : ℚ => t*r^p) scale]

/-- Every proper prefix stays at least 1/18 from the exact positive reading.
The last coefficient is needed even to attain this fixed absolute accuracy. -/
theorem error_before_sum {B p q k : ℕ} (pos : 0 < B) (hp : p.Prime) (hq : q.Prime)
    (lower : B ≤ p) (pq : p < q) (top : q < 2*B) (short : k < p+q) :
    (1:ℚ)/18 ≤ |prefixValue (p*q) k (base B) - value (p*q) (base B)| := by
  let r := base B
  have hb := bounds pos
  have qp : (1:ℚ)/2 ≤ r^q := half_le pos (by omega)
  have both : (1:ℚ)/2 ≤ r^(p+q) := half_le pos (by omega)
  have shrink : r^(p+q) ≤ r^p := pow_le_pow_of_le_one hb.1 hb.2 (by omega)
  have factor : (1:ℚ)/9 ≤ 1-r^p := missing_factor pos lower
  have product := mul_le_mul qp factor (by norm_num) (by linarith only [qp])
  change (1:ℚ)/18 ≤ |prefixValue (p*q) k r - value (p*q) r|
  rw [prefix_formula hp hq pq, value_eq hp hq pq, if_neg (by omega : ¬p+q ≤ k)]
  by_cases first : p ≤ k
  · rw [if_pos first]
    by_cases second : q ≤ k
    · rw [if_pos second]
      rw [pow_add] at both
      have negative : 1-r^p-r^q+0-(1-r^p)*(1-r^q) ≤ 0 := by nlinarith only [both]
      rw [abs_of_nonpos negative]
      nlinarith only [both]
    · rw [if_neg second]
      exact le_trans (by nlinarith only [product]) (le_abs_self _)
  · rw [if_neg first, if_neg (by omega : ¬q ≤ k)]
    rw [pow_add] at shrink
    exact le_trans (by nlinarith only [qp, shrink]) (le_abs_self _)

/-- The last degree is the exact cutoff for any error strictly below 1/18. -/
theorem accurate_iff {B p q k : ℕ} (pos : 0 < B) (hp : p.Prime) (hq : q.Prime)
    (lower : B ≤ p) (pq : p < q) (top : q < 2*B) :
    |prefixValue (p*q) k (base B) - value (p*q) (base B)| < (1:ℚ)/18 ↔ p+q ≤ k := by
  constructor
  · intro accurate
    by_contra! short
    exact (not_lt_of_ge (error_before_sum pos hp hq lower pq top short)) accurate
  · intro complete
    rw [exact_from_sum hp hq pq complete]
    norm_num

/-- Oddness removes every nonconstant term of a proper prefix when taking
the same two-reading projection used by the decoder. -/
theorem projection_before_sum {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (pq : p < q)
    (op : Odd p) (oq : Odd q) (short : k < p+q) (x : ℚ) :
    projection (prefixValue (p*q) k x) (prefixValue (p*q) k (-x)) = 0 := by
  simp only [projection, prefix_formula hp hq pq, if_neg (by omega : ¬p+q ≤ k),
    op.neg_pow, oq.neg_pow]
  split_ifs <;> ring

/-- At the chosen rational point the true projection exceeds the truncated
projection by at least one half at every degree below the sum. -/
theorem projection_gap {B p q k : ℕ} (pos : 0 < B) (hp : p.Prime) (hq : q.Prime)
    (pq : p < q) (top : q < 2*B) (op : Odd p) (oq : Odd q) (short : k < p+q) :
    (1:ℚ)/2 ≤ projection (value (p*q) (base B)) (value (p*q) (-(base B))) -
      projection (prefixValue (p*q) k (base B)) (prefixValue (p*q) k (-(base B))) := by
  rw [projection_before_sum hp hq pq op oq short, sub_zero, exponent hp hq pq op oq]
  exact half_le pos (by omega)

/-- Counting every degree, including zero, gives a lower bound of 2B+2
coefficient positions for this literal prefix evaluation. -/
theorem dense_slots {B p q k : ℕ} (pos : 0 < B) (hp : p.Prime) (hq : q.Prime)
    (lower : B ≤ p) (pq : p < q) (top : q < 2*B)
    (accurate : |prefixValue (p*q) k (base B) - value (p*q) (base B)| < (1:ℚ)/18) :
    2*B+2 ≤ (range (k+1)).card := by
  have stop := (accurate_iff pos hp hq lower pq top).mp accurate
  rw [card_range]
  omega

theorem cutoff_551 (k : ℕ) :
    |prefixValue 551 k (base 16) - value 551 (base 16)| < (1:ℚ)/18 ↔ 48 ≤ k :=
  accurate_iff (B:=16) (p:=19) (q:=29) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

end PrimeFactors.InverseCyclotomicTruncation
