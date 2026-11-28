import PrimeFactors.InverseCyclotomicThreshold
import PrimeFactors.BoundedPowerMeasurement
import PrimeFactors.RoundedUnitPowers

/-! Two bounded rational readings of a public-index inverse cyclotomic
polynomial. Oddness cancels the two individual prime powers and preserves
their sum as an exponent. Evaluating the polynomial is a separate input cost. -/
namespace PrimeFactors.InverseCyclotomicMeasurements

open Polynomial InverseCyclotomicThreshold BoundedPowerMeasurement
open scoped Polynomial

set_option maxRecDepth 8192
set_option exponentiation.threshold 4096

noncomputable def polynomial (N : ℕ) : ℤ[X] := (X-1)*inversePoly N

theorem sparse {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q) :
    polynomial (p*q)=(1-X^p)*(1-X^q) := by
  rw [polynomial,binary_inverse pp qp lt]
  have g := geom_sum_mul (X : ℤ[X]) p
  linear_combination (X^q-1)*g

noncomputable def value (N : ℕ) (x : ℚ) : ℚ :=
  (polynomial N).eval₂ (Int.castRingHom ℚ) x

theorem value_eq {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q) (x : ℚ) :
    value (p*q) x=(1-x^p)*(1-x^q) := by
  simp only [value,sparse pp qp lt,eval₂_mul,eval₂_sub,eval₂_one,eval₂_pow,eval₂_X]

noncomputable def projection (a b : ℚ) := (a+b)/2-1

theorem exponent {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q)
    (op : Odd p) (oq : Odd q) (x : ℚ) :
    projection (value (p*q) x) (value (p*q) (-x))=x^(p+q) := by
  rw [projection,value_eq pp qp lt,value_eq pp qp lt,op.neg_pow,oq.neg_pow,pow_add]
  ring

/-- Both readings stay in a fixed range at every width. -/
theorem range_readings {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q)
    (op : Odd p) (oq : Odd q) {x : ℚ} (lo : 0≤x) (hi : x≤1) :
    0≤value (p*q) x ∧ value (p*q) x≤1 ∧ 1≤value (p*q) (-x) ∧ value (p*q) (-x)≤4 := by
  rw [value_eq pp qp lt,value_eq pp qp lt,op.neg_pow,oq.neg_pow]
  have pl := pow_nonneg lo p
  have ql := pow_nonneg lo q
  have ph := pow_le_one₀ lo hi (n:=p)
  have qh := pow_le_one₀ lo hi (n:=q)
  refine ⟨mul_nonneg (by linarith) (by linarith),?_,?_,?_⟩
  · exact (mul_le_mul (by linarith : 1-x^p≤1) (by linarith : 1-x^q≤1)
      (by linarith) (by decide)).trans_eq (one_mul _)
  · simpa only [mul_one] using
      (mul_le_mul (by linarith : 1≤1- -x^p) (by linarith : 1≤1- -x^q) (by decide) (by linarith))
  · exact (mul_le_mul (by linarith : 1- -x^p≤2) (by linarith : 1- -x^q≤2)
      (by linarith) (by decide)).trans_eq (by norm_num)

theorem projection_error {a b u v ε : ℚ} (ha : |a-u|≤ε) (hb : |b-v|≤ε) :
    |projection a b-projection u v|≤ε := by
  obtain ⟨al,au⟩ := abs_le.mp ha
  obtain ⟨bl,bu⟩ := abs_le.mp hb
  unfold projection
  apply abs_le.mpr
  constructor <;> linarith

/-- This decoder can use approximate powers at every comparison. The two
supplied polynomial values and the power evaluations each have their own
absolute error budget. -/
theorem recover_sum {B p q fuel : ℕ} (pos : 0<B) (pp : p.Prime) (qp : q.Prime)
    (lt : p<q) (top : q<2*B) (op : Odd p) (oq : Odd q) (room : 4*B<2^fuel)
    (a b : ℚ) (approx : ℕ→ℚ)
    (ha : |a-value (p*q) (base B)|≤tolerance B)
    (hb : |b-value (p*q) (-(base B))|≤tolerance B)
    (ea : ∀ j, j<4*B → |approx j-base B^j|≤tolerance B) :
    (read B fuel (projection a b) approx).1=p+q ∧
    (read B fuel (projection a b) approx).2≤fuel := by
  have ey := projection_error ha hb
  rw [exponent pp qp lt op oq] at ey
  exact read_spec pos (by omega) room _ _ ey ea

noncomputable def powerAt (B j : ℕ) : ℚ :=
  RoundedUnitPowers.value (RoundedUnitPowers.scale B) (RoundedUnitPowers.input B) j

/-- Fixed-point products give all the trial readings used by bisection. -/
theorem rounded_comparison {B j : ℕ} (pos : 0<B) (cap : j≤4*B) :
    |powerAt B j-base B^j| ≤ tolerance B := by
  obtain ⟨lo,hi⟩ := RoundedUnitPowers.fixed_grid pos cap
  change 0≤base B^j-powerAt B j at lo
  rw [abs_of_nonpos (by linarith : powerAt B j-base B^j≤0)]
  change base B^j-powerAt B j < tolerance B at hi
  linarith

/-- At the full target width, input errors of 2^(-1030) suffice.
Rounding to nearest with 1,029 fractional bits meets this tolerance. -/
theorem full_width {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (lo : 2^1023≤p)
    (lt : p<q) (top : q<2^1024) (a b : ℚ)
    (ha : |a-value (p*q) (base (2^1023))|≤1/2^1030)
    (hb : |b-value (p*q) (-(base (2^1023)))|≤1/2^1030) :
    (read (2^1023) 1026 (projection a b) (powerAt (2^1023))).1=p+q ∧
    (read (2^1023) 1026 (projection a b) (powerAt (2^1023))).2≤1026 := by
  have tol : tolerance (2^1023)=1/2^1030 := by unfold tolerance; norm_num
  have two : 2 < (2:ℕ)^1023 := by decide +kernel
  apply recover_sum (B:=(2:ℕ)^1023) (fuel:=1026) (by decide +kernel) pp qp lt
    (by simpa only [show (2:ℕ)*2^1023=2^1024 by decide +kernel] using top)
    (pp.odd_of_ne_two (by omega)) (qp.odd_of_ne_two (by omega))
    (by decide +kernel) a b _ (tol ▸ ha) (tol ▸ hb)
  exact fun j hj => rounded_comparison (by decide +kernel) hj.le

/-- Two publicly reproducible dyadic readings for 551. Rounding each to the
nearest 1/4096 meets the absolute error budget of 1/2048 at B=16. -/
theorem example_551 : projection (115/4096) (13699/4096)=2811/4096 ∧
    |115/4096-value 551 (base 16)|≤tolerance 16 ∧
    |13699/4096-value 551 (-(base 16))|≤tolerance 16 := by
  have e (x : ℚ) : value 551 x=(1-x^19)*(1-x^29) :=
    value_eq (by decide : Nat.Prime 19) (by decide : Nat.Prime 29) (by decide) x
  simp only [e,projection,base,tolerance]
  decide +kernel

end PrimeFactors.InverseCyclotomicMeasurements
