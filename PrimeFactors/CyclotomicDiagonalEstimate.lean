import PrimeFactors.CyclotomicProductCurve
import PrimeFactors.Fermat

/-! Accuracy of substituting two equal real coordinates in the single
cyclotomic reading. This estimate uses just the product and its square root. -/
namespace PrimeFactors.CyclotomicDiagonalEstimate

open Real CyclotomicProductCurve

/-- Product-only estimate at the equal-factor point. -/
noncomputable def diagonal (N B : ℝ) := trial B (sqrt N) (sqrt N)

/-- Along the balanced product curve the diagonal overestimates the response
by at least the deficit in the sum divided by 2592B. -/
theorem error_lower {B p q : ℝ} (pos : 0 < B) (low : B ≤ p) (order : p ≤ q)
    (high : q ≤ 2*B) :
    (p+q-2*sqrt (p*q))/(2592*B) ≤ diagonal (p*q) B - trial B p q := by
  have p0 := (pos.trans_le low).le
  have q0 := p0.trans order
  have small : p ≤ sqrt (p*q) := le_sqrt_of_sq_le (by
    simpa only [sq] using mul_le_mul_of_nonneg_left order p0)
  have large : sqrt (p*q) ≤ q := (sqrt_le_left q0).mpr (by
    simpa only [sq] using mul_le_mul_of_nonneg_right order q0)
  have same := mul_self_sqrt (mul_nonneg p0 q0)
  simpa only [diagonal,two_mul] using
    ordered_separation pos (low.trans small) low le_rfl large high same

theorem gap_of_accuracy {B p q : ℝ} (pos : 0 < B) (low : B ≤ p) (order : p ≤ q)
    (high : q ≤ 2*B)
    (accurate : |diagonal (p*q) B - trial B p q| ≤ 1/(8192*B)) :
    p+q-2*sqrt (p*q) ≤ 81/256 := by
  have bound := (error_lower pos low order high).trans ((le_abs_self _).trans accurate)
  calc
    _ ≤ 1/(8192*B)*(2592*B) := (div_le_iff₀ (by positivity)).mp bound
    _ = _ := by field_simp; ring

/-- Specialization to an actual prime-index polynomial, allowing an arbitrary
positive width parameter shared by the supplied value and the estimator. -/
theorem actual_gap {B : ℝ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (pq : p < q)
    (pos : 0 < B) (low : B ≤ p) (high : (q:ℝ) ≤ 2*B)
    (accurate : |diagonal (p*q : ℕ) B - reading (p*q) B| ≤ 1/(8192*B)) :
    (p:ℝ)+q-2*sqrt (p*q : ℕ) ≤ 81/256 := by
  rw [actual_value hp hq pq, Nat.cast_mul] at accurate
  rw [Nat.cast_mul]
  exact gap_of_accuracy pos low (by exact_mod_cast pq.le) high accurate

/-- Accuracy at the prescribed tolerance forces Fermat's first midpoint
to give the true pair for two distinct odd primes. -/
theorem first_midpoint {B : ℝ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (pq : p < q)
    (op : Odd p) (oq : Odd q) (pos : 0 < B) (low : B ≤ p) (high : (q:ℝ) ≤ 2*B)
    (accurate : |diagonal (p*q : ℕ) B - reading (p*q) B| ≤ 1/(8192*B)) :
    ceilSqrt (p*q) = (p+q)/2 ∧ (ceilSqrt (p*q))^2 = p*q+((q-p)/2)^2 := by
  have gap := actual_gap hp hq pq pos low high accurate
  let m := (p+q)/2
  let d := (q-p)/2
  obtain ⟨i,pi⟩ := op
  obtain ⟨j,qj⟩ := oq
  have sum : 2*m = p+q := by dsimp [m]; omega
  have small : m = p+d := by dsimp [m,d]; omega
  have large : p+2*d = q := by dsimp [d]; omega
  have square : m^2 = p*q+d^2 := by
    calc
      m^2 = (p+d)^2 := by rw [small]
      _ = p*(p+2*d)+d^2 := by ring
      _ = p*q+d^2 := by rw [large]
  have start : ceilSqrt (p*q) ≤ m := ceilSqrt_le_iff.mpr (by omega)
  have root : sqrt (p*q : ℕ) ≤ (ceilSqrt (p*q):ℝ) :=
    (sqrt_le_left (by positivity)).mpr (by exact_mod_cast ceilSqrt_le_iff.mp (le_refl (ceilSqrt (p*q))))
  have twice : 2*(m:ℝ) = p+q := by exact_mod_cast sum
  have close : m < ceilSqrt (p*q)+1 := by
    exact_mod_cast (show (m:ℝ) < ceilSqrt (p*q)+1 by linarith only [twice,root,gap])
  have eq : ceilSqrt (p*q) = m := by omega
  exact ⟨eq,eq ▸ square⟩

/-- At 551, the first midpoint succeeds although the diagonal response misses
the required tolerance even in exact real arithmetic. -/
theorem converse_551 : ceilSqrt 551 = 24 ∧ 24^2 = 551+5^2 ∧
    1/(8192*16) < |diagonal 551 16 - reading 551 16| := by
  refine ⟨by decide,by decide,?_⟩
  have actual : reading 551 16 = trial 16 19 29 :=
    actual_value (p:=19) (q:=29) (by decide) (by decide) (by decide) 16
  have low := error_lower (B:=16) (p:=19) (q:=29) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at low
  have upper : sqrt (551:ℝ) ≤ 47/2 := (sqrt_le_left (by norm_num)).mpr (by norm_num)
  rw [actual]
  apply lt_of_lt_of_le _ (le_abs_self _)
  linarith only [low,upper]

end PrimeFactors.CyclotomicDiagonalEstimate
