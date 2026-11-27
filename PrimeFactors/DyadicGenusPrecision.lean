import PrimeFactors.DivisorSum
import PrimeFactors.Fermat
import Mathlib.Tactic

/-! # An absolute-error target for the genus of a modular curve

For distinct odd primes p and q and A = 2^m, the level 8*A²*p*q has
index 12*A²*(p+1)*(q+1), 16*A cusps, and no elliptic points. The classical
genus formula and these local counts (Csirik, Wetherell and Zieve, §2) are
external. We prove the accuracy required of a supplied numerical estimate.
-/
namespace PrimeFactors.DyadicGenusPrecision

/-- The numerical genus equation with the specified index and cusp count. -/
def GenusData (a p q g : ℕ) : Prop :=
  12*g + 6*(16*a) = 12 + 12*a^2*(p+1)*(q+1)

theorem amplification {a p q g : ℕ} (data : GenusData a p q g) :
    g+8*a = 1+a^2*((p+1)*(q+1)) := by
  unfold GenusData at data
  linarith only [data]

/-- Round a supplied nonnegative genus estimate after removing the cusp term.
The divisor sum of an odd semiprime with distinct factors is a multiple of four. -/
def divisorSumEstimate (a measured : ℕ) : ℕ :=
  4*((measured+8*a+2*a^2-1)/(4*a^2))

theorem rounded {a p q g measured : ℕ} (op : Odd p) (oq : Odd q)
    (data : GenusData a p q g)
    (below : g < measured+2*a^2) (above : measured < g+2*a^2) :
    divisorSumEstimate a measured = (p+1)*(q+1) := by
  obtain ⟨u,hu⟩ := op
  obtain ⟨v,hv⟩ := oq
  let k := (u+1)*(v+1)
  have multiple : (p+1)*(q+1)=4*k := by dsimp [k]; rw [hu,hv]; ring
  have genus := amplification data
  rw [multiple] at genus ⊢
  unfold divisorSumEstimate
  congr 1
  apply Nat.div_eq_of_lt_le
  · have lo : k*(4*a^2) + 1 ≤ measured+8*a+2*a^2 := by nlinarith only [genus,below]
    omega
  · have hi : measured+8*a+2*a^2 < (k+1)*(4*a^2)+1 := by nlinarith only [genus,above]
    omega

/-- An error at most the square root of the level lies strictly within the
rounding radius once a² exceeds twice the original product. -/
theorem sqrt_error_fits {a n error : ℕ} (scale : 2*n < a^2)
    (accuracy : error^2 ≤ 8*a^2*n) : error < 2*a^2 := by
  by_contra! large
  have ha : 0<a^2 := by omega
  have lower := Nat.mul_self_le_mul_self large
  have gap := Nat.mul_lt_mul_of_pos_left scale (show 0<4*a^2 by positivity)
  nlinarith only [accuracy,lower,gap]

/-- For any fixed power saving in the exponent, increasing the level can bring
the error within the rounding radius. The error hypothesis uses only integers. -/
theorem power_error_fits {a n error t : ℕ} (ha : 0<a) (scale : (8*n)^t ≤ a^2)
    (accuracy : error^(t+1) ≤ (8*a^2*n)^t) : error < 2*a^2 := by
  have upper : error ≤ a^2 := (Nat.pow_le_pow_iff_left (Nat.succ_ne_zero t)).mp (calc
    error^(t+1) ≤ (8*a^2*n)^t := accuracy
    _ = (a^2)^t*(8*n)^t := by rw [← mul_pow]; congr 1; ring
    _ ≤ (a^2)^t*a^2 := Nat.mul_le_mul_left _ scale
    _ = (a^2)^(t+1) := (pow_succ _ _).symm)
  have pos : 0<a^2 := by positivity
  omega

/-- For a 2,048-bit product, m = 1026*t suffices for the power bound.
The amplified level is the original product shifted by 2052*t+3 bits. -/
theorem dyadic_power_scale {n : ℕ} (high : n<2^2048) (t : ℕ) :
    (8*n)^t ≤ (2^(1026*t):ℕ)^2 ∧
      8*(2^(1026*t):ℕ)^2*n = 2^(2052*t+3)*n := by
  have smaller : 8*n ≤ 2^2052 := by norm_num1 at high ⊢; omega
  have eq : (2^(1026*t):ℕ)^2 = 2^(2052*t) := by rw [← pow_mul]; congr 1; omega
  rw [eq]
  constructor
  · simpa only [← pow_mul] using Nat.pow_le_pow_left smaller t
  · rw [pow_add]; ring

/-- The only unknown input to the readout is the supplied genus estimate.
The contract states the absolute error as two inequalities on naturals. -/
theorem recover {p q a g measured error : ℕ} (pp : p.Prime) (qp : q.Prime)
    (order : p<q) (op : Odd p) (oq : Odd q) (data : GenusData a p q g)
    (scale : 2*(p*q)<a^2) (accuracy : error^2≤8*a^2*(p*q))
    (lo : g≤measured+error) (hi : measured≤g+error) :
    recoverFromSigma (p*q) (divisorSumEstimate a measured) = (p,q) := by
  have bound := sqrt_error_fits scale accuracy
  rw [rounded op oq data (by omega) (by omega)]
  have sigma := sigma_semiprime pp qp order.ne
  have eq : (p+1)*(q+1) = ArithmeticFunction.sigma 1 (p*q) := by rw [sigma]; ring
  rw [eq]
  exact recoverFromSigma_correct pp qp order

/-- Replacing the hidden factor sum in the shifted genus by the first Fermat
sum reaches the square-root error target exactly when that first sum is right. -/
theorem first_midpoint {a p q g error : ℕ} (op : Odd p) (oq : Odd q)
    (data : GenusData a p q g) (scale : 2*(p*q)<a^2)
    (accuracy : error^2 ≤ 8*a^2*(p*q)) :
    let estimate := 1+a^2*(p*q+2*ceilSqrt (p*q)+1)
    (g+8*a ≤ estimate+error ∧ estimate ≤ g+8*a+error) ↔
      p+q = 2*ceilSqrt (p*q) := by
  dsimp only
  have genus := amplification data
  have bound := sqrt_error_fits scale accuracy
  obtain ⟨u,hu⟩ := op
  obtain ⟨v,hv⟩ := oq
  constructor
  · rintro ⟨low,high⟩
    by_contra wrong
    have apart : p+q+2 ≤ 2*ceilSqrt (p*q) ∨ 2*ceilSqrt (p*q)+2 ≤ p+q := by omega
    rcases apart with smaller | bigger
    · have gap := Nat.mul_le_mul_left (a^2) smaller
      nlinarith only [high,genus,gap,bound]
    · have gap := Nat.mul_le_mul_left (a^2) bigger
      nlinarith only [low,genus,gap,bound]
  · intro correct
    have eq : (p+1)*(q+1)=p*q+2*ceilSqrt (p*q)+1 := by rw [← correct]; ring
    rw [eq] at genus
    omega

/-- At 2,048 bits A = 2^1025 suffices. Multiplying by the level multiplier
adds exactly 2,053 binary places to the original product. -/
theorem full_size {n : ℕ} (low : 2^2047≤n) (high : n<2^2048) :
    2*n < (2^1025:ℕ)^2 ∧
    2^4100 ≤ 8*(2^1025:ℕ)^2*n ∧ 8*(2^1025:ℕ)^2*n < 2^4101 := by
  norm_num1 at low high ⊢
  omega

end PrimeFactors.DyadicGenusPrecision
