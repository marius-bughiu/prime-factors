import PrimeFactors.ConvergentGcdThreshold
import PrimeFactors.PowerImageWidth
import PrimeFactors.PowerRatioRemainder
import PrimeFactors.SmoothTotientTail

/-! A convergent hit with a smooth exponent requires a large smooth divisor
of the totient. All admissible LCM prefixes share this same obstruction. -/
namespace PrimeFactors.LcmConvergentObstruction

set_option exponentiation.threshold 4096

/-- The LCM of the positive integers from one through j. -/
def prefixLCM : ℕ → ℕ
  | 0 => 1
  | j+1 => (prefixLCM j).lcm (j+1)

theorem prefix_pos (j : ℕ) : 0<prefixLCM j := by
  induction j with
  | zero => decide
  | succ j ih => exact Nat.lcm_pos ih (Nat.succ_pos j)

/-- The full chain is monotone even across indices where the LCM repeats. -/
theorem prefix_dvd {i j : ℕ} (ij : i≤j) : prefixLCM i ∣ prefixLCM j := by
  induction j, ij using Nat.le_induction with
  | base => rfl
  | succ j _ ih => exact ih.trans (Nat.dvd_lcm_left ..)

theorem monotone : Monotone prefixLCM := fun _ _ h => Nat.le_of_dvd (prefix_pos _) (prefix_dvd h)

/-- Every prime divisor of a positive LCM prefix is at most its last index. -/
theorem prime_bound {p j : ℕ} (prime : p.Prime) (dv : p ∣ prefixLCM j) : p≤j := by
  induction j with
  | zero =>
    exact False.elim (prime.not_dvd_one dv)
  | succ j ih =>
    rcases prime.dvd_mul.mp (dv.trans (Nat.lcm_dvd_mul ..)) with h|h
    · exact (ih h).trans (Nat.le_succ j)
    · exact Nat.le_of_dvd (Nat.succ_pos _) h

set_option maxRecDepth 8192 in
/-- The first LCM prefix exceeding a 2048-bit product ceiling is at 1433.
The preceding prefix fits below every 2048-bit product. Both comparisons reduce in the kernel. -/
theorem cutoff : prefixLCM 1432 < 2^2047 ∧ 2^2048 < prefixLCM 1433 := by
  decide +kernel

/-- The full-size product has no effect on the last admissible prefix index. -/
theorem admissible {N j : ℕ} (lower : 2^2047≤N) (upper : N<2^2048) :
    prefixLCM j≤N ↔ j≤1432 := by
  constructor
  · intro fits
    by_contra! past
    exact (Nat.not_lt_of_ge (monotone past)) (fits.trans_lt (upper.trans cutoff.2))
  · intro before
    exact ((monotone before).trans cutoff.1.le).trans lower

theorem at_1500 : 2^2048 < prefixLCM 1500 := cutoff.2.trans_le (monotone (by decide))

/-- Mathlib uses a strict prime bound in smoothNumbers: 1501 means that
all prime divisors are at most 1500. The exact cutoff permits 1432 here. -/
theorem prefix_smooth {N j : ℕ} (size : N<2^2048) (fits : prefixLCM j≤N) :
    j≤1432 ∧ prefixLCM j∈Nat.smoothNumbers 1501 := by
  have bound : j<1433 := by
    by_contra! h
    exact (Nat.not_lt_of_ge (monotone h)) (fits.trans_lt (size.trans cutoff.2))
  refine ⟨by omega, Nat.mem_smoothNumbers'.mpr ?_⟩
  intro p hp hd
  exact (prime_bound hp hd).trans_lt (by omega)

/-- Arithmetic behind the obstruction. No primality is needed once the
totient, error, first-convergent gate and necessary approximation are supplied. -/
theorem large_gcd {N F E : ℕ} (delta : 3*N<(N-F)^2)
    (mass : 2*N≤3*F) (ex : N-F≤E) (necessary : E*F*(N-F)<N*(E.gcd F)^2) :
    2*N < (E.gcd F)^2 := by
  have three : 3*(2*N*N)≤3*(E*F*(N-F)) := calc
    _ = 3*N*(2*N) := by ring
    _ ≤ (N-F)^2*(3*F) := Nat.mul_le_mul delta.le mass
    _ ≤ 3*(E*F*(N-F)) := by
      have h := Nat.mul_le_mul_right ((N-F)*F) ex
      nlinarith only [h]
  have left : 2*N*N≤E*F*(N-F) := Nat.le_of_mul_le_mul_left three (by decide)
  have strict : N*(2*N)<N*(E.gcd F)^2 := by
    simpa only [Nat.mul_comm N (2*N)] using left.trans_lt necessary
  exact Nat.lt_of_mul_lt_mul_left strict

/-- For factors at least six, every successful exponent shares with the
product of their predecessors a divisor larger than sqrt(2N). -/
theorem convergent_gcd {p q E : ℕ} (hp : 6≤p) (hq : 6≤q)
    (ep : 0<E) (en : E≤p*q)
    (hit : ∃ i, (E:ℚ)/((p-1)*(q-1):ℕ)=((E:ℝ)/(p*q:ℕ)).convergent i) :
    2*(p*q)<(E.gcd ((p-1)*(q-1)))^2 := by
  let N := p*q
  let F := (p-1)*(q-1)
  have fp : 0<F := Nat.mul_pos (by omega) (by omega)
  have equation : N=F+(p+q-1) := PowerImageWidth.offset (by omega) (by omega)
  have fn : F≤N := by omega
  have necessary := ConvergentGcdThreshold.necessary ep fp fn hit
  have gate := (PowerRatioRemainder.remainder ep en fp hit).2
  have ex := gate.trans (Nat.mod_lt N ep).le
  have ps : 3*(p+q)≤N := by
    have a := Nat.mul_le_mul_right q hp
    have b := Nat.mul_le_mul_left p hq
    dsimp [N] at *
    nlinarith only [a,b]
  have ag : 4*N≤(p+q)^2 := by
    dsimp [N]
    exact_mod_cast (show (4:ℤ)*(p*q)≤(p+q)^2 by nlinarith only [sq_nonneg ((p:ℤ)-q)])
  have distance : N-F+1=p+q := by omega
  have delta : 3*N<(N-F)^2 := by
    rw [←distance] at ag ps
    nlinarith only [ag,ps]
  exact large_gcd delta (by omega) ex necessary

/-- Throughout the entire 2048-bit range the shared divisor exceeds 2^1024. -/
theorem full_size {p q E : ℕ} (hp : 6≤p) (hq : 6≤q)
    (width : 2^2047≤p*q) (ep : 0<E) (en : E≤p*q)
    (hit : ∃ i, (E:ℚ)/((p-1)*(q-1):ℕ)=((E:ℝ)/(p*q:ℕ)).convergent i) :
    2^1024<E.gcd ((p-1)*(q-1)) := by
  have g := convergent_gcd hp hq ep en hit
  have lo := Nat.mul_le_mul_left 2 width
  have eq : (2^1024:ℕ)^2=2*2^2047 := by decide +kernel
  by_contra! small
  have sq := Nat.pow_le_pow_left small 2
  rw [eq] at sq
  omega

attribute [local irreducible] MixedPrefixSample.eligible MixedPrefixSample.primes
  MixedPrefixSample.sample MixedPrefixSample.ordered SmoothTotientTail.exceptional

private theorem bounds {z : ℕ×ℕ} (hz : z∈MixedPrefixSample.eligible) :
    6≤z.1 ∧ 6≤z.2 ∧ 2^2047≤z.1*z.2 ∧ z.1*z.2<2^2048 := by
  open MixedPrefixSample Finset in
    rw [eligible,sample,mem_filter] at hz
    obtain ⟨inputs, _⟩ := hz
    obtain ⟨p,q,_,size,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp inputs
    have range {r : ℕ} (mem : r∈primes) : 6≤r ∧ r<2^1024 := by
      rw [primes,mem_filter] at mem
      obtain ⟨lo,hi⟩ := mem_Ico.mp mem.1
      change 2^1023≤r at lo
      change r<2*2^1023 at hi
      omega
    obtain ⟨lp,up⟩ := range p
    obtain ⟨lq,uq⟩ := range q
    have large : 2*X^2=2^2047 := by decide +kernel
    have upper := Nat.mul_lt_mul_of_lt_of_le up uq.le (by decide : 0<(2:ℕ)^1024)
    exact ⟨lp,lq,large ▸ size,upper.trans_eq (by decide +kernel)⟩

/-- This is a single population event even when the smooth exponent is allowed
to vary with the product. The threshold can be reduced to reuse a tail estimate. -/
theorem smooth_hit {B E T : ℕ} {z : ℕ×ℕ} (hz : z∈MixedPrefixSample.eligible)
    (smooth : E∈Nat.smoothNumbers B) (en : E≤z.1*z.2) (threshold : T≤2^1024)
    (hit : ∃ i, (E:ℚ)/((z.1-1)*(z.2-1):ℕ)=((E:ℝ)/(z.1*z.2:ℕ)).convergent i) :
    z∈SmoothTotientTail.exceptional B T := by
  obtain ⟨p,q,width,_⟩ := bounds hz
  exact SmoothTotientTail.of_gcd hz smooth
    (threshold.trans (full_size p q width (Nat.pos_of_ne_zero smooth.1) en hit).le)

/-- Simultaneously covers every index in the public prefix-LCM experiment. -/
theorem prefix_hit {T j : ℕ} {z : ℕ×ℕ} (hz : z∈MixedPrefixSample.eligible)
    (en : prefixLCM j≤z.1*z.2) (threshold : T≤2^1024)
    (hit : ∃ i, (prefixLCM j:ℚ)/((z.1-1)*(z.2-1):ℕ)=
      ((prefixLCM j:ℝ)/(z.1*z.2:ℕ)).convergent i) :
    z∈SmoothTotientTail.exceptional 1501 T :=
  smooth_hit hz (prefix_smooth (bounds hz).2.2.2 en).2 en threshold hit

end PrimeFactors.LcmConvergentObstruction
