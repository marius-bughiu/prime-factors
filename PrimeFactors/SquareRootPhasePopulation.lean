import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.QuantileResidueBins
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Bounds

/-! Finite transfer for leading fractional bits of the ordinary square root.
The exponential-sum and Erdős–Turán estimates are analytic premises. The
normalizing prime-pair count and the prime marginal bound are unconditional. -/
namespace PrimeFactors.SquareRootPhasePopulation
open Finset MixedPrefixSample
set_option exponentiation.threshold 8192

/-- The product of the primes in (x,2x) divides the central binomial coefficient. -/
theorem prime_upper {x k : ℕ} (power : x=2^k) (xp : 0<x) (S : Finset ℕ)
    (range : ∀ p∈S, x<p ∧ p<2*x ∧ p.Prime) : k*S.card≤2*x := by
  have divisor := Finset.prod_primes_dvd (s:=S) ((x+x).choose x)
    (fun p hp => Nat.prime_iff.mp (range p hp).2.2)
    (fun p hp => (range p hp).2.2.dvd_choose_add (range p hp).1 (range p hp).1
      (by have h := (range p hp).2.1; omega))
  have lower : x^S.card≤∏ p∈S, p := by
    simpa using Finset.prod_le_prod' (s:=S) (f:=fun _ => x) (g:=id) (fun i hi => (range i hi).1.le)
  have uq := Nat.le_of_dvd (Nat.choose_pos (show x≤x+x by omega)) divisor
  have full := lower.trans (uq.trans (Nat.choose_le_two_pow (x+x) x (by omega)).le)
  rw [power,←pow_mul] at full
  have := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp full
  omega

/-- Public normalization pays fewer than 41056 first-prime choices per unit
of mass at scale x. -/
theorem marginal : X*primes.card < 41056*eligible.card := by
  have xp : 2<X := by decide +kernel
  have composite : ¬X.Prime := Nat.not_prime_of_dvd_of_lt
    (show 2∣X by exact dvd_pow_self _ (by decide : 1023≠0)) le_rfl xp
  have cnt := prime_upper (x:=X) (k:=1023) rfl (by omega) primes (by
    intro p hp
    obtain ⟨range,prime⟩ := Finset.mem_filter.mp hp
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp range
    exact ⟨lt_of_le_of_ne lo (fun eq => composite (eq ▸ prime)),hi,prime⟩)
  have den : X*X<21000000*eligible.card := by
    change 2^1023*2^1023<_
    rw [←pow_add]
    exact ChebyshevPrimeSample.eligible_count
  have times := Nat.mul_le_mul_left X cnt
  nlinarith only [times,den,Nat.zero_le eligible.card]

/-- The numeric substitution after bounding the harmonic sums at H=2^329.
E is the error for a region, divided by the whole eligible population. -/
theorem discrepancy {E : ℝ} (analytic :
    E≤1/(2:ℝ)^329 +6*41056/(2:ℝ)^347 +3*41056*25000/(2:ℝ)^511) :
    (2:ℝ)^328*E<1 := by
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left analytic (by positivity)) (by norm_num)

/-- Convert phase-cell errors for an event and its complement into a
conditional bound. All dyadic phase cells are compared with the same
unconditional distribution of the event. -/
theorem cell_transfer {g b G B : ℕ} {d E : ℝ} (dp : 0<d)
    (base : 0<(G:ℝ)+B) (good : |(g:ℝ)-d*G|≤E) (bad : |(b:ℝ)-d*B|≤E)
    (err : 2*E<d*((G:ℝ)+B)) :
    0<(g:ℝ)+b ∧
    |(g:ℝ)/(g+b)-(G:ℝ)/(G+B)| ≤ E/(d*(G+B)) := by
  have ep : 0≤E := (abs_nonneg _).trans good
  have gp := (abs_le.mp good).2
  have gm := (abs_le.mp good).1
  have bp := (abs_le.mp bad).2
  have bm := (abs_le.mp bad).1
  by_cases occupied : 0<(g:ℝ)+b
  · refine ⟨occupied,?_⟩
    have side (u v U V : ℝ) (v0 : 0≤v) (uv : 0<u+v)
        (U0 : 0≤U) (V0 : 0≤V) (tot : 0<U+V)
        (a : u≤d*U+E) (b : d*V-E≤v) :
        u/(u+v) ≤ U/(U+V)+E/(d*(U+V)) := by
      let t := U/(U+V)+E/(d*(U+V))
      by_cases cap : t≤1
      · have t0 : 0≤t := by dsimp [t]; positivity
        have h1 := mul_le_mul_of_nonneg_left a (sub_nonneg.mpr cap)
        have h2 := mul_le_mul_of_nonneg_left b t0
        have same : t*(d*(U+V))=d*U+E := by dsimp [t]; field_simp; ring
        apply (div_le_iff₀ uv).mpr
        change u≤t*(u+v)
        nlinarith only [h1,h2,same]
      · apply le_trans ((div_le_one uv).mpr (by linarith))
          (le_of_not_ge cap)
    have gu := side g b G B (by positivity) occupied (by positivity) (by positivity) base
      (by linarith only [gp]) (by linarith only [bm])
    have bu := side b g B G (by positivity) (by linarith) (by positivity) (by positivity)
      (by linarith only [base]) (by linarith only [bp]) (by linarith only [gm])
    have total {x y : ℝ} (pos : 0<x+y) : x/(x+y)+y/(y+x)=1 := by
      rw [add_comm y x,←add_div,div_self (ne_of_gt pos)]
    have t1 := total occupied
    have t2 := total base
    rw [add_comm (B:ℝ) G] at bu t2
    rw [abs_le]
    constructor <;> linarith
  · exfalso
    nlinarith only [occupied,gm,bm,err]

/-- Every observed 300-bit cell is populated. Its conditional fraction differs
from the unconditioned fraction by less than 2⁻²⁸. -/
theorem phase_300 {g b G B : ℕ} {E : ℝ} (pop : 0<(G:ℝ)+B)
    (good : |(g:ℝ)-(1/(2:ℝ)^300)*G|≤E) (bad : |(b:ℝ)-(1/(2:ℝ)^300)*B|≤E)
    (disc : (2:ℝ)^328*E<(G:ℝ)+B) : 0<(g:ℝ)+b ∧
      |(g:ℝ)/(g+b)-(G:ℝ)/(G+B)|<1/(2:ℝ)^28 := by
  have ep : 0≤E := (abs_nonneg _).trans good
  have enough : 2*E < (1/(2:ℝ)^300)*((G:ℝ)+B) := by
    linarith only [ep,disc]
  obtain ⟨nonempty,h⟩ := cell_transfer (by positivity) pop good bad enough
  refine ⟨nonempty,h.trans_lt ((div_lt_iff₀ (by positivity)).mpr ?_)⟩
  rw [←mul_assoc,one_div_mul_one_div,←pow_add]
  linarith only [disc]

/-- Quantified smooth tilt on [1/2,2/3], retaining a discrete two-stage
prime-count error. Strict outer majority survives the phase-cell discrepancy. -/
theorem outer_majority {central global : ℝ}
    (archimedean : global ≤ 1/2 -
      (3/7)*(1-1/(2047:ℝ)^2)/(8*3550^2)+4/(10:ℝ)^145)
    (phase : |central-global|≤1/(2:ℝ)^28+1/(2:ℝ)^726) : central<1/2 := by
  have digits : 1/(2:ℝ)^28+1/(2:ℝ)^726 + 4/(10:ℝ)^145 <
      (3/7)*(1-1/(2047:ℝ)^2)/(8*3550^2) := by norm_num
  linarith only [(abs_le.mp phase).2,archimedean,digits]

/-- Exact integer comparison for the first fractional bit of a square root:
compare the scaled radicand to the square of the intervening odd integer. -/
theorem high_bit_iff {n r : ℕ} (below : r^2 ≤ n) :
    r+1 ≤ n-r^2 ↔ (2*r+1)^2 < 4*n := by
  have sum := Nat.sub_add_cancel below
  constructor
  · intro high
    nlinarith only [sum,high]
  · intro half
    by_contra! low
    have : n-r^2 ≤ r := by omega
    nlinarith only [sum,this,half]

/-- In the first Fermat midpoint, a positive squared half-gap no larger
than the preceding integer root puts the observed bit on its high side. -/
theorem near_square_high {n r d : ℕ} (midpoint : n+d^2=(r+1)^2)
    (nonzero : 0<d) (near : d^2≤r) :
    n.sqrt=r ∧ r+1≤n-r^2 := by
  have pos : 0<d^2 := by positivity
  have lo : r^2≤n := by nlinarith only [midpoint,near]
  have hi : n<(r+1)^2 := by omega
  exact ⟨(Nat.eq_sqrt'.mpr ⟨lo,hi⟩).symm,
    (high_bit_iff lo).mpr (by nlinarith only [midpoint,near])⟩

end PrimeFactors.SquareRootPhasePopulation
