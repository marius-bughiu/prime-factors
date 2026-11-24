import PrimeFactors.PhaseSeparation
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

namespace PrimeFactors

open Finset

/-- Squared Fourier bound for twice the normalized sum on a consecutive
interval. Its translate has the same squared modulus. -/
theorem weakPhase_interval_decay (length : ℕ) {N d : ℝ} (hd : 0 < d) (half : 2*d ≤ N) :
    (2/N)^2 * phaseFejer (range length) (2*Real.pi*d/N) ≤ 1/d^2 := by
  have hn : 0 < N := by linarith
  have q0 : 0 ≤ 2*d/N := by positivity
  have q1 : 2*d/N ≤ 1 := (div_le_one hn).mpr half
  have jordan := Real.le_sin_mul q0 q1
  rw [show Real.pi/2*(2*d/N) = (2*Real.pi*d/N)/2 by ring] at jordan
  have squares := mul_self_le_mul_self q0 jordan
  rw [← sq, ← sq] at squares
  have mass := phaseFejer_nonneg (range length) (2*Real.pi*d/N)
  have kernel := phaseFejer_geometric length (2*Real.pi*d/N)
  have product := mul_le_mul_of_nonneg_left squares mass
  rw [kernel] at product
  have limit := product.trans (Real.sin_sq_le_one _)
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  convert limit using 1
  ring

/-- The unnormalized tail for one sign of the frequency telescopes. -/
theorem weakPhase_square_tail {K : ℕ} (pos : 0 < K) (length : ℕ) :
    (∑ i ∈ range length, (1:ℝ)/((K:ℝ)+i+1)^2) ≤ 1/K - 1/((K:ℝ)+length) := by
  have hK : (0:ℝ) < K := by exact_mod_cast pos
  induction length with
  | zero => simp
  | succ n ih =>
    let x := (K:ℝ)+n
    have xPos : 0 < x := by dsimp [x]; positivity
    have next : 0 < x+1 := by positivity
    have term : 1/(x+1)^2 ≤ 1/x - 1/(x+1) := by
      calc
        1/(x+1)^2 ≤ 1/(x*(x+1)) := by
          apply one_div_le_one_div_of_le (mul_pos xPos next)
          nlinarith
        _ = 1/x - 1/(x+1) := by field_simp
    rw [Finset.sum_range_succ, Nat.cast_succ, ← add_assoc]
    dsimp [x] at term
    linarith

/-- Finite correlation truncation. Here f is a target coefficient magnitude,
g is a predictor coefficient magnitude at the permuted frequency, and dc
bounds their contribution at zero. -/
theorem weakPhase_heavy {ι : Type*} (head tail : Finset ι) (f g : ι → ℝ)
    {ε L dc : ℝ} (adv : 0 < ε) (massPos : 0 < L)
    (nonneg : ∀ i ∈ head, 0 ≤ f i)
    (correlation : ε ≤ dc + (∑ i ∈ head, f i*g i) + ∑ i ∈ tail, f i*g i)
    (zero : dc ≤ ε/4) (tailMass : (∑ i ∈ tail, (f i)^2) ≤ (ε/4)^2)
    (energy : (∑ i ∈ tail, (g i)^2) ≤ 1)
    (lowMass : (∑ i ∈ head, f i) ≤ 2*L) :
    ∃ i ∈ head, ε/(8*L) ≤ g i := by
  have tailSq := Finset.sum_mul_sq_le_sq_mul_sq tail f g
  have nonnegSum : 0 ≤ ∑ i ∈ tail, (f i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have tails := (mul_le_mul_of_nonneg_left energy nonnegSum)
  rw [mul_one] at tails
  have bound : (∑ i ∈ tail, f i*g i) ≤ ε/4 := by
    nlinarith only [tailSq.trans (tails.trans tailMass), adv]
  by_contra! small
  have terms := Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_left (small i hi).le (nonneg i hi))
  rw [← Finset.sum_mul] at terms
  have limit := mul_le_mul_of_nonneg_right lowMass (by positivity : 0 ≤ ε/(8*L))
  have arithmetic : 2*L*(ε/(8*L)) = ε/4 := by field_simp; ring
  rw [arithmetic] at limit
  linarith

/-- From a low harmonic k = jh, the residues ±j at the two primes already
give a factor by gcd. No modular inversion of the harmonic is needed. -/
theorem weakPhase_frequency_gcd {p q j k : ℕ} (prime : p.Prime) (odd : p ≠ 2)
    (unit : p.Coprime j) (plus : k ≡ j [MOD p]) (minus : q ∣ k+j) :
    (p*q).gcd (k+j) = q := by
  apply Nat.gcd_mul_of_coprime_of_dvd _ minus
  apply prime.coprime_iff_not_dvd.mpr
  intro bad
  have equiv := plus.add_right j
  have hj : p ∣ 2*j := by
    rw [two_mul]
    exact ((Nat.modEq_zero_iff_dvd).mp (equiv.symm.trans bad.modEq_zero_nat))
  obtain hp | hj := prime.dvd_mul.mp hj
  · exact odd (le_antisymm (Nat.le_of_dvd (by decide) hp) prime.two_le)
  · exact (prime.coprime_iff_not_dvd.mp unit) hj

/-- The integer middle-quarter sign test, positive near zero. -/
def weakPhaseSign (N t : ℕ) : Bool :=
  4*min (t%N) (N-t%N) < N

/-- The count of positive cosine signs on an odd cyclic grid. The signed
sum is consequently 1 or -1 according as the modulus is 1 or 3 mod 4. -/
theorem weakPhase_positive_count (r b : ℕ) (oddClass : b = 1 ∨ b = 3) :
    ((range (4*r+b)).filter (fun t => weakPhaseSign (4*r+b) t)).card = 2*r+1 := by
  have split : (range (4*r+b)).filter (fun t => weakPhaseSign (4*r+b) t) =
      range (r+1) ∪ Ico (4*r+b-r) (4*r+b) := by
    ext k
    simp only [mem_filter, mem_range, weakPhaseSign, decide_eq_true_eq, mem_union, mem_Ico]
    by_cases lt : k < 4*r+b
    · rw [Nat.mod_eq_of_lt lt]
      rcases le_total k (4*r+b-k) with left | right
      · rw [min_eq_left left]
        omega
      · rw [min_eq_right right]
        omega
    · omega
  have disjoint : Disjoint (range (r+1)) (Ico (4*r+b-r) (4*r+b)) := by
    rw [Finset.disjoint_left]
    intro k hk hj
    have lo := (Finset.mem_Ico.mp hj).1
    have upper := Finset.mem_range.mp hk
    omega
  rw [split, card_union_of_disjoint disjoint, card_range, Nat.card_Ico]
  omega

/-- A noisy toy oracle with a third harmonic. Its 52 correct signs out of
77 exceed chance, and the third-harmonic candidate splits the product. -/
theorem weakPhase_77 :
    ((range 77).filter (fun t => (!weakPhaseSign 77 (25*t)) = weakPhaseSign 77 (34*t))).card = 52 ∧
    (3*34)%77 = 25 ∧ 34^2%77 = 1 ∧ Nat.gcd 77 (25+3) = 7 ∧ 7*11=77 := by
  decide +kernel

end PrimeFactors
