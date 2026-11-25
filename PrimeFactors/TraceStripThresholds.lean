import PrimeFactors.Certificate
import PrimeFactors.PartialOrder
import PrimeFactors.TraceStripPacking
import Mathlib.Tactic.ReduceModChar
import PrimeFactors.OffsetCoordinateFloor
import PrimeFactors.GroupedOffsetRowExamples

namespace PrimeFactors.TraceStripThresholds
open Finset

set_option exponentiation.threshold 8192
set_option maxRecDepth 10000

/-- Cauchy's inequality combines the per-direction squared length estimates
from `TraceStripPacking.four_width_packing`. A direction is charged once per strip. -/
theorem cross_direction {ι : Type*} (s : Finset ι) (den len cost : ι → ℝ) (X : ℝ)
    (pos : ∀ i ∈ s, 0<den i)
    (localBound : ∀ i ∈ s, den i*len i^2≤16*X*cost i) :
    (∑ i ∈ s, len i)^2 ≤ 16*X*(∑ i ∈ s, cost i)*(∑ i ∈ s, 1 / den i) := by
  have mass := sum_nonneg (s:=s) (f:=fun i => 1 / den i)
    (fun i hi => (one_div_pos.mpr (pos i hi)).le)
  have cauchy := sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (f:=fun i => den i*len i^2) (g:=fun i => 1 / den i) (r:=len)
    (fun i hi => mul_nonneg (pos i hi).le (sq_nonneg _))
    (fun i hi => (one_div_pos.mpr (pos i hi)).le)
    (fun i hi => by field_simp [(pos i hi).ne'])
  have sum := sum_le_sum localBound
  rw [←mul_sum] at sum
  exact cauchy.trans (mul_le_mul_of_nonneg_right sum mass)

/-- When the reciprocal price has been bounded by S, a fourth power removes
both square roots in the integer comparison. -/
theorem threshold {N X M S W L : ℝ} (root : X^2=N)
    (length : L^2≤16*X*M*S) (cover : W≤5*M+L) (sep : 5*M<W)
    (h : 256*N*M^2*S^2<(W-5*M)^4) : False := by
  have pos : 0≤W-5*M := by linarith
  have sq := pow_le_pow_left₀ pos (show W-5*M≤L by linarith) 2
  have fourth := pow_le_pow_left₀ (sq_nonneg (W-5*M)) (sq.trans length) 2
  rw [←root] at h
  nlinarith only [h,fourth]

/-- A weight ratio outside [1,2] has trace slope of absolute value at least
one on the balanced domain. A single strip of width D spans at most D. -/
theorem outside_width {a b N x y D : ℝ} (xp : 0<x) (ord : x≤y) (bp : 0≤b)
    (lo : x*y≤N) (hi : N≤2*(x*y)) (outside : a+1≤b ∨ 2*b+1≤a)
    (span : |(a*y+b*N/y)-(a*x+b*N/x)|≤D) : y-x≤D := by
  have yp := xp.trans_le ord
  have xy := mul_pos xp yp
  have iden : (a*y+b*N/y)-(a*x+b*N/x)=(y-x)*(a-b*(N/(x*y))) := by
    field_simp
    ring
  rw [iden] at span
  obtain ⟨neg,pos⟩ := abs_le.mp span
  rcases outside with low|high
  · have ratio : 1≤N/(x*y) := (one_le_div xy).mpr lo
    have f : a-b*(N/(x*y))≤ -1 := by nlinarith only [low,mul_le_mul_of_nonneg_left ratio bp]
    nlinarith only [neg,mul_le_mul_of_nonneg_left f (sub_nonneg.mpr ord)]
  · have ratio : N/(x*y)≤2 := (div_le_iff₀ xy).mpr hi
    have f : 1≤a-b*(N/(x*y)) := by nlinarith only [high,mul_le_mul_of_nonneg_left ratio bp]
    nlinarith only [pos,mul_le_mul_of_nonneg_left f (sub_nonneg.mpr ord)]

private theorem harmonic (j : ℕ) : (∑ i ∈ range (2^j), 1/((i:ℝ)+1))≤j+1 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    let B := (2:ℕ)^j
    have Bp : 0<(B:ℝ) := by positivity
    rw [pow_succ,Nat.mul_two,sum_range_add]
    have tail := sum_le_sum (s:=range B) (fun i _ =>
      one_div_le_one_div_of_le Bp (show (B:ℝ)≤((B+i:ℕ):ℝ)+1 by push_cast; linarith only [(show 0≤(i:ℝ) by positivity)]))
    simp only [sum_const,card_range,nsmul_eq_mul,mul_one_div_cancel Bp.ne'] at tail
    change (∑ i ∈ range B, 1/((i:ℝ)+1))≤(j:ℝ)+1 at ih
    change (∑ i ∈ range B, 1/((i:ℝ)+1)) + (∑ i ∈ range B, 1/(((B+i:ℕ):ℝ)+1)) ≤ ((j+1:ℕ):ℝ)+1
    rw [Nat.cast_add,Nat.cast_one]
    linarith only [ih,tail]

private theorem triangle (k : ℕ) :
    2*(∑ i ∈ range k, ((i:ℝ)+1))=(k:ℝ)*((k:ℝ)+1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ]; push_cast; nlinarith only [ih]

/-- c(i) counts used weight pairs with denominator i+1. The low denominator
count cap and the total number of selected pairs are sufficient. -/
theorem reciprocal_price (j tail : ℕ) (c : ℕ → ℝ) {M : ℝ}
    (nonneg : ∀ i, 0≤c i) (cap : ∀ i, c i≤(i:ℝ)+2)
    (budget : (∑ i ∈ range (2^j+tail), c i)≤M) :
    (∑ i ∈ range (2^j+tail), c i/((i:ℝ)+1))≤M/2^j+2^j/2+j+1 := by
  let B := (2:ℕ)^j
  have Bp : 0<(B:ℝ) := by positivity
  have per {i : ℕ} (hi : i∈range B) :
      c i/((i:ℝ)+1)≤c i/B+(1+1/((i:ℝ)+1)-((i:ℝ)+1)/B) := by
    have bl : (i:ℝ)+1≤B := by exact_mod_cast mem_range.mp hi
    have ip : 0<(i:ℝ)+1 := by positivity
    have order := one_div_le_one_div_of_le ip bl
    have slack := mul_nonneg (sub_nonneg.mpr (cap i)) (sub_nonneg.mpr order)
    simp only [div_eq_mul_inv,one_mul] at slack ⊢
    nlinarith only [slack,mul_inv_cancel₀ ip.ne',inv_nonneg.mpr Bp.le]
  have early := sum_le_sum (s:=range B) (fun _ hi => per hi)
  simp only [sum_add_distrib,sum_sub_distrib,←sum_div,sum_const,card_range,nsmul_eq_mul,mul_one] at early
  have late := sum_le_sum (s:=range tail) (fun i _ =>
    div_le_div_of_nonneg_left (nonneg (B+i)) Bp (show (B:ℝ)≤((B+i:ℕ):ℝ)+1 by push_cast; linarith only [(show 0≤(i:ℝ) by positivity)]))
  rw [←sum_div] at late
  have H := harmonic j
  change (∑ i ∈ range B, 1/((i:ℝ)+1))≤(j:ℝ)+1 at H
  have tr : (∑ i ∈ range B, ((i:ℝ)+1))/(B:ℝ)=((B:ℝ)+1)/2 := by
    apply (div_eq_iff Bp.ne').mpr
    nlinarith only [triangle B]
  simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,mul_one] at tr
  rw [tr] at early
  have cp : (B:ℝ)=(2:ℝ)^j := by dsimp [B]; push_cast; rfl
  rw [←cp]
  change (∑ i ∈ range (B+tail), c i/((i:ℝ)+1))≤M/B+(B:ℝ)/2+j+1
  rw [sum_range_add]
  rw [sum_range_add] at budget
  have amt := div_le_div_of_nonneg_right budget Bp.le
  rw [add_div] at amt
  linarith only [early,late,amt,H]

/-- These are arithmetic checks at M=2^e and B=2^ceil(e/2).
The note bounds the reciprocal price by M/B+B/2+ceil(log₂ B)+1. -/
def price (e : ℕ) : ℕ :=
  let j := (e+1)/2
  let B := 2^j
  2^e/B+B/2+j+1

def Separates (N W e : ℕ) : Prop :=
  5*2^e<W ∧ 256*N*(2^e)^2*(price e)^2<(W-5*2^e)^4

/-- The prime estimate is used on paper. This quantity only uses integer division. -/
def primeFloor (L U : ℕ) : ℕ := U/709-(L+706)/707

def Control (N ei ep : ℕ) : Prop :=
  let U := N.sqrt
  let L := OffsetCoordinateFloor.lower1024 N
  2^1023≤L ∧ L≤U ∧ U<2^1024 ∧ N≤2*L^2 ∧
    Separates N (U-L+1) ei ∧ Separates N (primeFloor L U) ep

theorem fresh : Control ChebyshevQuarticScale.fresh 675 662 := by
  unfold Control
  rw [show ChebyshevQuarticScale.fresh.sqrt=GroupedOffsetRowExamples.fresh.T from
    GroupedOffsetRowExamples.fresh_row.1]
  unfold Separates primeFloor price
  decide +kernel

theorem crossed : Control ChebyshevQuarticScale.crossed 676 664 := by
  unfold Control
  rw [show ChebyshevQuarticScale.crossed.sqrt=GroupedOffsetRowExamples.crossed.T from
    GroupedOffsetRowExamples.crossed_row.1]
  unfold Separates primeFloor price
  decide +kernel

/-- Two factors just below the upper limit for 1,024-bit primes. -/
def boundaryFactor (t : ℕ) : ℕ := 2^1024-t*2^512+1

/-- The expanded product keeps its certificate independent of list multiplication. -/
def boundaryProduct : ℕ := (2^1024+1)^2-1410*2^512*(2^1024+1)+100125*2^1024

private theorem certifyNear {n : ℕ} (z : ZMod n) (size : 1<n) (cap : n≤(2^512)^2)
    (half : z^(2^511)= -1) (unit : Nat.Coprime ((-1-1:ZMod n).val) n) : n.Prime := by
  apply prime_of_partial_order_cover z size (by positivity : 0<(2:ℕ)^512) cap (ps:=[2])
  · simpa only [mul_one] using Covers.cons (n:=1) 512 Nat.prime_two covers_one
  · rw [show (2:ℕ)^512=2^511*2 by decide +kernel,pow_mul,half]
    norm_num
  · intro l hl
    obtain rfl := List.mem_singleton.mp hl
    rw [show (2:ℕ)^512/2=2^511 by decide +kernel,half]
    exact unit

private theorem boundary_prime_75 : (boundaryFactor 75).Prime := by
  apply certifyNear ((3 : ZMod (boundaryFactor 75))^(2^512-75)) (by decide +kernel) (by decide +kernel)
  · rw [←pow_mul]
    unfold boundaryFactor
    reduce_mod_char
  · decide +kernel

private theorem boundary_prime_1335 : (boundaryFactor 1335).Prime := by
  apply certifyNear ((3 : ZMod (boundaryFactor 1335))^(2^512-1335)) (by decide +kernel) (by decide +kernel)
  · rw [←pow_mul]
    unfold boundaryFactor
    reduce_mod_char
  · decide +kernel

theorem boundary_factorization :
    ExactFactorization boundaryProduct [boundaryFactor 1335,boundaryFactor 75] := by
  refine ⟨by decide +kernel,?_⟩
  intro p hp
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl|rfl
  · exact boundary_prime_1335
  · exact boundary_prime_75

/-- Both primes use 1,024 bits and the product uses 2,048 bits. Its actual
equal-bit-width factor interval has fewer than 2^522 integers. -/
theorem boundary_sizes :
    2^1023≤boundaryFactor 1335 ∧ boundaryFactor 1335<boundaryFactor 75 ∧
    boundaryFactor 75<2^1024 ∧ 2^2047≤boundaryProduct ∧ boundaryProduct<2^2048 ∧
    boundaryProduct.sqrt-OffsetCoordinateFloor.lower1024 boundaryProduct+1<2^522 := by
  have root : boundaryProduct.sqrt=2^1024-705*2^512-198450 :=
    (Nat.eq_sqrt.mpr (by constructor <;> decide +kernel)).symm
  rw [root]
  decide +kernel

end PrimeFactors.TraceStripThresholds
