import PrimeFactors.ShortRowPopulation

/-! Integer square-root block dimensions for the inclusive smaller-factor search.
A length W is charged ceil(sqrt W), the smallest side of a square covering W
positions. Work inside a product tree and elapsed machine time are separate costs. -/

namespace PrimeFactors.ShortRowBatchCost

open Finset ShortRowPopulation MixedPrefixSample

set_option exponentiation.threshold 8192

/-- Balanced square-block side charged before using the partner's bit length. -/
def ratioSide : ℕ×ℕ → ℕ := ceilSqrt ∘ ratioPrice

/-- Balanced square-block side charged after using the partner's bit length. -/
def partnerSide : ℕ×ℕ → ℕ := ceilSqrt ∘ partnerPrice

private theorem previous_sq (w : ℕ) : (ceilSqrt w-1)^2 ≤ w := by
  cases w with
  | zero => decide
  | succ w =>
    simp only [ceilSqrt,Nat.add_sub_cancel]
    exact (Nat.sqrt_le' w).trans (Nat.le_succ _)

/-- The integer square roots in the ratio-only lower endpoint can be bounded
relative to the integer square root of the input, with rounding on both ends. -/
private theorem old_root {n : ℕ} (np : 0<n) :
    let s := n.sqrt
    let L := ceilSqrt ((n+1)/2)
    707*s≤1000*L ∧ 1000*L ≤ 708*(s+1)+1000 ∧ L≤s+1 := by
  dsimp only
  let L := ceilSqrt ((n+1)/2)
  have left : (n+1)/2≤L^2 := ceilSqrt_le_iff.mp (le_refl L)
  have sq := Nat.sqrt_le' n
  have hi : n<(n.sqrt+1)^2 := Nat.lt_succ_sqrt' n
  have enough : n≤2*((n+1)/2) := by omega
  refine ⟨(Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (by
    change (707*n.sqrt)^2 ≤ (1000*L)^2
    nlinarith only [left,sq,enough,Nat.zero_le n]),?_,?_⟩
  · rw [show (n+1)/2=(n-1)/2+1 by omega]
    change 1000*(((n-1)/2).sqrt+1) ≤ _
    have small := Nat.sqrt_le' ((n-1)/2)
    have cap : 2*((n-1)/2)≤n := by omega
    have bound : 1000*((n-1)/2).sqrt≤708*(n.sqrt+1) := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [small,hi,cap]
    omega
  · apply ceilSqrt_le_iff.mpr
    omega

/-- Uniform range of the old integer block side, with T the square-root scale
defined by X=2T². The estimate does not use the unknown prime divisors. -/
theorem side_range {n T : ℕ} (large : 20000≤T)
    (low : 2*(2*T^2)^2≤n) (top : n≤4*(2*T^2)^2) :
    908*T≤1000*ceilSqrt (ratioWidth n) ∧
      1000*ceilSqrt (ratioWidth n)≤1084*T := by
  let B := 2*T^2
  let s := n.sqrt
  let w := ratioWidth n
  let L := ceilSqrt ((n+1)/2)
  have sq : s^2≤n := Nat.sqrt_le' n
  have hi : n<(s+1)^2 := Nat.lt_succ_sqrt' n
  have Bpos : 0<B := by dsimp [B]; positivity
  change 2*B^2≤n at low
  change n≤4*B^2 at top
  have np : 0<n := (by positivity : 0<2*B^2).trans_le low
  obtain ⟨ll,lu,ls⟩ := old_root np
  change 707*s≤1000*L at ll
  change 1000*L≤708*(s+1)+1000 at lu
  change L≤s+1 at ls
  have width : w+L=s+1 := Nat.sub_add_cancel ls
  have upper : s≤2*B := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (by nlinarith only [sq,top])
  have lower : 1414*B≤1000*(s+1) :=
    (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (by nlinarith only [low,hi])
  have rr : w≤(ceilSqrt w)^2 := ceilSqrt_le_iff.mp (le_refl _)
  have t2 : 20000^2≤T^2 := Nat.pow_le_pow_left large 2
  dsimp only [B] at upper lower
  constructor
  · apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    change (908*T)^2≤(1000*ceilSqrt w)^2
    nlinarith only [rr,lower,width,lu,t2]
  · have prev := previous_sq w
    have price : 1000*(ceilSqrt w-1)≤1083*T := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [prev,upper,width,ll,t2]
    change 1000*ceilSqrt w ≤ 1084*T
    omega

private theorem upper_tangent {T w : ℕ} (large : 20000≤T) :
    1660000*T*ceilSqrt w ≤ 1000000*w+688990*T^2 := by
  have small := previous_sq w
  by_cases z : ceilSqrt w=0
  · simp [z]
  have pred : ceilSqrt w=(ceilSqrt w-1)+1 := by omega
  have budget := Nat.mul_le_mul_right T large
  have tangent : 1660000*T*(ceilSqrt w-1)≤1000000*w+688900*T^2 := by
    zify at small ⊢
    nlinarith only [small,sq_nonneg (1000*((ceilSqrt w-1:ℕ):ℤ)-830*(T:ℤ))]
  have h := congrArg (1660000*T*·) pred
  nlinarith only [h,tangent,budget,Nat.zero_le T]

private theorem lower_chord {T w : ℕ} (lo : 908*T≤1000*ceilSqrt w) (hi : 1000*ceilSqrt w≤1084*T) :
    1000000*w+984272*T^2≤1992000*T*ceilSqrt w := by
  have sq : w≤(ceilSqrt w)^2 := ceilSqrt_le_iff.mp (le_refl _)
  zify at lo hi sq ⊢
  nlinarith only [sq,mul_nonneg (sub_nonneg.mpr lo) (sub_nonneg.mpr hi)]

/-- Transfer an aggregate width improvement to aggregate integer sides on any
finite population with the stated range of old widths. -/
theorem transfer {ι : Type*} (S : Finset ι) (P R U V : ι→ℕ) {T : ℕ} (large : 20000≤T)
    (u : ∀z, U z=ceilSqrt (P z)) (v : ∀z, V z=ceilSqrt (R z))
    (saving : 10*S.sum P<7*S.sum R)
    (bounds : ∀z∈S, 908*T≤1000*V z ∧ 1000*V z≤1084*T) :
    25*S.sum U < 21*S.sum V := by
  have eachU (z : ι) : 1660000*T*U z ≤ 1000000*P z+688990*T^2 := u z ▸ upper_tangent large
  have eachV (z : ι) (hz : z∈S) : 1000000*R z+984272*T^2≤1992000*T*V z := by
    obtain ⟨lo,hi⟩ := bounds z hz
    rw [v z] at lo hi ⊢
    exact lower_chord lo hi
  have upper := sum_le_sum (s:=S) (fun z _ => eachU z)
  have lower := sum_le_sum eachV
  simp only [sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] at upper lower
  have h : T*(25*S.sum U) < T*(21*S.sum V) := by
    nlinarith only [upper,lower,saving,Nat.zero_le (S.card*T^2)]
  exact (Nat.mul_lt_mul_left (by omega : 0<T)).mp h

attribute [local irreducible] X primes eligible ordered sample

private theorem sample_range (z : ℕ×ℕ) (hz : z∈eligible) :
    908*2^511≤1000*ratioSide z ∧ 1000*ratioSide z≤1084*2^511 := by
  rw [eligible,sample] at hz
  obtain ⟨ord,_⟩ := mem_filter.mp hz
  obtain ⟨p,q,_,bounded,_⟩ := (mem_ordered (E:=fun _=>True) (z:=z)).mp ord
  have pm : z.1∈(Ico X (2*X)).filter Nat.Prime := by simpa only [primes] using p
  have qm : z.2∈(Ico X (2*X)).filter Nat.Prime := by simpa only [primes] using q
  have ptop := (mem_Ico.mp (mem_filter.mp pm).1).2.le
  have qtop := (mem_Ico.mp (mem_filter.mp qm).1).2.le
  have limit := Nat.mul_le_mul ptop qtop
  have eq : X=2*(2^511)^2 := by decide +kernel
  rw [eq] at bounded limit
  exact side_range (by decide +kernel) bounded (by nlinarith only [limit])

/-- Uniform unordered same-width prime pairs with a full-size 2048-bit product.
The mean of the new integer square-block dimension is strictly less than 84%
of the old mean, subject only to the same published unconditional prime estimate
as the width theorem. -/
theorem aggregate (analytic : AxlerEndpoints) :
    25*eligible.sum partnerSide < 21*eligible.sum ratioSide :=
  transfer eligible partnerPrice ratioPrice partnerSide ratioSide (T:=2^511) (by decide +kernel)
    (fun _ => rfl) (fun _ => rfl)
    (ShortRowPopulation.aggregate analytic) sample_range

end PrimeFactors.ShortRowBatchCost
