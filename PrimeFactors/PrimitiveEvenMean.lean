import PrimeFactors.MixedPrefixSample
import Mathlib.Data.Real.Sqrt

/-! Algebraic consequences of the normalized first two raw moments in the
primitive-even character family. These formulas concern exact or supplied
moments; they do not estimate the cost of obtaining those moments. -/
namespace PrimeFactors.PrimitiveEvenMean

open Finset MixedPrefixSample

/-- For character-pair count T=(p−2)(q−2), the normalized mean uses U=T+1. -/
def parameter (p q : ℕ) : ℕ := (p-2)*(q-2)+1

noncomputable def mean (u : ℝ) : ℝ := 2+4/u

noncomputable def secondMoment (u : ℝ) : ℝ := 6+20/u

theorem parameter_balance {p q : ℕ} (hp : 2≤p) (hq : 2≤q) :
    parameter p q + 2*(p+q) = p*q+5 := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hq
  simp only [parameter,Nat.add_sub_cancel_left]
  ring

/-- The offset of the exact mean above two determines the family parameter. -/
theorem inverse {u : ℝ} (positive : 0<u) : 4/(mean u-2) = u := by
  rw [mean,add_sub_cancel_left,div_eq_iff (div_ne_zero (by norm_num) positive.ne')]
  field_simp

/-- Decode a proposed mean to a real factor sum at fixed product n. -/
noncomputable def sumFromMean (n m : ℝ) : ℝ := (n+5-4/(m-2))/2

theorem exact_sum {p q : ℕ} (hp : 2≤p) (hq : 2≤q) :
    sumFromMean ((p:ℝ)*q) (mean (parameter p q)) = (p:ℝ)+q := by
  have pos : 0<(parameter p q:ℝ) := by exact_mod_cast Nat.succ_pos ((p-2)*(q-2))
  have bal : (parameter p q:ℝ)+2*((p:ℝ)+q) = (p:ℝ)*q+5 := by
    exact_mod_cast parameter_balance hp hq
  rw [sumFromMean,inverse pos]
  linarith only [bal]

/-- The ordinary quadratic discriminant recovers both ordered factors from the
product and this exact mean. -/
theorem exact_factors {p q : ℕ} (hp : 2≤p) (ordered : p≤q) :
    let n := (p:ℝ)*q
    let s := sumFromMean n (mean (parameter p q))
    let d := Real.sqrt (s^2-4*n)
    (s-d)/2=(p:ℝ) ∧ (s+d)/2=(q:ℝ) := by
  dsimp only
  rw [exact_sum hp (hp.trans ordered),
    show ((p:ℝ)+q)^2-4*((p:ℝ)*q)=((q:ℝ)-p)^2 by ring,
    Real.sqrt_sq (sub_nonneg.mpr (by exact_mod_cast ordered))]
  constructor <;> ring

/-- The second raw moment gives the variance; it is strictly larger than two
whenever U>4. -/
theorem variance {u : ℝ} (hu : 4<u) :
    secondMoment u - (mean u)^2 = 2+4/u-16/u^2 ∧ 2 < secondMoment u - (mean u)^2 := by
  have pos : 0<u := by linarith
  have eq : secondMoment u - (mean u)^2 = 2+4/u-16/u^2 := by
    unfold secondMoment mean
    field_simp
    ring
  have rearrange : 2+4/u-16/u^2 = 2+4*(u-4)/u^2 := by
    field_simp
    ring
  exact ⟨eq,by rw [eq,rearrange]; exact lt_add_of_pos_right _ (div_pos
    (mul_pos (by norm_num) (sub_pos.mpr hu)) (sq_pos_of_pos pos))⟩

/-- Changing U by eight corresponds algebraically to changing the sum by four
at a fixed product. This does not assert that the second parameter is realized. -/
theorem adjacent_sums (n u : ℝ) : (n+5-(u+8))/2 = (n+5-u)/2-4 := by ring

theorem spacing {u : ℝ} (pos : 0<u) : mean u-mean (u+8) = 32/(u*(u+8)) := by
  unfold mean
  have also : 0<u+8 := by positivity
  field_simp
  ring

/-- The two algebraic predictions differ by less than 2^(-4087). -/
theorem spacing_bound {u : ℝ} (size : (2:ℝ)^2046≤u) :
    0<mean u-mean (u+8) ∧ mean u-mean (u+8)<1/(2:ℝ)^4087 := by
  have up : 0<u := (show (0:ℝ)<2^2046 by positivity).trans_le size
  have later : (2:ℝ)^2046 < u+8 := size.trans_lt (lt_add_of_pos_right _ (by norm_num))
  rw [spacing up]
  constructor
  · positivity
  · apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    rw [one_mul,show (32:ℝ)*2^4087=2^2046*2^2046 by
      rw [show (32:ℝ)=2^5 by norm_num,←pow_add,←pow_add]]
    exact (mul_le_mul_of_nonneg_right size (by positivity)).trans_lt (mul_lt_mul_of_pos_left later up)

attribute [local irreducible] X eligible ordered primes
set_option maxRecDepth 4096 in
set_option exponentiation.threshold 4096 in
/-- The sample's product-width lower bound absorbs the factor-sum correction
in U=N+5−2(p+q). -/
theorem eligible_parameter {p q : ℕ} (ok : (p,q)∈eligible) : 2^2046 ≤ parameter p q := by
  rw [eligible,sample,mem_filter] at ok
  obtain ⟨pm,qm,_,full,_⟩ := mem_ordered.mp ok.1
  rw [primes,mem_filter,mem_Ico] at pm qm
  have pu : p<2*X := pm.1.2
  have qu : q<2*X := qm.1.2
  have balanced := parameter_balance pm.2.two_le qm.2.two_le
  change parameter p q + 2*(p+q) = p*q+5 at balanced
  have fullsize : 2^2047≤p*q := by
    change 2*X^2≤p*q at full
    rwa [show 2*X^2=2^2047 by unfold X; decide +kernel] at full
  have cap : 2*(2*X+2*X) ≤ 2^2046 := by unfold X; decide +kernel
  have twice : 2*2^2046=2^2047 := by decide +kernel
  omega

end PrimeFactors.PrimitiveEvenMean
