import PrimeFactors.SmoothSampleBound
import PrimeFactors.SharedSmoothPowers
import Mathlib.Tactic

/-! A finite Rankin bound for smoothness up to 1000. Integer inequalities
certify every rational upper estimate and their product. -/
namespace PrimeFactors.BoundedSmoothCount
open Finset

set_option maxRecDepth 1024
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

/-- Ceiling of the product of the 168 outward-rounded local upper bounds. -/
abbrev eulerCap : ℕ := 146158226894699421149079360080063550799310

/-- Search for a rational upper bound whose denominator is 65536. The
returned integer certificate is checked independently of this search. -/
private def bisect (p : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, hi => hi
  | fuel+1, lo, hi =>
    let m := (lo+hi)/2
    if m^32 ≤ p^5*(m-65536)^32 then bisect p fuel lo m else bisect p fuel m hi

private def numerator (p : ℕ) := bisect p 21 65536 (32*65536)

/-- The outward rounding used in CubicSmoothRows, here with tunable
denominator and exponent 5/32. Clearing the powers eliminates all roots. -/
private theorem local_bound {p u k : ℕ} (kp : 0<k) (large : k<u)
    (order : u^32 ≤ p^5*(u-k)^32) :
    (1-(p:ℝ)^(-(5/32:ℝ)))⁻¹ ≤ (u:ℝ)/k := by
  have kk : (0:ℝ)<k := by exact_mod_cast kp
  have ul : (k:ℝ)<u := by exact_mod_cast large
  have den : (0:ℝ)<u-k := by linarith
  have test : (u:ℝ)^32 ≤ (p:ℝ)^5*((u:ℝ)-k)^32 := by
    have h : (u:ℝ)^32 ≤ (p:ℝ)^5*((u-k:ℕ):ℝ)^32 := by exact_mod_cast order
    simpa only [Nat.cast_sub large.le] using h
  let x : ℝ := (p:ℝ)^(5/32:ℝ)
  have power : x^32=(p:ℝ)^5 := by
    dsimp only [x]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    rw [show (5/32:ℝ)*((32:ℕ):ℝ)=((5:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have pos : 0≤x := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have bound : (u:ℝ) ≤ x*(u-k) := by
    apply le_of_pow_le_pow_left₀ (by decide : 32≠0) (mul_nonneg pos den.le)
    rwa [mul_pow,power]
  have xp : 1<x := by
    apply lt_of_not_ge
    intro bad
    linarith only [kk,bound,mul_le_mul_of_nonneg_right bad den.le]
  rw [Real.rpow_neg (Nat.cast_nonneg p)]
  change (1-x⁻¹)⁻¹ ≤ _
  have x0 : 0<x := by linarith
  have gap : 0<1-x⁻¹ := by
    rw [inv_eq_one_div, sub_pos, div_lt_one x0]
    exact xp
  rw [inv_eq_one_div, div_le_iff₀ gap, inv_eq_one_div]
  rw [show (u:ℝ)/k*(1-1/x)=u*(x-1)/(k*x) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith only [bound]

private noncomputable def ps : Finset ℕ :=
  (range 1001).filter fun n => SharedSmoothPowers.trialPrime 31 n

private theorem ps_eq : ps=(1001:ℕ).primesBelow := by
  ext p
  simp [ps, Nat.primesBelow, SharedSmoothPowers.trialPrime_eq]

private theorem local_checks : ∀ p ∈ ps, 65536<numerator p ∧
    numerator p^32 ≤ p^5*(numerator p-65536)^32 := by decide +kernel

private theorem integer_product :
    ps.card=168 ∧ 65536^ps.card*(eulerCap-1) < (∏ p ∈ ps, numerator p) ∧
      (∏ p ∈ ps, numerator p) ≤ 65536^ps.card*eulerCap := by decide +kernel

/-- Finite Euler-product majorant at exponent 5/32. -/
theorem euler_1000 :
    (∏ p ∈ (1001:ℕ).primesBelow, (1-(p:ℝ)^(-(5/32:ℝ)))⁻¹) ≤ eulerCap := by
  rw [←ps_eq]
  calc
    _ ≤ ∏ p ∈ ps, ((numerator p:ℝ)/65536) := by
      apply prod_le_prod
      · intro p hp
        have pp : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primesBelow (ps_eq ▸ hp)).one_lt
        exact inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg pp (by norm_num)).le)
      · exact fun p hp => local_bound (by decide) (local_checks p hp).1 (local_checks p hp).2
    _ ≤ eulerCap := by
      rw [prod_div_distrib,prod_const,div_le_iff₀ (by positivity),mul_comm]
      exact_mod_cast integer_product.2.2

/-- Applies at every integer cutoff, including the smaller endpoints in
dyadic decompositions of signed predecessor and successor gcds. -/
theorem smooth_rankin (X : ℕ) :
    ((Nat.smoothNumbersUpTo X 1001).card:ℝ) ≤ (X:ℝ)^(5/32:ℝ)*eulerCap := by
  exact (SmoothSampleBound.rankinBound X 1000 (5/32) (by norm_num)).trans
    (mul_le_mul_of_nonneg_left euler_1000 (Real.rpow_nonneg (Nat.cast_nonneg _) _))

attribute [local irreducible] Nat.smoothNumbersUpTo

theorem smooth_blocks (k : ℕ) :
    (Nat.smoothNumbersUpTo (2^(32*k)) 1001).card ≤ 2^(5*k)*eulerCap := by
  have h := smooth_rankin (2^(32*k))
  have power : (((2^(32*k):ℕ):ℝ)^(5/32:ℝ))=(2:ℝ)^(5*k) := by
    rw [Nat.cast_pow,Nat.cast_ofNat, ←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2)]
    rw [show ((32*k:ℕ):ℝ)*(5/32)=(5*k:ℕ) by push_cast; ring,Real.rpow_natCast]
  rw [power] at h
  exact_mod_cast h

/-- A dyadic bound at arbitrary bit widths. The leading power is rounded
up to the next 32-bit block, while the Euler bound stays fixed. -/
theorem smooth_dyadic (m : ℕ) : (Nat.smoothNumbersUpTo (2^m) 1001).card ≤
    2^(5*((m+31)/32))*eulerCap := by
  apply le_trans _ (smooth_blocks ((m+31)/32))
  apply card_le_card
  intro n hn
  obtain ⟨size, smooth⟩ := Nat.mem_smoothNumbersUpTo.mp hn
  exact Nat.mem_smoothNumbersUpTo.mpr ⟨size.trans (Nat.pow_le_pow_right (by decide) (by omega)),smooth⟩

/-- The sharper integer bound before rounding to a power of two. -/
theorem smooth_1024_decimal : (Nat.smoothNumbersUpTo (2^1024) 1001).card ≤
    213610487915984814431264236986221993216229676390096562478667745602860493752369565726146560 :=
  smooth_blocks 32

/-- Fewer than 2^297 positive integers up to 2^1024 have all prime
factors at most 1000. -/
theorem smooth_1024 : (Nat.smoothNumbersUpTo (2^1024) 1001).card < 2^297 := by
  exact (smooth_blocks 32).trans_lt (by decide +kernel)

/-- The proportion of smooth integers in the full positive interval is
less than 1.19 × 10⁻²¹⁹, with denominators cleared. -/
theorem density_decimal :
    10^221*(Nat.smoothNumbersUpTo (2^1024) 1001).card < 119*2^1024 :=
  (Nat.mul_le_mul_left _ smooth_1024_decimal).trans_lt (by decide +kernel)

/-- The normalized Rankin bound itself is below 2⁻⁷²⁷ at height 2^1024,
before counting any primes or imposing a factorization algorithm. -/
theorem normalized_1024 :
    ((2:ℝ)^1024)^(5/32-1:ℝ) *
      (∏ p ∈ (1001:ℕ).primesBelow, (1-(p:ℝ)^(-(5/32:ℝ)))⁻¹) < ((2:ℝ)^727)⁻¹ := by
  have scale : ((2:ℝ)^1024)^(5/32-1:ℝ) = (2:ℝ)^(-864:ℝ) := by
    rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    norm_num
  have upper : (eulerCap:ℝ)<(2:ℝ)^137 := by
    exact_mod_cast (show eulerCap<(2:ℕ)^137 by decide +kernel)
  rw [scale]
  apply (mul_lt_mul_of_pos_left (euler_1000.trans_lt upper) (Real.rpow_pos_of_pos (by norm_num) _)).trans_eq
  rw [←Real.rpow_natCast 2 (137:ℕ),←Real.rpow_add (by norm_num : (0:ℝ)<2)]
  rw [show (-864:ℝ)+(137:ℕ)=-((727:ℕ):ℝ) by norm_num,Real.rpow_neg (by norm_num),Real.rpow_natCast]

end PrimeFactors.BoundedSmoothCount
