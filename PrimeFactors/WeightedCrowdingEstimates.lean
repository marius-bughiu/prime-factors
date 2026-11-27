import PrimeFactors.WeightedPrimeCrowding
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic
import Mathlib.Data.Complex.ExponentialBounds

/-! Transfer the published prime-count estimates to the finite hypotheses for
the weighted prime population. The analytic inequalities are explicit inputs. -/
namespace PrimeFactors.WeightedCrowdingEstimates
open Finset Real
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096
private abbrev U : ℕ := 2^1024
private abbrev A : ℕ := 3*U/4
private abbrev B : ℕ := 7*U/8

/-- Dusart (2010), equation (6.6), using the stronger threshold for both estimates.
See https://arxiv.org/pdf/1002.0442#page=9. -/
def Dusart := ∀ x : ℕ, 60184<x →
    (x:ℝ)/(log x-1) ≤ x.primeCounting ∧ (x.primeCounting:ℝ) ≤ x/(log x-11/10)

/-- Montgomery and Vaughan, The large sieve, Theorem 2 (1.10) with modulus 1.
See https://doi.org/10.1112/S0025579300004708. -/
def BrunTitchmarsh := ∀ n y : ℕ, 0<n → 1<y →
    ((n+y).primeCounting:ℝ)-n.primeCounting < 2*(y:ℝ)/log y

private theorem count_eq (a b : ℕ) (ab : a≤b) :
    a.primeCounting+((Ioc a b).filter Nat.Prime).card=b.primeCounting := by
  classical
  let primes (n : ℕ) := (range (n+1)).filter Nat.Prime
  have card (n : ℕ) : (primes n).card=n.primeCounting :=
    (Nat.count_eq_card_filter_range Nat.Prime (n+1)).symm
  rw [←card a,←card b]
  have cut := filter_card_add_filter_neg_card_eq_card (s:=primes b) (fun m => m≤a)
  convert cut using 2
  · congr 1
    ext p
    by_cases hp : p.Prime <;> simp [primes,hp]
    omega
  · congr 1
    ext p
    by_cases hp : p.Prime <;> simp [primes,hp]
    omega

/-- The lower and upper bounds for π give at least 2^1011 primes in this pool. -/
theorem population (dusart : Dusart) :
    2^1011 ≤ ((Icc A B).filter Nat.Prime).card := by
  have loglo {x : ℕ} (hx : 2^1023≤x) : (702:ℝ)≤log x := by
    have h := log_le_log (by positivity : 0<(2:ℝ)^1023) (by exact_mod_cast hx : (2:ℝ)^1023≤x)
    rw [log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h,log_two_gt_d9]
  have logtop (x : ℕ) (pos : (0:ℝ)<x) (le : (x:ℝ)≤2^1024) : log (x:ℝ)-1≤710 := by
    have h := log_le_log pos le
    rw [log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h,log_two_lt_d9]
  have la := loglo (x:=A) (by decide +kernel)
  have lb := loglo (x:=B) (by decide +kernel)
  have loghi := logtop B (by norm_num) (by norm_num)
  have upper := (le_div_iff₀ (sub_pos.mpr ((by norm_num : (11/10:ℝ)<702).trans_le la))).mp
    (dusart A (by decide +kernel)).2
  have lower := (div_le_iff₀ (sub_pos.mpr ((by norm_num : (1:ℝ)<702).trans_le lb))).mp
    (dusart B (by decide +kernel)).1
  have left : 700*A.primeCounting≤A := by
    have h := (mul_le_mul_of_nonneg_left
      (le_sub_iff_add_le.mpr ((by norm_num : (700:ℝ)+11/10≤702).trans la))
      (Nat.cast_nonneg A.primeCounting)).trans upper
    rw [mul_comm] at h
    exact_mod_cast h
  have right : B≤710*B.primeCounting := by
    have h := lower.trans (mul_le_mul_of_nonneg_left loghi (Nat.cast_nonneg B.primeCounting))
    rw [mul_comm] at h
    exact_mod_cast h
  have split := count_eq A B (by decide +kernel)
  have incl := card_le_card (filter_subset_filter Nat.Prime (Ioc_subset_Icc_self (a:=A) (b:=B)))
  have margin : 710*A+(700*710)*2^1011 ≤ 700*B := by decide +kernel
  omega

/-- A closed interval of length 2^507 gains at most one extra prime at its left endpoint. -/
theorem short_intervals (bt : BrunTitchmarsh) (n : ℕ) (hn : A≤n) :
    ((Icc n (n+2^507)).filter Nat.Prime).card ≤ 2^500 := by
  have hn' : 0<n := (by decide +kernel : 0<A).trans_le hn
  have bound := bt n (2^507) hn' (by decide +kernel)
  have big : (300:ℝ)≤log (2^507:ℕ) := by
    rw [Nat.cast_pow,Nat.cast_ofNat,log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [log_two_gt_d9]
  have small : 2*((2^507:ℕ):ℝ)/log (2^507:ℕ) ≤ (2:ℝ)^500 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<300) big)).mpr
    calc 2*((2^507:ℕ):ℝ) ≤ (2:ℝ)^500*300 := by norm_num
         _ ≤ _ := mul_le_mul_of_nonneg_left big (by positivity)
  have delta := count_eq n (n+2^507) (by omega)
  have less : (n+2^507).primeCounting < n.primeCounting+2^500 := by
    exact_mod_cast (sub_lt_iff_lt_add'.mp (bound.trans_le small))
  have incl : (Icc n (n+2^507)).filter Nat.Prime ⊆ insert n ((Ioc n (n+2^507)).filter Nat.Prime) := by
    intro p hp
    obtain ⟨mem,pr⟩ := mem_filter.mp hp
    obtain ⟨l,r⟩ := mem_Icc.mp mem
    rcases l.eq_or_lt with eq|gt
    · exact mem_insert.mpr (Or.inl eq.symm)
    · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨mem_Ioc.mpr ⟨gt,r⟩,pr⟩))
  have h := (card_le_card incl).trans (card_insert_le _ _)
  omega

/-- At least 2^1504 distinct products are recovered by the fixed menu after
applying the two published unconditional estimates. -/
theorem many_products (dusart : Dusart) (bt : BrunTitchmarsh) :
    2^1504 ≤ WeightedPrimeCrowding.products.card := by
  apply WeightedPrimeCrowding.many_products
  · rw [WeightedPrimeCrowding.pool_def]
    exact population dusart
  · exact short_intervals bt

end PrimeFactors.WeightedCrowdingEstimates
