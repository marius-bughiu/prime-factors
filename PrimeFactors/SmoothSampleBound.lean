import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Tactic.NormNum

namespace PrimeFactors.SmoothSampleBound

open scoped BigOperators

/-- All modular square roots of a target in a finite ring. -/
noncomputable def roots {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] (t : R) : Finset R :=
  Finset.univ.filter fun x => x ^ 2 = t

private theorem fieldRootCount {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (t : K) : (roots t).card ≤ 2 := by
  rcases (roots t).eq_empty_or_nonempty with h | ⟨a, ha⟩
  · simp [h]
  · refine (Finset.card_le_card (show roots t ⊆ {a, -a} from ?_)).trans Finset.card_le_two
    intro x hx
    have he : x ^ 2 = a ^ 2 := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp ha).2.symm
    simpa using sq_eq_sq_iff_eq_or_eq_neg.mp he

/-- This bound includes zero and nonunits and hence also bounds the unit samples. -/
theorem crtRootCount {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hc : p.Coprime q) (t : ZMod (p * q)) : (roots t).card ≤ 4 := by
  let e := ZMod.chineseRemainder hc
  calc
    (roots t).card ≤ ((roots (e t).1) ×ˢ (roots (e t).2)).card := by
      apply Finset.card_le_card_of_injOn e _ e.injective.injOn
      intro x hx
      have he : (e x) ^ 2 = e t := by rw [← map_pow, (Finset.mem_filter.mp hx).2]
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Prod.fst he⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Prod.snd he⟩⟩
    _ ≤ 4 := by
      rw [Finset.card_product]
      exact Nat.mul_le_mul (fieldRootCount _) (fieldRootCount _)

/-- At most eight modular inputs per permitted positive smooth magnitude. -/
theorem signedRootCount {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hc : p.Coprime q) (magnitudes : Finset ℕ) :
    (magnitudes.biUnion fun n => roots (n : ZMod (p*q)) ∪ roots (-(n : ZMod (p*q)))).card ≤
      magnitudes.card * 8 := by
  refine Finset.card_biUnion_le_card_mul _ _ _ fun n _ => (Finset.card_union_le ..).trans ?_
  exact Nat.add_le_add (crtRootCount hc _) (crtRootCount hc _)

/-- Rankin's finite Euler-product upper bound. Mathlib's smoothness cutoff
is strict, so `B + 1` includes the prime `B` when `B` is prime. -/
theorem rankinBound (X B : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    ((Nat.smoothNumbersUpTo X (B + 1)).card : ℝ) ≤
      (X : ℝ) ^ σ * ∏ p ∈ (B + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  classical
  let f (n : ℕ) : ℝ := (n : ℝ) ^ (-σ)
  have hf (n : ℕ) : 0 ≤ f n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpow (p k : ℕ) : f (p ^ k) = (f p) ^ k := by
    simp only [f, Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p),
      mul_comm (k : ℝ), Real.rpow_mul_natCast (Nat.cast_nonneg p)]
  have hlt {p : ℕ} (hp : p.Prime) : f p < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_lt_zero.mpr hσ)
  have heuler := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := f) (by simp [f])
    (fun {m n} _ => by simp [f, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)])
    (fun {p} hp => by
      simp only [Real.norm_eq_abs, hpow, abs_of_nonneg (pow_nonneg (hf p) _)]
      exact summable_geometric_of_lt_one (hf p) (hlt hp)) (B + 1)).2
  let s := Nat.smoothNumbersUpTo X (B + 1)
  have hmem (n : ℕ) (hn : n ∈ s) := (Nat.mem_smoothNumbersUpTo.mp hn).2
  have hsum : ∑ n ∈ s, f n ≤ ∏ p ∈ (B + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    rw [← Finset.sum_subtype_of_mem f hmem]
    refine (sum_le_hasSum _ (fun n _ => hf _) heuler).trans_eq (Finset.prod_congr rfl ?_)
    intro p hp
    simp only [hpow]
    exact tsum_geometric_of_lt_one (hf p) (hlt (Nat.prime_of_mem_primesBelow hp))
  calc
    (s.card : ℝ) = ∑ _ ∈ s, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ s, (X : ℝ) ^ σ * f n := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (hmem n hn).1
      have hnX : (n : ℝ) ≤ X := by exact_mod_cast (Nat.mem_smoothNumbersUpTo.mp hn).1
      rw [show f n = ((n : ℝ) ^ σ)⁻¹ from Real.rpow_neg hnpos.le _]
      rw [← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hnpos _), one_mul]
      exact Real.rpow_le_rpow hnpos.le hnX hσ.le
    _ = (X : ℝ) ^ σ * ∑ n ∈ s, f n := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg X) _)

end PrimeFactors.SmoothSampleBound
