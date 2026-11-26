import PrimeFactors.WeightedMultiplierCoverage

/-! Direct gcd hits among the first two labels at weights one through eight.
An anchor prime dividing a label confines its partner to a short interval. -/

namespace PrimeFactors.WeightedSubsetNonunit

open Finset WeightedMultiplierPopulation
private abbrev X : ℕ := 2^1023
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

/-- A public label in any of the indicated continuous windows is a nonunit. -/
def Reached (n : ℕ) : Prop :=
  ∃ r A : ℕ, 0 < r ∧ r ≤ 8 ∧ Label r 2 A (Real.sqrt n) ∧ ¬ A.Coprime n

private def decode (t : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ :=
  let (p, r, c, e) := t
  let q := (c^2*p-e)/(4*r)
  (min p q, max p q)

private def choices : Finset (ℕ × ℕ × ℕ × ℕ) :=
  range (2*X) ×ˢ range 9 ×ˢ range 15 ×ˢ range 1296

attribute [local irreducible] choices

private theorem encode {p q r A : ℕ} (small : X ≤ p) (large : p < 2*X)
    (rp : 0 < r) (rc : r ≤ 8)
    (top : Real.sqrt (p*q : ℕ) ≤ 2*(2:ℝ)^1023)
    (label : Label r 2 A (Real.sqrt (p*q : ℕ))) (div : p ∣ A) :
    (min p q,max p q) ∈ choices.image decode := by
  have cap : r ≤ 3^2 := by omega
  have room : 24*2 ≤ 3*X := by decide +kernel
  have ttop : Real.sqrt (p*q : ℕ) ≤ 2*(X : ℝ) := by exact_mod_cast top
  have labelBound := first_lt rp cap room (Real.sqrt_nonneg _) ttop label
  obtain ⟨c, hA⟩ := div
  have pp : 0 < p := lt_of_lt_of_le (by decide +kernel : 0 < X) small
  have csmall : c < 15 := by
    by_contra! largeC
    have d := Nat.mul_le_mul small largeC
    rw [hA] at labelBound
    omega
  obtain ⟨bot, hi⟩ := excess rp cap room (Real.sqrt_nonneg _) ttop label
  rw [hA] at bot hi
  rw [Real.sq_sqrt (by positivity)] at bot hi
  push_cast at bot hi
  have le : 4*r*(p*q) ≤ (p*c)^2 := by exact_mod_cast (sub_nonneg.mp bot)
  have lt : (p*c)^2 < 4*r*(p*q) + 1296*X := by
    have bo : ((p:ℝ)*c)^2 < 4*r*(p*q) + 1296*(2:ℝ)^1023 := by linarith only [hi]
    exact_mod_cast bo
  have le' : 4*r*q ≤ c^2*p := by
    have mult : p*(4*r*q) ≤ p*(c^2*p) := by convert le using 1 <;> ring
    exact Nat.le_of_mul_le_mul_left mult pp
  let e := c^2*p - 4*r*q
  have eq : c^2*p = 4*r*q + e := (Nat.add_sub_of_le le').symm
  have esmall : e < 1296 := by
    apply lt_of_not_ge
    intro tooLarge
    have big := Nat.mul_le_mul tooLarge small
    have calc₁ : (p*c)^2 = 4*r*(p*q) + e*p := by
      linear_combination p*eq
    omega
  apply mem_image.mpr
  refine ⟨(p,r,c,e), ?_, ?_⟩
  · simp only [choices, mem_product, mem_range]
    exact ⟨large, (by omega), csmall, esmall⟩
  · have back : (c^2*p-e)/(4*r) = q := by
      rw [eq, Nat.add_sub_cancel]
      exact Nat.mul_div_cancel_left q (by omega)
    simp [decode, back]

attribute [local irreducible] MixedPrefixSample.ordered MixedPrefixSample.primes MixedPrefixSample.X

private theorem cover : MixedPrefixSample.sample Reached ⊆ choices.image decode := by
  intro z hz
  obtain ⟨hp, hq, order, top, r, A, rp, rc, label, nonunit⟩ :=
    WeightedMultiplierCoverage.sample_data (E := Reached) (z := z) hz
  rw [MixedPrefixSample.sample, mem_filter] at hz
  have hm := (MixedPrefixSample.mem_ordered (E := Reached) (z := z)).mp hz.1
  have pr := hm.1
  have qr := hm.2.1
  rw [MixedPrefixSample.primes, mem_filter, mem_Ico] at pr qr
  unfold MixedPrefixSample.X at pr qr
  have orient : z = (min z.1 z.2,max z.1 z.2) := by simp [min_eq_left order.le,max_eq_right order.le]
  rw [orient]
  by_cases pdiv : z.1 ∣ A
  · exact encode pr.1.1 pr.1.2 rp rc top label pdiv
  · have qdiv : z.2 ∣ A := by
      apply Classical.byContradiction
      intro hqdiv
      exact nonunit ((hp.coprime_iff_not_dvd.mpr pdiv).symm.mul_right
        (hq.coprime_iff_not_dvd.mpr hqdiv).symm)
    rw [mul_comm z.1 z.2] at label top
    rw [min_comm z.1, max_comm z.1]
    exact encode qr.1.1 qr.1.2 rp rc top label qdiv

/-- Among all eligible unordered prime pairs fewer than one in 2^980 has
a nonunit in these windows. The numerator even allows every label in the
continuous rounding bands. -/
theorem eligible_coverage : 2^980*(MixedPrefixSample.sample Reached).card <
    MixedPrefixSample.eligible.card := by
  have size : (MixedPrefixSample.sample Reached).card ≤ (2*X)*(9*(15*1296)) := by
    apply (card_le_card cover).trans
    apply card_image_le.trans
    simp only [choices, card_product, card_range, le_refl]
  have numeric : 21000000*(2^980*((2*X)*(9*(15*1296)))) ≤ 2^2046 := by decide +kernel
  have small := (Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left (2^980) size)).trans numeric
  exact Nat.lt_of_mul_lt_mul_left (small.trans_lt ChebyshevPrimeSample.eligible_count)

end PrimeFactors.WeightedSubsetNonunit
