import PrimeFactors.HighLowSumPopulation

/-! How much modular sum precision separates two possible unordered factor
endings of a fixed odd product. The inputs are finite modular observations. -/

namespace PrimeFactors.FactorEndingSeparation

open private PrimeFactors.HighLowSumPopulation.other_factor from PrimeFactors.HighLowSumPopulation

/-- The sufficient sum and product precision for distinguishing k-bit factor
endings, according to the last three bits of the product. -/
def depth (N k : ℕ) : ℕ :=
  if N%4=3 then k+1 else if N%8=5 then k+2 else 2*k-1

/-- Two modular presentations of the same sum and product must put the
first factor of one into one of the two k-bit classes of the other. -/
def Separates (N k e : ℕ) : Prop :=
  ∀ a b c d : ℤ, a*b ≡ (N:ℤ) [ZMOD (2:ℤ)^e] →
    c*d ≡ (N:ℤ) [ZMOD (2:ℤ)^e] →
    a+b ≡ c+d [ZMOD (2:ℤ)^e] →
    a ≡ c [ZMOD (2:ℤ)^k] ∨ a ≡ d [ZMOD (2:ℤ)^k]

theorem mono {N k e f : ℕ} (h : Separates N k e) (le : e≤f) : Separates N k f := by
  intro a b c d ab cd sum
  exact h a b c d (ab.of_dvd (pow_dvd_pow 2 le)) (cd.of_dvd (pow_dvd_pow 2 le))
    (sum.of_dvd (pow_dvd_pow 2 le))

/-- Difference of sums on the modular product curve, with unit denominators cleared. -/
theorem scaled_sum_difference {R : Type*} [CommRing R] (n : R) (u v : Rˣ) :
    (u:R)*v*((u+n*↑(u⁻¹))-(v+n*↑(v⁻¹))) = ((u:R)-v)*(u*v-n) := by
  linear_combination n*(v:R)*(Units.mul_inv u) - n*(u:R)*(Units.mul_inv v)

/-- Evaluating one factorization's quadratic at the other one's factor. -/
theorem difference_product (a b c d : ℤ) :
    (a-c)*(a-d)=a*((a+b)-(c+d))+(c*d-a*b) := by ring

private theorem divides_differences {a b c d M : ℤ}
    (prod : a*b ≡ c*d [ZMOD M]) (sum : a+b ≡ c+d [ZMOD M]) :
    M ∣ (a-c)*(a-d) := by
  rw [difference_product]
  exact dvd_add (dvd_mul_of_dvd_right (Int.modEq_iff_dvd.mp sum.symm) a)
    (Int.modEq_iff_dvd.mp prod)

/-- A uniform precision valid for arbitrary integral factors, even if their
difference vanishes. -/
theorem uniform (N : ℕ) {k : ℕ} (hk : 1≤k) : Separates N k (2*k-1) := by
  intro a b c d ab cd sum
  have prod := divides_differences (ab.trans cd.symm) sum
  by_cases left : (2:ℤ)^k ∣ a-c
  · exact Or.inl (Int.modEq_iff_dvd.mpr left).symm
  · right
    have bound : ¬(2:ℤ)^(k-1+1) ∣ a-c := by simpa [Nat.sub_add_cancel hk] using left
    have div := PrimeFactors.HighLowSumPopulation.other_factor bound prod
    exact (Int.modEq_iff_dvd.mpr (show (2:ℤ)^k ∣ a-d by
      simpa only [show 2*k-1-(k-1)=k by omega] using div)).symm

private theorem with_gap {N k t : ℕ} {a b c d g : ℤ}
    (gap : d-c=(2:ℤ)^t*g) (odd : Odd g)
    (ab : a*b ≡ (N:ℤ) [ZMOD (2:ℤ)^(k+t)])
    (cd : c*d ≡ (N:ℤ) [ZMOD (2:ℤ)^(k+t)])
    (sum : a+b ≡ c+d [ZMOD (2:ℤ)^(k+t)]) :
    a ≡ c [ZMOD (2:ℤ)^k] ∨ a ≡ d [ZMOD (2:ℤ)^k] := by
  have prod : c*d ≡ a*(c+d-a) [ZMOD (2:ℤ)^(k+t)] := by
    apply Int.modEq_iff_dvd.mpr
    rw [show a*(c+d-a)-c*d = -((a-c)*(a-d)) by ring]
    exact dvd_neg.mpr (divides_differences (ab.trans cd.symm) sum)
  simpa using HighLowSumPopulation.two_roots gap odd (show c+d=a+(c+d-a) by ring) prod

private theorem gap_of_half {z : ℤ} {t : ℕ} (h : z ≡ 2^t [ZMOD (2:ℤ)^(t+1)]) :
    ∃ g : ℤ, z=2^t*g ∧ Odd g := by
  obtain ⟨w,hw⟩ := Int.modEq_iff_dvd.mp h.symm
  refine ⟨2*w+1,?_,w,rfl⟩
  rw [pow_succ] at hw
  linear_combination hw

private theorem mod_four : ∀ x y : ZMod 4, x*y=3 → y-x=2 := by decide +kernel
private theorem mod_eight : ∀ x y : ZMod 8, x*y=5 → y-x=4 := by decide +kernel

theorem at_depth_all {N k : ℕ} (hk : 4≤k) : Separates N k (depth N k) := by
  unfold depth
  split_ifs with three five
  · intro a b c d ab cd sum
    have small : c*d ≡ (3:ℤ) [ZMOD 4] := (cd.of_dvd (show (4:ℤ)∣2^(k+1) from
      pow_dvd_pow 2 (by omega : 2≤k+1))).trans
      (by exact_mod_cast Int.natCast_modEq_iff.mpr (show N ≡ 3 [MOD 4] from three))
    have low : d-c ≡ (2:ℤ)^1 [ZMOD (2:ℤ)^(1+1)] := by
      apply (ZMod.intCast_eq_intCast_iff _ _ 4).mp
      push_cast
      exact mod_four _ _ (by simpa using (ZMod.intCast_eq_intCast_iff _ _ 4).mpr small)
    obtain ⟨g,gap,go⟩ := gap_of_half low
    exact with_gap gap go ab cd sum
  · intro a b c d ab cd sum
    have small : c*d ≡ (5:ℤ) [ZMOD 8] := (cd.of_dvd (show (8:ℤ)∣2^(k+2) from
      pow_dvd_pow 2 (by omega : 3≤k+2))).trans
      (by exact_mod_cast Int.natCast_modEq_iff.mpr (show N ≡ 5 [MOD 8] from five))
    have low : d-c ≡ (2:ℤ)^2 [ZMOD (2:ℤ)^(2+1)] := by
      apply (ZMod.intCast_eq_intCast_iff _ _ 8).mp
      push_cast
      exact mod_eight _ _ (by simpa using (ZMod.intCast_eq_intCast_iff _ _ 8).mpr small)
    obtain ⟨g,gap,go⟩ := gap_of_half low
    exact with_gap gap go ab cd sum
  · exact uniform N (by omega)

/-- Odd-product form for comparison with the matching lower bound. -/
theorem at_depth {N k : ℕ} (hk : 4≤k) (_odd : Odd N) : Separates N k (depth N k) :=
  at_depth_all hk

/-- The other factor matches as well, so a compatible sum determines the
unordered pair of endings. -/
theorem same_or_swapped {N k e : ℕ} (sep : Separates N k e) (enough : k≤e)
    {a b c d : ℤ} (ab : a*b ≡ (N:ℤ) [ZMOD (2:ℤ)^e])
    (cd : c*d ≡ (N:ℤ) [ZMOD (2:ℤ)^e]) (sum : a+b ≡ c+d [ZMOD (2:ℤ)^e]) :
    (a ≡ c [ZMOD (2:ℤ)^k] ∧ b ≡ d [ZMOD (2:ℤ)^k]) ∨
    (a ≡ d [ZMOD (2:ℤ)^k] ∧ b ≡ c [ZMOD (2:ℤ)^k]) := by
  have small := sum.of_dvd (pow_dvd_pow (2:ℤ) enough)
  rcases sep a b c d ab cd sum with same|swap
  · exact Or.inl ⟨same,by simpa only [add_sub_cancel_left] using small.sub same⟩
  · exact Or.inr ⟨swap,by simpa only [add_sub_cancel_left,add_sub_cancel_right] using small.sub swap⟩

end PrimeFactors.FactorEndingSeparation
