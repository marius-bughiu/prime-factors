import PrimeFactors.FactorSumSpacingSmall
import PrimeFactors.FactorSumSpacingCRT

/-! A positive modulus admits every difference between two locally compatible factor sums
of every integer product exactly when it is coprime to 210. The single squarefree product
713 = 23 * 31 and the difference one detect all four excluded prime divisors. -/
namespace PrimeFactors.UniversalSpacing
open FactorSumSpacing

/-- Reducing both factor-pair witnesses preserves their prescribed sum difference. -/
theorem descends {m d : ℕ} (div : d∣m) (n t : ℤ) (h : Gap m n t) : Gap d n t := by
  let f := ZMod.castHom div (ZMod d)
  have admissible {s : ZMod m} (a : AdmissibleSum (n : ZMod m) s) :
      AdmissibleSum (n : ZMod d) (f s) := by
    obtain ⟨x,y,prod,sum⟩ := a
    exact ⟨f x,f y,by rw [←map_mul,prod,map_intCast],by rw [←map_add,sum]⟩
  obtain ⟨s,a,b⟩ := h
  exact ⟨f s,admissible a,by simpa only [map_add,map_intCast] using admissible b⟩

/-- The two primes 23 and 31 give a common obstruction at 2, 3, 5, and 7. -/
theorem witness :
    713=23*31 ∧ Nat.Prime 23 ∧ Nat.Prime 31 ∧
    ¬Gap 2 713 1 ∧ ¬Gap 3 713 1 ∧ ¬Gap 5 713 1 ∧ ¬Gap 7 713 1 :=
  ⟨by decide,by decide,by decide,
    (FactorSumSpacingSmall.two 713 1).mpr (by decide),
    (FactorSumSpacingSmall.three 713 1).mpr (by decide),
    (FactorSumSpacingSmall.five 713 1).mpr (by decide),
    (FactorSumSpacingSmall.seven 713 1).mpr (by decide)⟩

private theorem coprime_of_test {m : ℕ} (h : Gap m 713 1) : m.Coprime 210 := by
  obtain ⟨_,_,_,two,three,five,seven⟩ := witness
  have good {p : ℕ} (pp : p.Prime) (bad : ¬Gap p 713 1) : m.Coprime p := by
    apply (pp.coprime_iff_not_dvd.mpr ?_).symm
    intro div
    apply bad
    simpa only [Int.cast_ofNat,Int.cast_one] using
      descends div 713 1 (by simpa only [Int.cast_ofNat,Int.cast_one] using h)
  change m.Coprime (2*(3*(5*7)))
  exact Nat.coprime_mul_iff_right.mpr ⟨good Nat.prime_two two,Nat.coprime_mul_iff_right.mpr
    ⟨good Nat.prime_three three,Nat.coprime_mul_iff_right.mpr ⟨good (by decide) five,good (by decide) seven⟩⟩⟩

private theorem all_of_coprime {m : ℕ} (pos : 0<m) (cop : m.Coprime 210) (n t : ℤ) :
    Gap m n t := by
  apply all_large_prime_factors n t m pos
  intro p pp div
  by_contra! small
  have table : ∀ j : Fin 11, j.val.Prime → j.val∣210 := by decide +kernel
  have both := Nat.dvd_gcd div (table ⟨p,small⟩ pp)
  rw [cop.gcd_eq_one] at both
  exact pp.not_dvd_one both

/-- One fixed product and one fixed difference detect whether the modulus is coprime to 210. -/
theorem test_iff {m : ℕ} (pos : 0<m) : Gap m 713 1 ↔ m.Coprime 210 :=
  ⟨coprime_of_test,fun h => by simpa only [Int.cast_ofNat,Int.cast_one] using all_of_coprime pos h 713 1⟩

/-- Complete classification over arbitrary integer products and differences. -/
theorem universal_iff {m : ℕ} (pos : 0<m) : (∀ n t : ℤ, Gap m n t) ↔ m.Coprime 210 :=
  ⟨fun all => coprime_of_test (by simpa only [Int.cast_ofNat,Int.cast_one] using all 713 1),all_of_coprime pos⟩

theorem universal_iff_test {m : ℕ} (pos : 0<m) :
    (∀ n t : ℤ, Gap m n t) ↔ Gap m 713 1 := (universal_iff pos).trans (test_iff pos).symm

end PrimeFactors.UniversalSpacing
