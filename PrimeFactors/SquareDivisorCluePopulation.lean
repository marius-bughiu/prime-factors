import PrimeFactors.FourSquareDivisorClues

/-! Transfer the square-divisor residue counts to the 2,048-bit prime-pair
population outside explicit exceptional sets. -/
namespace PrimeFactors.SquareDivisorCluePopulation

open Finset MixedPrefixSample FourNeighborScaleFrequency
set_option exponentiation.threshold 4096
attribute [local irreducible] X primes ordered

private theorem sample_data {p q : ℕ} (ok : (p,q) ∈ eligible) :
    Odd p ∧ Odd q ∧ p < q ∧ 2^2047 ≤ p*q := by
  rw [eligible,sample,mem_filter] at ok
  obtain ⟨pm,qm,_,full,_⟩ := mem_ordered.mp ok.1
  rw [primes,mem_filter,mem_Ico] at pm qm
  have pl : X ≤ p := pm.1.1
  have ql : X ≤ q := qm.1.1
  have big : 2 < X := by unfold X; decide +kernel
  have bound : 2*X^2 = 2^2047 := by unfold X; decide +kernel
  exact ⟨pm.2.odd_of_ne_two (by omega),qm.2.odd_of_ne_two (by omega),ok.2,bound ▸ full⟩

/-- Each supplied clue uses the labeled neighboring product F. The reference
value r is the actual sum for matching signs or the gap for opposite signs.
The count works for every even r, including the relevant one in either case. -/
theorem one_clue {p q y r : ℕ} (ok : (p,q) ∈ eligible)
    (typical : (p,q) ∉ allSigns (2^1792)) (a b : Bool) (yp : 0 < y)
    (given : y^2 ∣ neighbor a p*neighbor b q) (even : Even r) :
    2^764 ≤ (SquareDivisorClueWindow.sums (p*q) y r).card ∧
    2^767 ≤ (SquareDivisorClueWindow.gaps (p*q) y r).card := by
  obtain ⟨op,oq,_,full⟩ := sample_data ok
  exact SquareDivisorClueWindow.counts full yp (SquareDivisorClueWindow.four_dvd_neighbors a b op oq)
    given (fun _ hy => square_roots_small ok typical a b hy) even

private theorem small_roots {p q R L : ℕ} (ok : (p,q) ∈ eligible)
    (typical : (p,q) ∉ allSigns L) (rp : 0<R) (budget : 2^1024*2^1024 ≤ L*R^2)
    (a b : Bool) (y : ℕ) (given : y^2 ∣ neighbor a p*neighbor b q) : y<R := by
  by_contra! large
  exact typical (large_square_divisor ok a b given large rp budget)

/-- Outside the exceptional set of relative size less than 2^-13, even the
four supplied divisors together leave at least 2^514 compatible sums. -/
theorem four_clues_64 {p q : ℕ} (ok : (p,q) ∈ eligible)
    (typical : (p,q) ∉ allSigns (2^1920)) (r : Bool → Bool → ℕ)
    (positive : ∀ a b, 0<r a b) (given : ∀ a b, (r a b)^2 ∣ neighbor a p*neighbor b q) :
    2^514 ≤ (FourSquareDivisorClues.survivors (p*q) (p+q) (q-p) r).card := by
  obtain ⟨op,oq,order,full⟩ := sample_data ok
  exact FourSquareDivisorClues.count_64 r full order.le op oq positive given
    (small_roots ok typical (by positivity) (by decide +kernel))

/-- A weaker survivor bound holds with exceptional fraction below 2^-45. -/
theorem four_clues_96 {p q : ℕ} (ok : (p,q) ∈ eligible)
    (typical : (p,q) ∉ allSigns (2^1856)) (r : Bool → Bool → ℕ)
    (positive : ∀ a b, 0<r a b) (given : ∀ a b, (r a b)^2 ∣ neighbor a p*neighbor b q) :
    2^258 ≤ (FourSquareDivisorClues.survivors (p*q) (p+q) (q-p) r).card := by
  obtain ⟨op,oq,order,full⟩ := sample_data ok
  exact FourSquareDivisorClues.count_96 r full order.le op oq positive given
    (small_roots ok typical (by positivity) (by decide +kernel))

end PrimeFactors.SquareDivisorCluePopulation
