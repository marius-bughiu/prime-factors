import PrimeFactors.DiscriminantJacobiCharacter
import PrimeFactors.NegativeCharacterPrimeCover
import PrimeFactors.NonsquareJacobiWitness
import PrimeFactors.UnconditionalSignBudget
import PrimeFactors.Isolation
import PrimeFactors.CoprimePrefixDiscrepancy
import PrimeFactors.IntervalSievePrimeCount

/-! Separate a positive nonsquare discriminant by a prime test. The analytic
assumptions are published inequalities, distinguished from the elementary
finite estimates in the proof. -/
namespace PrimeFactors.DiscriminantPrimeSeparation

open Finset Real DiscriminantJacobiCharacter UnconditionalSignBudget

noncomputable abbrev testPrimes := NegativeCharacterPrimeCover.primes Y X

/-- The finite specializations of Rosser–Schoenfeld (1962), Corollary 1,
Theorem 5, and Frolenkov–Soundararajan (2013), Corollary 1.
The last estimate is the restriction to integer-valued characters. -/
structure PublishedEstimates : Prop where
  reciprocal : (∑ p ∈ testPrimes, 1/(p:ℝ)) ≤ log (log (X:ℝ)) - log (log (Y:ℝ)) +
    1/(2*(log (X:ℝ))^2) + 1/(2*(log (Y:ℝ))^2)
  primeCount : (testPrimes.card:ℝ)/(X:ℝ) ≤ 1.25506/log (X:ℝ)
  characterSum : ∀ (M : ℕ), 100 ≤ M → ∀ χ : DirichletCharacter ℤ M, χ ≠ 1 →
    |∑ n ∈ Icc 1 X, (χ (n:ZMod M):ℝ)| ≤ sqrt M * ((log M+6)/(Real.pi*sqrt 2)+1)

private theorem negative_budget {d : ℕ}
    (small : ∀ p : ℕ, p.Prime → p ≤ Y → 0 ≤ realSign d p) :
    ((NegativeCharacterPrimeCover.negative (realSign d) X).card:ℝ) ≤
    4/15*(X:ℝ)*(∑ p ∈ testPrimes, 1/(p:ℝ)) + testPrimes.card := by
  have cover := NegativeCharacterPrimeCover.negative_le_prime_sum (real_support d) small (X:=X)
  have div : 30 ∣ modulus d := ⟨4*d,by unfold modulus; ring⟩
  have localBound (p : ℕ) (hp : p ∈ testPrimes) :
      ((NegativeCharacterPrimeCover.units (modulus d) (X/p)).card : ℝ) ≤
        4/15*(X:ℝ)*(1/(p:ℝ))+1 := by
    have c := cofactors div (X/p)
    have pp := (mem_filter.mp hp).2
    have floor : ((X/p:ℕ):ℝ) ≤ (X:ℝ)/(p:ℝ) := by
      apply (le_div_iff₀ (show (0:ℝ)<p by exact_mod_cast pp.pos)).mpr
      exact_mod_cast Nat.div_mul_le_self X p
    apply c.trans
    rw [div_eq_mul_one_div] at floor
    linarith only [floor]
  calc
    _ ≤ ∑ p ∈ testPrimes, ((NegativeCharacterPrimeCover.units (modulus d) (X/p)).card:ℝ) := by
      exact_mod_cast cover
    _ ≤ ∑ p ∈ testPrimes, (4/15*(X:ℝ)*(1/(p:ℝ))+1) := sum_le_sum localBound
    _ = _ := by rw [sum_add_distrib,←mul_sum]; simp

set_option exponentiation.threshold 3000

/-- For positive nonsquares of the required size the cited estimates force
an odd prime witness for the raw discriminant, including its square part. -/
theorem witness (est : PublishedEstimates) {d : ℕ} (pos : 0 < d)
    (nonsquare : ¬IsSquare d) (size : d < 2^2050) :
    ∃ ℓ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≤ Y ∧ ¬IsSquare (d:ZMod ℓ) := by
  obtain ⟨a,_,cop,jac⟩ := NonsquareJacobiWitness.exists_masked pos nonsquare
  have bad : sign d a= -1 := (sign_of_unit cop.symm).trans jac
  by_cases short : modulus d ≤ Y
  · obtain ⟨ℓ,hℓ,prime,negative⟩ := negative_prime_in_period pos bad
    obtain ⟨odd,_,reject⟩ := prime_obstruction prime negative
    exact ⟨ℓ,prime,odd,hℓ.le.trans short,reject⟩
  have big := lt_of_not_ge short
  have high : modulus d < 2^2057 := by
    have := Nat.mul_lt_mul_of_pos_left size (by decide : 0<120)
    unfold modulus
    exact this.trans (by decide +kernel)
  have has : ∃ ℓ, ℓ.Prime ∧ ℓ ≤ Y ∧ realSign d ℓ < 0 := by
    by_contra! small
    have disc := CoprimePrefixDiscrepancy.discrepancy X (show 0 < modulus d by
      unfold modulus; omega)
    have count := (abs_le.mp disc).1
    have total := NegativeCharacterPrimeCover.signed_sum X (real_support d) (real_values d)
    have pv := est.characterSum (modulus d) ((by decide +kernel : 100 ≤ Y).trans big.le)
      (character d pos) (nonprincipal_of_negative pos bad)
    simp only [character_nat] at pv
    exact contradiction big high (by linarith only [count]) (negative_budget small) total
      est.reciprocal est.primeCount pv
  obtain ⟨ℓ,prime,le,negative⟩ := has
  have badSign : sign d ℓ= -1 := by
    change (sign d ℓ:ℝ) < 0 at negative
    rcases values d ℓ with h|h|h <;> first | exact h | (rw [h] at negative; norm_num at negative)
  obtain ⟨odd,_,reject⟩ := prime_obstruction prime badSign
  exact ⟨ℓ,prime,odd,le,reject⟩

/-- The product, the public lower bound for a real discriminant and the
small-prime tests isolate the true sum throughout the stated width range. -/
theorem isolates (est : PublishedEstimates) {p q s : ℕ} (pp : p.Prime) (qp : q.Prime)
    (order : p ≤ q) (realRoots : 4*(p*q) ≤ s^2) (nontrivial : s < p*q+1) (width : s < 2^1025) :
    (∀ ℓ ∈ ((Icc 3 Y).filter Nat.Prime), AdmissibleSum ((p*q:ℕ):ZMod ℓ) (s:ZMod ℓ)) ↔ s=p+q := by
  apply admissible_all_iff_semiprime_sum _ pp qp order realRoots nontrivial
  dsimp only
  intro pos nonsquare
  have sq : s^2 < 2^2050 := by
    rw [show (2:ℕ)^2050=(2^1025)^2 by rw [←pow_mul]]
    exact Nat.pow_lt_pow_left width (by decide)
  obtain ⟨ℓ,prime,odd,le,reject⟩ := witness est pos nonsquare ((Nat.sub_le ..).trans_lt sq)
  exact ⟨ℓ,mem_filter.mpr ⟨mem_Icc.mpr ⟨by have := prime.two_le; omega,le⟩,prime⟩,prime,odd,reject⟩

/-- For two primes fitting in 1024 bits, the public conditions themselves
have exactly one solution, including when the two primes coincide. -/
theorem unique_sum (est : PublishedEstimates) {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (order : p ≤ q) (width : q < 2^1024) :
    ∃! s : ℕ, (4*(p*q) ≤ s^2 ∧ s < p*q+1 ∧ s < 2^1025) ∧
      ∀ ℓ ∈ ((Icc 3 Y).filter Nat.Prime), AdmissibleSum ((p*q:ℕ):ZMod ℓ) (s:ZMod ℓ) := by
  have lower : 4*(p*q) ≤ (p+q)^2 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le order
    nlinarith [Nat.zero_le (k*k)]
  have upper : p+q < p*q+1 := by
    obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le pp.two_le
    obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le qp.two_le
    rw [ha,hb]
    nlinarith [Nat.zero_le (a*b)]
  have bits : p+q < 2^1025 := by
    rw [show (2:ℕ)^1025 = 2^1024 + 2^1024 by decide +kernel]
    omega
  refine ⟨p+q, ⟨⟨lower,upper,bits⟩, (isolates est pp qp order lower upper bits).mpr rfl⟩, ?_⟩
  rintro s ⟨⟨lo,hi,sz⟩,legal⟩
  exact (isolates est pp qp order lo hi sz).mp legal

attribute [local irreducible] IntervalSievePrimeWeights.primes

/-- Even visiting the odd primes in this family once costs more than 2^930 visits. -/
theorem prime_visits : 2^930 < (IntervalSievePrimeWeights.primes Y).card := by
  unfold Y
  have bound := IntervalSievePrimeCount.exponent_bound (k:=940) (by decide)
  have numeric : 32768 + 940*(2^930+1) < 39*(2^940/30) := by decide +kernel
  omega

/-- The false sum 200 meets the public width and parity bounds at 9523.
Three detects the squarefree part 53, but the extra factor 6² masks it
modulo three. Five rejects the original discriminant directly. -/
theorem control9523 :
    89*107=(9523:ℕ) ∧ 4*9523 ≤ (200:ℕ)^2 ∧ 200%4=(9523+1)%4 ∧
    (200^2-4*9523:ℕ)=53*6^2 ∧
    ¬IsSquare (53:ZMod 3) ∧ IsSquare (1908:ZMod 3) ∧
    ¬IsSquare (1908:ZMod 5) ∧ ¬IsSquare (1908:ZMod 27) := by
  unfold IsSquare
  decide +kernel

end PrimeFactors.DiscriminantPrimeSeparation
