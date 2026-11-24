import PrimeFactors.FactorSum

namespace PrimeFactors

/-- Within the nontrivial factor-sum range, an integral square discriminant
already determines the true sum of the prime factors. -/
theorem semiprime_sum_of_square_discriminant {p q s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ordered : p ≤ q)
    (lower : 4 * (p * q) ≤ s ^ 2) (upper : s < p * q + 1)
    (square : IsSquare (s ^ 2 - 4 * (p * q))) : s = p + q := by
  obtain ⟨d, hd⟩ := square
  have eqn : s ^ 2 = 4 * (p * q) + d ^ 2 := by rw [pow_two d]; omega
  have le : d ≤ s := by
    apply Nat.mul_self_le_mul_self_iff.mp
    simpa only [← pow_two] using (show d ^ 2 ≤ s ^ 2 by omega)
  have parity : Even s ↔ Even d := calc
    Even s ↔ Even (s ^ 2) := (Nat.even_pow' (by decide)).symm
    _ ↔ Even d := by
      rw [eqn]
      simp [Nat.even_add, Nat.even_mul, Nat.even_pow, show Even (4 : ℕ) from ⟨2, rfl⟩]
  obtain ⟨x, y, hxy, prod, sum⟩ := (exists_ordered_pair_iff_square_gap (p * q) s).mpr
    ⟨d, eqn, le, (Nat.even_sub le).mpr parity⟩
  have nontrivial : 1 < x := by
    by_contra! small
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp small with rfl | rfl
    · exact (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) (by simpa using prod.symm)
    · simp at prod
      omega
  obtain ⟨rfl, rfl⟩ := ordered_semiprime_pair_unique hp hq ordered hxy nontrivial prod
  exact sum.symm

/-- A finite set of moduli isolates the true sum whenever it supplies a
quadratic nonresidue witness for the candidate's positive nonsquare discriminant.
The analytic step is to bound the primes needed to supply these witnesses. -/
theorem admissible_all_iff_semiprime_sum {p q s : ℕ} (mods : Finset ℕ)
    (hp : p.Prime) (hq : q.Prime) (ordered : p ≤ q)
    (lower : 4 * (p * q) ≤ s ^ 2) (upper : s < p * q + 1)
    (detect : let Δ := s ^ 2 - 4 * (p * q)
      0 < Δ → ¬ IsSquare Δ → ∃ ℓ ∈ mods, ℓ.Prime ∧ ℓ ≠ 2 ∧ ¬ IsSquare (Δ : ZMod ℓ)) :
    (∀ ℓ ∈ mods, AdmissibleSum ((p * q : ℕ) : ZMod ℓ) (s : ZMod ℓ)) ↔ s = p + q := by
  constructor
  · intro passes
    apply semiprime_sum_of_square_discriminant hp hq ordered lower upper
    by_contra nonsquare
    have pos : 0 < s ^ 2 - 4 * (p * q) := Nat.pos_of_ne_zero (fun h =>
      nonsquare (h ▸ ⟨0, rfl⟩))
    obtain ⟨ℓ, mem, prime, odd, rejects⟩ := detect pos nonsquare
    letI : Fact ℓ.Prime := ⟨prime⟩
    apply rejects
    simpa only [Nat.cast_sub lower, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using
      (admissibleSum_iff_isSquare odd _ _).mp (passes ℓ mem)
  · rintro rfl ℓ _
    exact admissibleSum_of_factor_pair ℓ rfl

/-- A factor ratio between one and two puts the true sum in this integer search interval. -/
theorem balanced_factorSum_bounds {p q : ℕ} (ordered : p ≤ q) (balance : q ≤ 2 * p) :
    4 * (p * q) ≤ (p + q) ^ 2 ∧ 2 * (p + q) ^ 2 ≤ 9 * (p * q) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ordered
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (show d ≤ p by omega)
  constructor <;> nlinarith [Nat.zero_le (d * d), Nat.zero_le (d * e), Nat.zero_le (e * e)]

/-- Every sum in the balanced search interval has discriminant at most half the product. -/
theorem balanced_discriminant_bound {n s : ℕ} (lower : 4 * n ≤ s ^ 2)
    (upper : 2 * s ^ 2 ≤ 9 * n) : 2 * (s ^ 2 - 4 * n) ≤ n := by
  omega

end PrimeFactors
