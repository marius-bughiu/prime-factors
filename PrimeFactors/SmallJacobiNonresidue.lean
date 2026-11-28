import PrimeFactors.CharacterDivisorColumn

/-! A bounded prime outside the subgroup of positive Jacobi symbol gives a
coprime prime of negative symbol at the same bound. -/

namespace PrimeFactors.SmallJacobiNonresidue

/-- The prime supplied by the subgroup estimate is a unit modulo the product.
It suffices that the second of the two distinct primes is odd. -/
theorem exists_prime {p q M : ℕ} (pp : p.Prime) (qp : q.Prime) (diff : p ≠ q)
    (odd : q ≠ 2) (small : SmallPrimeOutside (p*q) M) :
    ∃ ℓ ≤ M, ℓ.Prime ∧ ℓ.Coprime (p*q) ∧ jacobiSym (ℓ : ℤ) (p*q) = -1 := by
  obtain ⟨ℓ, prime, bound, neg⟩ := CharacterDivisorColumn.bounded_prime pp qp diff odd small
  refine ⟨ℓ, bound, prime, ?_, neg⟩
  by_contra nonunit
  have zero : jacobiSym (ℓ : ℤ) (p*q) = 0 := jacobiSym.eq_zero_iff.mpr
    ⟨Nat.mul_ne_zero pp.ne_zero qp.ne_zero,
      by simpa only [Int.gcd_natCast_natCast] using nonunit⟩
  omega

end PrimeFactors.SmallJacobiNonresidue
