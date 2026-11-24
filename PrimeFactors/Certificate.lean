import Mathlib.Data.Nat.Factors

namespace PrimeFactors

/-- An exact factorization accounts for the whole input, including repeated primes. -/
def ExactFactorization (n : ℕ) (factors : List ℕ) : Prop :=
  factors.prod = n ∧ ∀ p ∈ factors, Nat.Prime p

theorem exactFactorization_nil : ExactFactorization 1 [] := by
  simp [ExactFactorization]

theorem ExactFactorization.cons {p n : ℕ} {ps : List ℕ} (hp : Nat.Prime p)
    (hs : ExactFactorization n ps) : ExactFactorization (p * n) (p :: ps) := by
  refine ⟨by simp [hs.1], ?_⟩
  intro q hq
  rcases List.mem_cons.mp hq with rfl | h
  · exact hp
  · exact hs.2 q h

/-- The certificate gives exactly mathlib's prime factors, up to ordering. -/
theorem ExactFactorization.perm_primeFactorsList {n : ℕ} {ps : List ℕ}
    (h : ExactFactorization n ps) : ps.Perm n.primeFactorsList :=
  Nat.primeFactorsList_unique h.1 h.2

example : ExactFactorization 12 [2, 2, 3] :=
  ExactFactorization.cons Nat.prime_two
    (.cons Nat.prime_two (.cons Nat.prime_three exactFactorization_nil))

end PrimeFactors
