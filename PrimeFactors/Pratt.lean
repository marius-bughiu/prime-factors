import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Prime.Basic

namespace PrimeFactors

/-- Every prime divisor of `n` appears in `ps`. Used for the distinct primes of `p - 1`. -/
def Covers (n : ℕ) (ps : List ℕ) : Prop :=
  ∀ q, Nat.Prime q → q ∣ n → q ∈ ps

theorem covers_one : Covers 1 [] :=
  fun _ hq hdiv => (hq.not_dvd_one hdiv).elim

theorem Covers.cons {p n : ℕ} {ps : List ℕ} (e : ℕ) (hp : Nat.Prime p)
    (rest : Covers n ps) : Covers (p ^ e * n) (p :: ps) := by
  intro q hq hdiv
  apply List.mem_cons.mpr
  rcases hq.dvd_mul.mp hdiv with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h))
  · exact Or.inr (rest q hq h)

/-- Lucas's criterion with a finite list of all possible prime divisors of `p - 1`. -/
theorem prime_of_lucas_cover {p : ℕ} (g : ZMod p) {ps : List ℕ}
    (cover : Covers (p - 1) ps) (full : g ^ (p - 1) = 1)
    (proper : ∀ q ∈ ps, g ^ ((p - 1) / q) ≠ 1) : Nat.Prime p :=
  lucas_primality p g full fun q hq hd => proper q (cover q hq hd)

end PrimeFactors
