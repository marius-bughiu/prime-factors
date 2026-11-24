import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring

namespace PrimeFactors

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.sigma 1 p = 1 + p := by
  simpa [Finset.sum_range_succ] using
    (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp)

/-- The divisor sum gives the sum of the factors for a product of two distinct primes. -/
theorem sigma_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ArithmeticFunction.sigma 1 (p * q) = p * q + (p + q) + 1 := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ((Nat.coprime_primes hp hq).2 hne),
    sigma_prime hp, sigma_prime hq]
  ring

/-- Recover two roots using only the product and an exact divisor sum. -/
def recoverFromSigma (n sigma : ℕ) : ℕ × ℕ :=
  let s := sigma - n - 1
  let gap := Nat.sqrt (s ^ 2 - 4 * n)
  ((s - gap) / 2, (s + gap) / 2)

theorem recoverFromSigma_correct {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    recoverFromSigma (p * q) (ArithmeticFunction.sigma 1 (p * q)) = (p, q) := by
  unfold recoverFromSigma
  rw [sigma_semiprime hp hq (Nat.ne_of_lt hlt)]
  have hs : p * q + (p + q) + 1 - p * q - 1 = p + q := by omega
  rw [hs]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hlt)
  subst q
  have hd : (p + (p + k)) ^ 2 = k ^ 2 + 4 * (p * (p + k)) := by ring
  dsimp only
  rw [hd, Nat.add_sub_cancel, Nat.sqrt_eq']
  congr 1 <;> omega

end PrimeFactors
