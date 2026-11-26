import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.Ring

/-!
For a product of a prime congruent to one modulo four and a prime congruent
to three, the first normalized derivative of a translated cubic coefficient
is a single Pascal entry. Lucas's theorem identifies its gcd with the product.
-/

namespace PrimeFactors.HasseBinomialDerivative

open Polynomial

/-- The unsigned coefficient required by the normalized derivative. -/
def entry (n : ℕ) := ((n - 1) / 2).choose ((n + 1) / 4)

private theorem short_choose {p n k : ℕ} (prime : p.Prime) (small : n < p)
    (inside : k ≤ n) : ¬ p ∣ n.choose k := by
  intro h
  apply (not_le.mpr small) ∘ prime.dvd_factorial.mp
  rw [← Nat.choose_mul_factorial_mul_factorial inside]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _

private theorem units_lucas {p u v s t : ℕ} (prime : p.Prime) (u0 : u < p) (s0 : s < p) :
    (p * v + u).choose (p * t + s) ≡ u.choose s * v.choose t [MOD p] := by
  letI : Fact p.Prime := ⟨prime⟩
  simpa only [Nat.mul_add_mod, Nat.mod_eq_of_lt u0, Nat.mod_eq_of_lt s0,
    Nat.mul_add_div prime.pos, Nat.div_eq_of_lt u0, Nat.div_eq_of_lt s0, Nat.add_zero]
    using Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (n := p*v+u) (k := p*t+s) (p := p)

/-- The ordinary prime always divides the entry. For arbitrary relative
sizes, divisibility by the inert prime is determined by a smaller central
binomial coefficient. -/
theorem divisors {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (pc : p % 4 = 1) (qc : q % 4 = 3) :
    p ∣ entry (p*q) ∧
      (q ∣ entry (p*q) ↔ q ∣ ((p-1)/2).choose ((p-1)/4)) := by
  let a := p / 4
  let b := q / 4
  have pe : p = 4*a + 1 := by dsimp [a]; omega
  have qe : q = 4*b + 3 := by dsimp [b]; omega
  have rowP : (p*q-1)/2 = p*(2*b+1) + 2*a := by
    have e : p*q = 2*(p*(2*b+1) + 2*a) + 1 := by rw [pe,qe]; ring
    omega
  have columnP : (p*q+1)/4 = p*b + (3*a+1) := by
    have e : p*q+1 = 4*(p*b+(3*a+1)) := by rw [pe,qe]; ring
    omega
  have rowQ : (p*q-1)/2 = q*(2*a) + (2*b+1) := by
    have e : p*q = 2*(q*(2*a) + (2*b+1)) + 1 := by rw [pe,qe]; ring
    omega
  have columnQ : (p*q+1)/4 = q*a + (b+1) := by
    have e : p*q+1 = 4*(q*a+(b+1)) := by rw [pe,qe]; ring
    omega
  constructor
  · rw [entry, rowP, columnP, ← Nat.modEq_zero_iff_dvd]
    have lucas := units_lucas (v := 2*b+1) (t := b) pp
      (show 2*a < p by omega) (show 3*a+1 < p by have := pp.two_le; omega)
    simpa [Nat.choose_eq_zero_of_lt (show 2*a < 3*a+1 by omega)] using lucas
  · rw [entry, rowQ, columnQ, show (p-1)/2 = 2*a by omega, show (p-1)/4 = a by omega]
    have lucas := units_lucas (v := 2*a) (t := a) qp
      (show 2*b+1 < q by omega) (show b+1 < q by omega)
    rw [lucas.dvd_iff (dvd_refl q), qp.dvd_mul, or_iff_right]
    exact short_choose qp (by omega) (by omega)

/-- The residue classes and the single upper bound on the ordinary prime
guarantee a proper factor. This includes the inert prime three. -/
theorem gcd_entry {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (pc : p % 4 = 1) (qc : q % 4 = 3) (size : p ≤ 2*q) :
    (entry (p*q)).gcd (p*q) = p := by
  obtain ⟨hit,other⟩ := divisors pp qp pc qc
  have miss : ¬q ∣ entry (p*q) := fun h =>
    short_choose qp (by omega) (by omega) (other.mp h)
  rw [Nat.gcd_comm]
  simpa only [Nat.mul_comm q p] using
    Nat.gcd_mul_of_coprime_of_dvd (qp.coprime_iff_not_dvd.mpr miss) hit

/-- Immediately past the symmetric middle coefficient of the odd cubic
power, there is just one signed binomial term. -/
theorem adjacent_characteristic_zero (a : ℕ) :
    (((X : ℤ[X])^3-X)^(2*a+1)).coeff (4*a+3) =
      (-1 : ℤ)^a * (2*a+1).choose (a+1) := by
  have factor : ((X : ℤ[X])^3-X) = X * (expand ℤ 2) (X + C (-1)) := by
    simp [map_add, expand_X]; ring
  rw [factor, mul_pow, ← map_pow,
    show 4*a+3=2*(a+1)+(2*a+1) by omega, coeff_X_pow_mul,
    coeff_expand_mul' (by decide : 0 < 2), coeff_X_add_C_pow]
  rw [show 2*a+1-(a+1)=a by omega]

/-- Over the integers, the actual derivative at zero of the translation
polynomial has the known factor `n`. Removing it gives the signed entry
before taking any residue. -/
theorem derivative_at_zero {n : ℕ} (residue : n % 4 = 3) :
    (derivative (hasseDeriv (n-1) (((X : ℤ[X])^3-X)^((n-1)/2)))).eval 0 =
      (n : ℤ) * ((-1 : ℤ)^(n/4) * (entry n : ℤ)) := by
  let a := n/4
  have ne : n = 4*a+3 := by dsimp [a]; omega
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, hasseDeriv_coeff]
  rw [show 0+1+(n-1)=n by omega, ← Nat.choose_symm (show n-1≤n by omega),
    show n-(n-1)=1 by omega, Nat.choose_one_right,
    show (n-1)/2=2*a+1 by omega, ne, adjacent_characteristic_zero]
  simp only [entry]
  rw [show (4*a+3)/4=a by omega, show (4*a+3-1)/2=2*a+1 by omega,
    show (4*a+3+1)/4=a+1 by omega]
  simp

/-- The gcd may be taken directly on the derivative after exact division by
the public product. -/
theorem gcd_normalized_derivative {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (pc : p % 4 = 1) (qc : q % 4 = 3) (size : p ≤ 2*q) :
    let n := p*q
    Int.gcd ((derivative (hasseDeriv (n-1) (((X : ℤ[X])^3-X)^((n-1)/2)))).eval 0 /
      (n : ℤ)) (n : ℤ) = p := by
  dsimp only
  have residue : (p*q) % 4 = 3 := by rw [Nat.mul_mod, pc, qc]
  have nz : ((p*q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero pp.ne_zero qp.ne_zero
  rw [derivative_at_zero residue, Int.mul_ediv_cancel_left _ nz]
  simpa [Int.gcd, Int.natAbs_mul, Int.natAbs_pow] using gcd_entry pp qp pc qc size

example : (entry 15).gcd 15 = 5 := by decide +kernel

/-- Outside the size hypothesis both primes can divide the entry. -/
example : (entry 87).gcd 87 = 87 := by decide +kernel

end PrimeFactors.HasseBinomialDerivative
