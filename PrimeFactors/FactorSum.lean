import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- A residue is an admissible sum if some pair of residues has that sum and the given product. -/
def AdmissibleSum {ℓ : ℕ} (n s : ZMod ℓ) : Prop :=
  ∃ x y : ZMod ℓ, x * y = n ∧ x + y = s

/-- Reduction modulo any modulus preserves every actual factor-pair sum. -/
theorem admissibleSum_of_factor_pair (ℓ : ℕ) {n p q : ℕ} (hpq : p * q = n) :
    AdmissibleSum (n : ZMod ℓ) ((p + q : ℕ) : ZMod ℓ) := by
  subst n
  exact ⟨p, q, (Nat.cast_mul ..).symm, (Nat.cast_add ..).symm⟩

/-- For an odd prime modulus, the discriminant gives an exact test of local compatibility. -/
theorem admissibleSum_iff_isSquare {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hodd : ℓ ≠ 2)
    (n s : ZMod ℓ) : AdmissibleSum n s ↔ IsSquare (s ^ 2 - 4 * n) := by
  constructor
  · rintro ⟨x, y, rfl, rfl⟩
    exact ⟨x - y, by ring⟩
  · rintro ⟨d, hd⟩
    have htwo : (2 : ZMod ℓ) ≠ 0 := by
      intro hz
      have hdiv := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 ℓ).mp hz
      exact hodd ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).mp hdiv)
    refine ⟨(s + d) / 2, (s - d) / 2, ?_, ?_⟩
    · rw [div_mul_div_comm, div_eq_iff (mul_ne_zero htwo htwo)]
      linear_combination hd
    · rw [← add_div, div_eq_iff htwo]
      ring

/-- A product test alone leaves every nonzero individual residue possible. -/
theorem exists_partner_residue {ℓ : ℕ} [Fact ℓ.Prime] {n x : ZMod ℓ} (hn : n ≠ 0)
    (hx : x ≠ 0) : ∃ y : ZMod ℓ, y ≠ 0 ∧ x * y = n := by
  refine ⟨n / x, div_ne_zero hn hx, ?_⟩
  field_simp

/-- Over the naturals, a square discriminant and matching parity reconstruct an ordered pair.
Writing the discriminant without subtraction also handles proposed sums below the square root. -/
theorem exists_ordered_pair_iff_square_gap (n s : ℕ) :
    (∃ p q : ℕ, p ≤ q ∧ p * q = n ∧ p + q = s) ↔
    ∃ d : ℕ, s ^ 2 = 4 * n + d ^ 2 ∧ d ≤ s ∧ Even (s - d) := by
  constructor
  · rintro ⟨p, q, hpq, rfl, rfl⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
    exact ⟨d, by ring, by omega, p, by omega⟩
  · rintro ⟨d, hd, hle, p, heven⟩
    have hs : s = p + (p + d) := by omega
    refine ⟨p, p + d, by omega, ?_, hs.symm⟩
    rw [hs] at hd
    nlinarith only [hd]

/-- Two ordered natural factor pairs with the same product and the same sum coincide. -/
theorem ordered_pair_unique_of_product_sum {p q x y : ℕ} (hpq : p ≤ q) (hxy : x ≤ y)
    (hprod : p * q = x * y) (hsum : p + q = x + y) : p = x ∧ q = y := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hpq
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hxy
  have hsquared := congrArg (fun v : ℕ => v ^ 2) hsum
  dsimp only at hsquared
  have hab : a * a = b * b := by nlinarith only [hsquared, hprod]
  have : a = b := (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp hab
  omega

private theorem eq_pair_of_prime_dvd_left {p q x y : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hy : 1 < y) (hm : x * y = p * q) (hd : p ∣ x) :
    x = p ∧ y = q := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k * y = q := Nat.eq_of_mul_eq_mul_left hp.pos (by simpa [Nat.mul_assoc] using hm)
  have hyd : y ∣ q := hk ▸ dvd_mul_left y k
  have hyq := ((Nat.dvd_prime hq).mp hyd).resolve_left (by omega)
  subst y
  have hk1 : k = 1 := Nat.eq_of_mul_eq_mul_right hq.pos (by simpa using hk)
  simp [hk1]

/-- For a semiprime, imposing nontriviality leaves a unique ordered pair, hence a unique sum. -/
theorem ordered_semiprime_pair_unique {p q x y : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≤ q) (hxy : x ≤ y) (hx : 1 < x) (hm : x * y = p * q) :
    x = p ∧ y = q := by
  have hd : p ∣ x * y := hm ▸ dvd_mul_right p q
  rcases hp.dvd_mul.mp hd with h | h
  · exact eq_pair_of_prime_dvd_left hp hq (by omega) hm h
  · have h' := eq_pair_of_prime_dvd_left hp hq hx (by simpa [Nat.mul_comm y x] using hm) h
    omega

end PrimeFactors
