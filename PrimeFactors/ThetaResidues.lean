import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace PrimeFactors

/-- The coefficient of the Lambert series restricted to the positive character class. -/
noncomputable def projectedDivisorSum (η : ℕ → ℤ) (N : ℕ) : ℕ :=
  ∑ d ∈ N.divisors.filter (fun d => η d = 1), d

private theorem mem_semiprime_divisors {p q d : ℕ} (hp : p.Prime) (hq : q.Prime) :
    d ∈ (p * q).divisors ↔ d = 1 ∨ d = p ∨ d = q ∨ d = p * q := by
  rw [Nat.divisors_mul, hp.divisors, hq.divisors, Finset.mem_mul]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  · rintro (h | h | h | h) <;> rw [h]
    · exact ⟨1, Or.inl rfl, 1, Or.inl rfl, rfl⟩
    · exact ⟨p, Or.inr rfl, 1, Or.inl rfl, mul_one _⟩
    · exact ⟨1, Or.inl rfl, q, Or.inr rfl, one_mul _⟩
    · exact ⟨p, Or.inr rfl, q, Or.inr rfl, rfl⟩

theorem projectedDivisorSum_oriented {η : ℕ → ℤ} {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (h1 : η 1 = 1) (hpos : η p = 1) (hneg : η q = -1)
    (hN : η (p * q) = -1) : projectedDivisorSum η (p * q) = 1 + p := by
  have hf : (p * q).divisors.filter (fun d => η d = 1) = {1, p} := by
    ext d
    simp only [Finset.mem_filter, mem_semiprime_divisors hp hq, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hd, h⟩
      rcases hd with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
      · omega
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, h1⟩
      · exact ⟨Or.inr (Or.inl rfl), hpos⟩
  simp [projectedDivisorSum, hf, Ne.symm hp.ne_one]

/-- A public negative character value at the product guarantees a prime in the readout. -/
theorem projectedDivisorSum_factor {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (η : ℕ →* ℤ) (hN : η (p * q) = -1) :
    (projectedDivisorSum η (p * q) = 1 + p ∧ η p = 1) ∨
    (projectedDivisorSum η (p * q) = 1 + q ∧ η q = 1) := by
  have h : η p * η q = -1 := (map_mul η p q).symm.trans hN
  rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨projectedDivisorSum_oriented hp hq η.map_one ha hb hN, ha⟩
  · rw [mul_comm p q] at hN ⊢
    exact Or.inr ⟨projectedDivisorSum_oriented hq hp η.map_one hb ha hN, hb⟩

/-- The input-only Legendre-symbol test gives the factor identity for the chosen prime level. -/
theorem projectedLegendre_factor {p q ℓ : ℕ} [Fact ℓ.Prime] (hp : p.Prime) (hq : q.Prime)
    (hN : legendreSym ℓ (p * q : ℕ) = -1) :
    let η := fun d : ℕ => legendreSym ℓ d
    (projectedDivisorSum η (p * q) = 1 + p ∧ η p = 1) ∨
    (projectedDivisorSum η (p * q) = 1 + q ∧ η q = 1) := by
  exact projectedDivisorSum_factor hp hq
    ((legendreSym.hom ℓ).toMonoidHom.comp (Nat.castRingHom ℤ).toMonoidHom) hN

/-- Two positive odd candidate divisors give the same compressed word exactly when their
residues agree at one more bit of precision. -/
theorem projectedWord_iff {p r m : ℕ} (hp : Odd p) (hr : Odd r) :
    (1 + p) / 2 ≡ (1 + r) / 2 [MOD m] ↔ p ≡ r [MOD 2 * m] := by
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hr
  rw [show (1 + (2 * a + 1)) / 2 = a + 1 by omega,
      show (1 + (2 * b + 1)) / 2 = b + 1 by omega]
  constructor
  · intro h
    exact ((h.add_right_cancel' 1).mul_left' 2).add_right 1
  · intro h
    exact ((h.add_right_cancel' 1).mul_left_cancel' (by decide : 2 ≠ 0)).add_right 1

end PrimeFactors
