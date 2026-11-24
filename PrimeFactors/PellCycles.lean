import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- A residue-tree leaf reveals the other entries' product modulo its own entry. -/
theorem pellCycles_leaf {v : ℕ} (hv : 0 < v) (rest : ℕ) :
    ((v * rest) % (v * v)) / v = rest % v := by
  rw [Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ hv]

/-- The private part of the absolute value of a row has to be a square in any
integer square dependency containing that row. -/
theorem pellCycles_private {u rest : ℕ} (cop : u.Coprime rest)
    (whole : IsSquare (u * rest)) : IsSquare u := by
  obtain ⟨r, h⟩ := (isSquare_iff_exists_sq _).mp whole
  apply (isSquare_iff_exists_sq _).mpr
  apply exists_eq_pow_of_mul_eq_pow _ h
  change IsUnit (Nat.gcd u rest)
  simp [cop.gcd_eq_one]

/-- The obstruction remains valid after appending arbitrary factors supported
on a specified external base E, with no bound on their exponents. -/
theorem pellCycles_external_private {u rest E M k : ℕ} (nonsquare : ¬IsSquare u)
    (cop : u.Coprime rest) (external : u.Coprime E) (supported : M ∣ E^k) :
    ¬IsSquare ((u * rest) * M) := by
  rw [Nat.mul_assoc]
  exact fun h => nonsquare (pellCycles_private
    (cop.mul_right ((external.pow_right k).of_dvd_right supported)) h)

/-- An odd exponent of a nonsquare base stays nonsquare, even if that base
is composite and its prime divisors are unknown. -/
theorem pellCycles_base_power (b e : ℕ) (hb : 0 < b) :
    IsSquare (b ^ e) ↔ IsSquare b ∨ Even e := by
  constructor
  · intro h
    by_cases he : Even e
    · exact Or.inr he
    left
    obtain ⟨k,rfl⟩ := Nat.not_even_iff_odd.mp he
    obtain ⟨r,hr⟩ := (isSquare_iff_exists_sq _).mp h
    have eq : (b ^ k)^2 * b = r^2 := by
      rw [← hr]
      ring
    have dv : (b ^ k)^2 ∣ r^2 := ⟨_, eq.symm⟩
    obtain ⟨s, hs⟩ := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp dv
    apply (isSquare_iff_exists_sq _).mpr
    refine ⟨s, Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos hb k) 2) ?_⟩
    rw [eq, hs, mul_pow]
  · rintro (h | h)
    · exact h.pow e
    · exact h.isSquare_pow b

/-- On a coprime basis, each nonsquare base contributes exactly one parity
constraint. The entries of the basis need no prime factorizations. -/
theorem pellCycles_base_criterion {ι : Type*} {s : Finset ι} (b e : ι → ℕ)
    (pos : ∀ i ∈ s, 0 < b i)
    (cop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (b i).Coprime (b j)) :
    IsSquare (∏ i ∈ s, (b i)^(e i)) ↔ ∀ i ∈ s, IsSquare (b i) ∨ Even (e i) := by
  classical
  constructor
  · intro h i hi
    apply (pellCycles_base_power _ _ (pos i hi)).mp
    have hc : ((b i)^(e i)).Coprime (∏ j ∈ s.erase i, (b j)^(e j)) := by
      apply Nat.Coprime.prod_right
      intro j hj
      have mem := Finset.mem_erase.mp hj
      exact (((cop i hi j mem.2 mem.1.symm).pow_left _).pow_right _)
    apply pellCycles_private hc
    simpa [Finset.mul_prod_erase s (fun i => b i ^ e i) hi] using h
  · intro h
    apply Finset.prod_induction _ (fun x : ℕ => IsSquare x) (fun _ _ => IsSquare.mul) IsSquare.one
    exact fun i hi => (pellCycles_base_power _ _ (pos i hi)).mpr (h i hi)

/-- A symmetric difference of two trivial square relations stays trivial.
The common indices contribute the same unit to both products up to the
sign of their norms. -/
theorem pellCycles_trivial_xor {A : Type*} [CommRing A] {x y z a b d c : A}
    (unit : IsUnit c) (left : x = a ∨ x = -a) (right : y = b ∨ y = -b)
    (numerators : x*y = z*c) (roots : a*b = d*c ∨ a*b = -(d*c)) :
    z = d ∨ z = -d := by
  have same : x*y = a*b ∨ x*y = -(a*b) := by
    rcases left with rfl | rfl <;> rcases right with rfl | rfl <;> simp
  rw [numerators] at same
  rcases roots with h | h <;> rw [h] at same <;>
    simpa only [neg_neg, ← neg_mul, unit.mul_left_inj, or_comm] using same

/-- Four early convergents of √21490481 return a factor before a center. -/
theorem pellCycles_early_example :
    64901^2 % 21490481 = 5525 ∧ 3050345^2 % 21490481 = 3341 ∧
    13699541^2 % 21490481 = 4112 ∧ 3003701^2 % 21490481 = 2057 ∧
    5525*3341*4112*2057 = 12495340^2 ∧
    (64901*3050345*13699541*3003701) % 21490481 = 5709105 ∧
    Nat.gcd (12495340-5709105) 21490481 = 4421 ∧ 4421*4861 = 21490481 := by decide

end PrimeFactors
