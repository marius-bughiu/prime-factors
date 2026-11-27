import PrimeFactors.LocalSumMenu

/-! Counts of admissible factor sums for the wheel through 19. -/

namespace PrimeFactors.IntervalWheelResidues

open LocalSumMenu

/-- The factor four fixes the sum modulo four for every odd product. -/
def modulus : ℕ := 4 * 3 * 5 * 7 * 11 * 13 * 17 * 19

/-- Every odd product fixes a unique admissible sum modulo four. -/
theorem count_four {n : ℕ} (odd : ¬ 2 ∣ n) : count n 4 = 1 := by
  have parity : (n : ZMod 4).val % 2 = 1 := by
    rw [ZMod.val_natCast, Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)]
    omega
  have trace {s : ZMod 4} (ok : AdmissibleSum (n : ZMod 4) s) : s = 1 + n := by
    obtain ⟨x, y, prod, rfl⟩ := ok
    rw [← prod] at parity ⊢
    exact (show ∀ x y : ZMod 4, (x * y).val % 2 = 1 → x + y = 1 + x * y by decide) x y parity
  letI : Nonempty {s : ZMod 4 // AdmissibleSum (n : ZMod 4) s} :=
    ⟨⟨1 + n, 1, n, one_mul _, rfl⟩⟩
  letI : Subsingleton {s : ZMod 4 // AdmissibleSum (n : ZMod 4) s} :=
    ⟨fun s t => Subtype.ext ((trace s.property).trans (trace t.property).symm)⟩
  exact Nat.card_unique

private theorem count_mul {a b : ℕ} (cop : a.Coprime b) (n : ℕ) :
    count n (a * b) = count n a * count n b := card_admissibleSum_crt cop n

/-- CRT multiplies the eight local counts for every product. -/
theorem count_components (n : ℕ) :
    count n modulus = count n 4 * count n 3 * count n 5 * count n 7 *
      count n 11 * count n 13 * count n 17 * count n 19 := by
  simp (disch := decide) only [modulus, count_mul]

/-- A nonzero product at an odd prime admits at most half the classes,
rounded up, as sums. -/
theorem prime_classes {n p : ℕ} (hp : p.Prime) (odd : p ≠ 2) (nondiv : ¬p ∣ n) :
    count n p ≤ (p + 1) / 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have unit := (ZMod.natCast_zmod_eq_zero_iff_dvd n p).mp.mt nondiv
  rw [count, card_admissibleSum_eq p _ unit]
  by_cases sq : IsSquare (n : ZMod p)
  · exact (card_factorSumResidues_of_square p odd _ unit sq).le
  · rw [card_factorSumResidues_of_nonsquare p _ unit sq]
    omega

/-- At most 90,720 of the 19,399,380 sums per full period pass all local tests.
The hypothesis is checkable from the product alone. -/
theorem count_le {n : ℕ} (cop : modulus.Coprime n) : count n modulus ≤ 90720 := by
  have primeBound (p : ℕ) (hp : p.Prime) (odd : p ≠ 2) (div : p ∣ modulus) :
      count n p ≤ (p + 1) / 2 :=
    prime_classes hp odd (hp.coprime_iff_not_dvd.mp (cop.of_dvd_left div))
  have four := count_four (Nat.prime_two.coprime_iff_not_dvd.mp
    (cop.of_dvd_left (by decide : 2 ∣ modulus)))
  calc
    count n modulus = count n 4 * count n 3 * count n 5 * count n 7 *
        count n 11 * count n 13 * count n 17 * count n 19 := count_components n
    _ ≤ 1 * 2 * 3 * 4 * 6 * 7 * 9 * 10 := by
      gcongr <;> first | exact four.le | exact primeBound _ (by decide) (by decide) (by decide)
    _ = 90720 := by decide

end PrimeFactors.IntervalWheelResidues
