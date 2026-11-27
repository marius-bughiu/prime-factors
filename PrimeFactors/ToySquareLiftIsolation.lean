import PrimeFactors.PrimePower
import PrimeFactors.ToySumIsolation

/-! A numeric cutoff includes the odd prime rows up to the cutoff and, from
9 onward, one conditional lift at 3. All population checks use the public
factor-width window from `ToySumIsolation`. -/

namespace PrimeFactors.ToySquareLiftIsolation

open ToySumIsolation

set_option maxRecDepth 8192

/-- After a prime test passes, only zero discriminants require a new
divisibility test at the square of that prime. -/
theorem admissible_prime_square {ℓ : ℕ} [Fact ℓ.Prime] (odd : ℓ ≠ 2)
    (n s : ℤ) :
    AdmissibleSum (n : ZMod (ℓ^2)) (s : ZMod (ℓ^2)) ↔
      AdmissibleSum (n : ZMod ℓ) (s : ZMod ℓ) ∧
        ((ℓ : ℤ) ∣ s^2-4*n → (ℓ : ℤ)^2 ∣ s^2-4*n) := by
  by_cases h : (ℓ : ℤ) ∣ s^2-4*n
  · have zero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    have base : AdmissibleSum (n : ZMod ℓ) (s : ZMod ℓ) := by
      apply (admissibleSum_iff_isSquare odd _ _).mpr
      push_cast at zero
      rw [zero]
      exact ⟨0, by simp⟩
    simp [admissibleSum_prime_sq_iff_of_singular odd n s h, base, h]
  · have regular := mt (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
    simpa [h] using admissibleSum_primePow_iff_of_regular odd n s regular 1

/-- Extra test evaluated alongside the ordinary mod-3 test. -/
def liftAtThree (n s : ℕ) : Bool :=
  let d := s*s-4*n
  d%3 != 0 || d%9 == 0

/-- On the public window, the original mod-3 row and this one extra
condition are exactly the mod-9 local sum predicate. -/
theorem mod_nine_iff {n A s : ℕ} (inside : s ∈ menu n A) :
    AdmissibleSum (n : ZMod 9) (s : ZMod 9) ↔
      accepts n (3,3) s = true ∧ liftAtThree n s = true := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have a := admissible_prime_square (ℓ := 3) (by decide) (n : ℤ) (s : ℤ)
  have b := accepts_iff inside (r := (3,3)) (by decide)
  have above : 4*n ≤ s*s := by
    simpa only [pow_two] using ceilSqrt_le_iff.mp (mem_menu.mp inside).1
  have discr : (s : ℤ)^2-4*n = ((s*s-4*n : ℕ) : ℤ) := by
    simp [Nat.cast_sub above, pow_two]
  rw [discr] at a
  change AdmissibleSum (n : ZMod 9) (s : ZMod 9) ↔
    AdmissibleSum (n : ZMod 3) (s : ZMod 3) ∧
      ((3 : ℤ) ∣ ((s*s-4*n : ℕ) : ℤ) → (9 : ℤ) ∣ ((s*s-4*n : ℕ) : ℤ)) at a
  rw [a, b]
  apply and_congr_right
  intro _
  change (((3 : ℕ) : ℤ) ∣ _ → ((9 : ℕ) : ℤ) ∣ _) ↔ _
  simp only [Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero, liftAtThree,
    Bool.or_eq_true, bne_iff_ne, beq_iff_eq]
  tauto

/-- Each modulus is bounded by `cap`. Nine contributes only its extra test. -/
noncomputable def survivors (n A cap : ℕ) : List ℕ :=
  let schedule := rows.takeWhile (fun r => r.1 ≤ cap)
  (menu n A).filter fun s =>
    (cap < 9 || liftAtThree n s) && schedule.all (fun r => accepts n r s)

/-- At cutoff 23 the tested modular predicates are exactly those for 9 and
for the eight odd primes from 3 through 23. -/
theorem mem_at_23 {n A s : ℕ} :
    s ∈ survivors n A 23 ↔ s ∈ menu n A ∧
      AdmissibleSum (n : ZMod 9) (s : ZMod 9) ∧
      ∀ r ∈ rows.takeWhile (fun r => r.1 ≤ 23),
        AdmissibleSum (n : ZMod r.1) (s : ZMod r.1) := by
  have three : (3,3) ∈ rows.takeWhile (fun r => r.1 ≤ 23) := by decide
  simp only [survivors, List.mem_filter, Nat.reduceLT, decide_false, Bool.false_or,
    Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨inside, lift, pass⟩
    exact ⟨inside, (mod_nine_iff inside).mpr ⟨pass _ three, lift⟩,
      fun r hr => (accepts_iff inside (List.takeWhile_subset _ hr)).mp (pass r hr)⟩
  · rintro ⟨inside, nine, pass⟩
    exact ⟨inside, ((mod_nine_iff inside).mp nine).2,
      fun r hr => (accepts_iff inside (List.takeWhile_subset _ hr)).mpr (pass r hr)⟩

/-- The known factors are read when checking the result for a population row. -/
noncomputable def exceptions (A cap : ℕ) : List (ℕ × ℕ) :=
  (pairs A).filter fun (p,q) => survivors (p*q) A cap != [p+q]

/-- In both complete factor-width populations 23 suffices. One eight-bit
pair and four nine-bit pairs still admit false sums at the previous prime. -/
theorem eight_bits : exceptions 128 23 = [] ∧ exceptions 128 19 = [(193,197)] := by
  simp only [exceptions, pairs, catalog_eight, List.filter_flatMap]
  decide +kernel

theorem nine_bits : exceptions 256 23 = [] ∧ exceptions 256 19 =
    [(317,421),(337,503),(353,389),(367,467)] := by
  simp only [exceptions, pairs, catalog_nine, List.filter_flatMap]
  decide +kernel

/-- The cutoff-23 result as a statement about any eligible input pair. -/
theorem nine_bit_singleton {p q : ℕ} (lo : 256 ≤ p) (lt : p < q) (hi : q < 512)
    (hp : p.Prime) (hq : q.Prime) : survivors (p*q) 256 23 = [p+q] := by
  by_contra wrong
  have member : (p,q) ∈ pairs 256 := mem_pairs.mpr ⟨lo, by omega, hp, lt, hi, hq⟩
  have bad : (p,q) ∈ exceptions 256 23 :=
    List.mem_filter.mpr ⟨member, by simpa using wrong⟩
  simp [nine_bits.1] at bad

/-- One of the four witnesses at 19; no added numeric modulus from 20 through
22 is on the schedule. The former hard sum 748 is already rejected modulo 9. -/
theorem sharp_and_singular_examples :
    survivors 137317 256 22 = [742,778] ∧ survivors 137317 256 23 = [742] ∧
      liftAtThree 136831 748 = false ∧ survivors 136831 256 9 = [752,760] ∧
      survivors 136831 256 11 = [760] := by
  decide +kernel

/-- The false sum 778 survives even if every odd prime through 19 is lifted
to its square. Its normalized discriminant is 14004 = 36 · 389. -/
theorem false_sum_passes_squares :
    ∀ r ∈ rows.takeWhile (fun r => r.1 ≤ 19),
      AdmissibleSum (137317 : ZMod (r.1^2)) (778 : ZMod (r.1^2)) := by
  have digits : ∀ r ∈ rows.takeWhile (fun r => r.1 ≤ 19),
      r.1.Prime ∧ r.1 ≠ 2 ∧ accepts 137317 r 778 = true ∧
        ((r.1 : ℤ) ∣ 778^2-4*137317 → (r.1 : ℤ)^2 ∣ 778^2-4*137317) := by
    decide +kernel
  have inside : 778 ∈ menu 137317 256 := by decide +kernel
  intro r hr
  obtain ⟨prime,odd,pass,digit⟩ := digits r hr
  letI : Fact r.1.Prime := ⟨prime⟩
  have lifted := admissible_prime_square odd 137317 778
  simp only [Int.cast_ofNat] at lifted
  apply lifted.mpr
  refine ⟨?_, digit⟩
  simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
    (accepts_iff inside (List.takeWhile_subset _ hr)).mp pass

end PrimeFactors.ToySquareLiftIsolation
