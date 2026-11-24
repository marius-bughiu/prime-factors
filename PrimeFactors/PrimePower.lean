import PrimeFactors.FactorSum

namespace PrimeFactors

/-- The discriminant detects admissibility over any modulus in which two is invertible. -/
theorem admissibleSum_iff_isSquare_of_two_unit {m : ℕ} (two : IsUnit (2 : ZMod m))
    (n s : ZMod m) : AdmissibleSum n s ↔ IsSquare (s ^ 2 - 4 * n) := by
  constructor
  · rintro ⟨x, y, rfl, rfl⟩
    exact ⟨x - y, by ring⟩
  · rintro ⟨d, hd⟩
    obtain ⟨u, hu⟩ := two
    let h := (↑(u⁻¹) : ZMod m)
    have half : 2 * h = 1 := by rw [← hu]; exact u.mul_inv
    refine ⟨(s + d) * h, (s - d) * h, ?_, ?_⟩
    · calc
        _ = (s ^ 2 - d * d) * h ^ 2 := by ring
        _ = (4 * n) * h ^ 2 := by rw [← hd]; ring
        _ = n * (2 * h) ^ 2 := by ring
        _ = n := by rw [half]; simp
    · calc
        _ = s * (2 * h) := by ring
        _ = s := by rw [half, mul_one]

private theorem square_iff_integer_root (m : ℕ) (D : ℤ) :
    IsSquare (D : ZMod m) ↔ ∃ x : ℤ, (m : ℤ) ∣ D - x ^ 2 := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := ZMod.intCast_surjective z
    refine ⟨x, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_⟩
    push_cast
    rw [hz, pow_two, sub_self]
  · rintro ⟨x, hx⟩
    refine ⟨(x : ZMod m), ?_⟩
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hx
    push_cast at h
    simpa [pow_two] using sub_eq_zero.mp h

private theorem lift_unit_square_root {ℓ : ℕ} [Fact ℓ.Prime] (hodd : ℓ ≠ 2)
    {D x : ℤ} (hx : (x : ZMod ℓ) ≠ 0) (base : (ℓ : ℤ) ∣ D - x ^ 2) (k : ℕ) :
    ∃ y : ℤ, (y : ZMod ℓ) = (x : ZMod ℓ) ∧
      (ℓ : ℤ) ^ (k + 1) ∣ D - y ^ 2 := by
  induction k with
  | zero => exact ⟨x, rfl, by simpa using base⟩
  | succ k ih =>
    obtain ⟨y, hy, u, hu⟩ := ih
    have htwo : (2 : ZMod ℓ) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    have slope : (2 : ZMod ℓ) * y ≠ 0 := mul_ne_zero htwo (hy ▸ hx)
    obtain ⟨t, ht⟩ := ZMod.intCast_surjective ((u : ZMod ℓ) / (2 * (y : ZMod ℓ)))
    have digit : (ℓ : ℤ) ∣ u - 2 * y * t := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [ht, mul_div_cancel₀ _ slope, sub_self]
    obtain ⟨v, hv⟩ := digit
    refine ⟨y + (ℓ : ℤ) ^ (k + 1) * t, ?_, v - (ℓ : ℤ) ^ k * t ^ 2, ?_⟩
    · push_cast
      simp [hy]
    · linear_combination hu + (ℓ : ℤ) ^ (k + 1) * hv

/-- A nonzero discriminant residue that is square modulo an odd prime is a
square modulo every positive power of that prime. -/
theorem isSquare_primePow_iff_of_unit {ℓ : ℕ} [Fact ℓ.Prime] (hodd : ℓ ≠ 2)
    (D : ℤ) (hD : (D : ZMod ℓ) ≠ 0) (k : ℕ) :
    IsSquare (D : ZMod (ℓ ^ (k + 1))) ↔ IsSquare (D : ZMod ℓ) := by
  rw [square_iff_integer_root, square_iff_integer_root]
  push_cast
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (dvd_pow_self _ (Nat.succ_ne_zero k)).trans hy⟩
  · rintro ⟨x, hx⟩
    have hunit : (x : ZMod ℓ) ≠ 0 := by
      intro hz
      apply hD
      have z := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hx
      simpa [hz] using z
    obtain ⟨y, _, hy⟩ := lift_unit_square_root hodd hunit hx k
    exact ⟨y, hy⟩


private theorem two_unit_odd_primePow {ℓ : ℕ} [Fact ℓ.Prime] (hodd : ℓ ≠ 2) (e : ℕ) :
    IsUnit (2 : ZMod (ℓ ^ e)) := by
  exact (ZMod.isUnit_iff_coprime 2 _).mpr
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two Fact.out).mpr hodd.symm))

/-- Once the discriminant is nonzero modulo an odd prime, higher powers of
that prime cannot reject a sum that passed at the first power. -/
theorem admissibleSum_primePow_iff_of_regular {ℓ : ℕ} [Fact ℓ.Prime] (hodd : ℓ ≠ 2)
    (n s : ℤ) (regular : ((s ^ 2 - 4 * n : ℤ) : ZMod ℓ) ≠ 0) (k : ℕ) :
    AdmissibleSum (n : ZMod (ℓ ^ (k + 1))) (s : ZMod (ℓ ^ (k + 1))) ↔
      AdmissibleSum (n : ZMod ℓ) (s : ZMod ℓ) := by
  rw [admissibleSum_iff_isSquare_of_two_unit (two_unit_odd_primePow hodd _),
    admissibleSum_iff_isSquare hodd]
  simpa using isSquare_primePow_iff_of_unit hodd (s ^ 2 - 4 * n) regular k

/-- A discriminant divisible by a prime is a square modulo its square
exactly when the prime square divides it. -/
theorem isSquare_prime_sq_iff_of_dvd {ℓ : ℕ} [Fact ℓ.Prime] (D : ℤ)
    (singular : (ℓ : ℤ) ∣ D) :
    IsSquare (D : ZMod (ℓ ^ 2)) ↔ (ℓ : ℤ) ^ 2 ∣ D := by
  rw [square_iff_integer_root]
  push_cast
  constructor
  · rintro ⟨x, hx⟩
    have hdiv : (ℓ : ℤ) ∣ D - x ^ 2 := (dvd_pow_self _ (by decide : 2 ≠ 0)).trans hx
    have hxsq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
    have zero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr singular
    have hxzero : (x : ZMod ℓ) = 0 := by simpa [zero] using hxsq
    have square_dvd := pow_dvd_pow_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hxzero) 2
    simpa using dvd_add hx square_dvd
  · intro hd
    exact ⟨0, by simpa using hd⟩

/-- For a sum of discriminant zero modulo an odd prime, the next digit
survives exactly when its new discriminant is zero modulo the prime square. -/
theorem admissibleSum_prime_sq_iff_of_singular {ℓ : ℕ} [Fact ℓ.Prime] (hodd : ℓ ≠ 2)
    (n s : ℤ) (singular : (ℓ : ℤ) ∣ s ^ 2 - 4 * n) :
    AdmissibleSum (n : ZMod (ℓ ^ 2)) (s : ZMod (ℓ ^ 2)) ↔
      (ℓ : ℤ) ^ 2 ∣ s ^ 2 - 4 * n := by
  rw [admissibleSum_iff_isSquare_of_two_unit (two_unit_odd_primePow hodd _)]
  simpa using isSquare_prime_sq_iff_of_dvd (s ^ 2 - 4 * n) singular

/-- If a sum is singular at the first power and the product is a unit there,
exactly one next base-prime digit survives. The formula computes that digit
directly from the product and the candidate, including when their discriminant is zero. -/
theorem admissibleSum_singular_digit_iff {ℓ : ℕ} [Fact ℓ.Prime] (hodd : ℓ ≠ 2)
    (n s u t : ℤ) (unitProduct : (n : ZMod ℓ) ≠ 0)
    (quotient : s ^ 2 - 4 * n = (ℓ : ℤ) * u) :
    AdmissibleSum (n : ZMod (ℓ ^ 2)) ((s + (ℓ : ℤ) * t : ℤ) : ZMod (ℓ ^ 2)) ↔
      (t : ZMod ℓ) = -(u : ZMod ℓ) / (2 * (s : ZMod ℓ)) := by
  have expansion : (s + (ℓ : ℤ) * t) ^ 2 - 4 * n =
      (ℓ : ℤ) * (u + 2 * s * t + (ℓ : ℤ) * t ^ 2) := by linear_combination quotient
  have slope : (2 : ZMod ℓ) * (s : ZMod ℓ) ≠ 0 := by
    have two : (2 : ZMod ℓ) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    apply mul_ne_zero two
    intro hs
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Dvd.intro u quotient.symm)
    have four : (4 : ZMod ℓ) ≠ 0 := by
      rw [show (4 : ZMod ℓ) = 2 * 2 by norm_num]
      exact mul_ne_zero two two
    simp [hs, four, unitProduct] at hd
  rw [admissibleSum_prime_sq_iff_of_singular hodd n _ (expansion ▸ dvd_mul_right _ _),
    expansion, pow_two, mul_dvd_mul_iff_left (Int.natCast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero),
    ← ZMod.intCast_zmod_eq_zero_iff_dvd, eq_div_iff slope]
  push_cast
  simp only [ZMod.natCast_self, zero_mul, add_zero]
  constructor <;> intro h <;> linear_combination h

/-- For a product congruent to one modulo three, one entire sum class modulo
27 survives simultaneously at every three-adic precision. -/
theorem exists_permanent_sum_class_mod_27 (n : ℤ) (hn : (n : ZMod 3) = 1) :
    ∃ r : ℤ, ∀ s : ℤ, s ≡ r [ZMOD 27] → ∀ e : ℕ,
      AdmissibleSum (n : ZMod (3 ^ e)) (s : ZMod (3 ^ e)) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have one : ((4 * n + 9 : ℤ) : ZMod 3) = 1 := by
    push_cast
    rw [hn]
    decide
  have sq : IsSquare ((4 * n + 9 : ℤ) : ZMod (3 ^ (2 + 1))) :=
    (isSquare_primePow_iff_of_unit (by decide : 3 ≠ 2) _ (by rw [one]; decide) 2).mpr
      (by rw [one]; exact ⟨1, by simp⟩)
  obtain ⟨r, hr⟩ := (square_iff_integer_root 27 (4 * n + 9)).mp sq
  refine ⟨r, fun s hs e => ?_⟩
  obtain ⟨w, hw⟩ := hr
  obtain ⟨v, hv⟩ := Int.modEq_iff_dvd.mp hs.symm
  have discr : s ^ 2 - 4 * n = 9 * (1 + 3 * (v * (s + r) - w)) := by
    linear_combination (s + r) * hv - hw
  let u := 1 + 3 * (v * (s + r) - w)
  have residue : (u : ZMod 3) = 1 := by
    dsimp [u]
    push_cast
    rw [show (3 : ZMod 3) = 0 by decide, zero_mul, add_zero]
  cases e with
  | zero =>
    rw [pow_zero]
    exact ⟨0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  | succ k =>
    have sqUnit : IsSquare (u : ZMod (3 ^ (k + 1))) :=
      (isSquare_primePow_iff_of_unit (by decide : 3 ≠ 2) u (by rw [residue]; decide) k).mpr
        (by rw [residue]; exact ⟨1, by simp⟩)
    obtain ⟨z, hz⟩ := sqUnit
    apply (admissibleSum_iff_isSquare_of_two_unit
      (two_unit_odd_primePow (by decide : 3 ≠ 2) _) _ _).mpr
    refine ⟨3 * z, ?_⟩
    have h := congrArg (fun a : ℤ => (a : ZMod (3 ^ (k + 1))))
      (show s ^ 2 - 4 * n = 9 * u from discr)
    push_cast at h
    rw [h, hz]
    ring

/-- On the eleven even sums in the balanced interval for 34387, the first
three odd primes leave 382, 388 and 392. Upgrading 3 to 9 isolates 388. -/
theorem primePower_example_34387 :
    ∀ i : Fin 11, let s := 372 + 2 * i.val
      let passes := fun m : ℕ => AdmissibleSum (34387 : ZMod m) (s : ZMod m)
      ((passes 3 ∧ passes 5 ∧ passes 7) ↔ s = 382 ∨ s = 388 ∨ s = 392) ∧
      ((passes 9 ∧ passes 5 ∧ passes 7) ↔ s = 388) := by
  unfold AdmissibleSum
  decide

end PrimeFactors
