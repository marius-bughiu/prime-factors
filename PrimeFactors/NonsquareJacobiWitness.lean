import PrimeFactors.AffineNonsquareSign

/-! A positive nonsquare represents a nonprincipal quadratic character in the
denominator of the Jacobi symbol, even after excluding any prescribed finite
set of primes. The witness is obtained from the odd part by reciprocity and
the Chinese remainder theorem. -/

namespace PrimeFactors.NonsquareJacobiWitness

private theorem prescribe {u : ℕ} (hu : Odd u) (k r y : ℕ) (hr : r = 1 ∨ r = 5) :
    ∃ a : ℕ, Odd a ∧ jacobiSym ((2 ^ k * u : ℕ) : ℤ) a =
      (if r = 1 then (1 : ℤ) else -1) ^ k * jacobiSym (y : ℤ) u := by
  have cop : Nat.Coprime 8 u := by simpa using hu.coprime_two_left.pow_left 3
  let a := Nat.chineseRemainder cop r y
  have mod8 : a.val % 8 = r % 8 := a.property.1
  have odd : Odd a.val := Nat.odd_iff.mpr (by rcases hr with rfl | rfl <;> omega)
  have four : a.val % 4 = 1 := by rcases hr with rfl | rfl <;> omega
  have two : jacobiSym 2 a.val = if r = 1 then (1 : ℤ) else -1 := by
    rw [jacobiSym.at_two odd, ZMod.χ₈_nat_eq_if_mod_eight]
    have om := Nat.odd_iff.mp odd
    rcases hr with rfl | rfl <;> norm_num at mod8 ⊢ <;> simp [om, mod8]
  have odd_part : jacobiSym (u : ℤ) a.val = jacobiSym (y : ℤ) u := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hu four]
    exact jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr a.property.2)
  refine ⟨a.val, odd, ?_⟩
  push_cast
  rw [jacobiSym.mul_left, jacobiSym.pow_left, two, odd_part]

/-- Every positive nonsquare numerator has negative Jacobi symbol at an odd denominator. -/
theorem exists_odd {d : ℕ} (hd : 0 < d) (ns : ¬ IsSquare d) :
    ∃ a : ℕ, Odd a ∧ jacobiSym (d : ℤ) a = -1 := by
  obtain ⟨k, u, odd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hd.ne'
  by_cases square : IsSquare u
  · have ko : Odd k := by
      by_contra even
      exact ns ((Nat.not_odd_iff_even.mp even).isSquare_pow 2 |>.mul square)
    obtain ⟨a, ha, sign⟩ := prescribe odd k 5 1 (Or.inr rfl)
    exact ⟨a, ha, by simpa [jacobiSym.one_left, ko.neg_one_pow] using sign⟩
  · obtain ⟨y, hy⟩ := AffineNonsquareSign.nonprincipal odd square
    obtain ⟨a, ha, sign⟩ := prescribe odd k 1 y (Or.inl rfl)
    exact ⟨a, ha, by simpa [hy] using sign⟩

/-- A witness can avoid every prime dividing a prescribed positive modulus. -/
theorem exists_coprime {d m : ℕ} (hd : 0 < d) (ns : ¬ IsSquare d) (hm : 0 < m) :
    ∃ a : ℕ, Odd a ∧ m.Coprime a ∧ jacobiSym (d : ℤ) a = -1 := by
  have nonsquare : ¬ IsSquare (m^2 * d) := by
    intro h
    obtain ⟨x, hx⟩ := h.exists_sq
    have hmx : m ∣ x := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp ⟨d, hx.symm⟩
    obtain ⟨q, rfl⟩ := hmx
    rw [mul_pow] at hx
    exact ns ((isSquare_iff_exists_sq _).mpr ⟨q, Nat.eq_of_mul_eq_mul_left (by positivity) hx⟩)
  obtain ⟨a, odd, sign⟩ := exists_odd (mul_pos (pow_pos hm _) hd) nonsquare
  have cop : (m^2*d).Coprime a := by
    by_contra h
    have z := jacobiSym.eq_zero_iff.mpr ⟨odd.pos.ne',
      (by simpa only [Int.gcd_natCast_natCast] using h : ((m^2*d : ℕ) : ℤ).gcd a ≠ 1)⟩
    omega
  have mask : m.Coprime a := cop.coprime_dvd_left
    ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_right _ _))
  have sqsign := jacobiSym.sq_one' (by simpa only [Int.gcd_natCast_natCast] using mask :
    (m : ℤ).gcd a = 1)
  push_cast at sign
  rw [jacobiSym.mul_left, sqsign, one_mul] at sign
  exact ⟨a, odd, mask, sign⟩

/-- The witness is a unit for the modulus used by the masked denominator character. -/
theorem exists_masked {d : ℕ} (hd : 0 < d) (ns : ¬ IsSquare d) :
    ∃ a : ℕ, 0 < a ∧ (120*d).Coprime a ∧ jacobiSym (d : ℤ) a = -1 := by
  obtain ⟨a, odd, cop, sign⟩ := exists_coprime hd ns (show 0 < 120*d by positivity)
  exact ⟨a, odd.pos, cop, sign⟩

end PrimeFactors.NonsquareJacobiWitness
