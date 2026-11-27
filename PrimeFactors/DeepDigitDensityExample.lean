import PrimeFactors.PrimePowerWheelDensity

/-! For the toy semiprime 94579, compare depths two and eight at all odd
primes through 23. Counts on the common period come from the local square
recurrence and CRT. -/
namespace PrimeFactors.DeepDigitDensityExample

open PrimePowerDensityRatio (density)
open PrimePowerWheelDensity (density_product)

noncomputable def seeds : Finset ℕ := {3,5,7,11,13,17,19,23}
noncomputable def period (e : ℕ) := ∏ p ∈ seeds, p^e

theorem factorization : ExactFactorization 94579 [271,349] := by
  unfold ExactFactorization
  decide +kernel

/-- Each test prime sees a nonzero square product residue. -/
theorem square_units : ∀ p ∈ seeds, p.Prime ∧ p ≠ 2 ∧ ¬p ∣ 94579 ∧
    ∃ x : Fin p, x.val*x.val%p = 94579%p := by
  intro p hp
  simp only [seeds, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h|h|h|h|h|h|h|h <;> subst p <;> decide +kernel

/-- The known square branch of the local recurrence suffices at every depth. -/
theorem local_count {p : ℕ} (member : p ∈ seeds) (k : ℕ) :
    LocalSumMenu.count 94579 (p^(k+1)) = primePowerSumCount p true (k+1) := by
  classical
  obtain ⟨prime, odd, unit, x, hx⟩ := square_units p member
  letI : Fact p.Prime := ⟨prime⟩
  have square : IsSquare (94579 : ZMod p) := by
    refine ⟨x.val, ?_⟩
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (ZMod.natCast_eq_natCast_iff' _ _ p).mpr hx.symm
  have nz : firstPrimeDigit p k ((94579:ℕ) : ZMod (p^(k+1))) ≠ 0 := by
    rw [map_natCast]
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp.mt unit
  have digitSquare : IsSquare (firstPrimeDigit p k ((94579:ℕ) : ZMod (p^(k+1)))) := by
    rw [map_natCast]
    exact square
  apply (card_primePower_admissibleSum odd k _ nz).trans
  apply congrArg (fun flag => primePowerSumCount p flag (k+1))
  exact @decide_eq_true _ (Classical.propDecidable _) digitSquare

private noncomputable def localProduct (e : ℕ) : ℚ :=
  ∏ p ∈ seeds, (primePowerSumCount p true e : ℚ) / (p^e : ℕ)

private theorem count_certificate (k c : ℕ)
    (number : localProduct (k+1) * (period (k+1) : ℚ) = c) :
    LocalSumMenu.count 94579 (period (k+1)) = c := by
  have h : density 94579 (period (k+1)) = localProduct (k+1) := by
    unfold period localProduct
    rw [density_product 94579 seeds (fun _ => k+1) (fun p hp => (square_units p hp).1)]
    exact Finset.prod_congr rfl fun p hp => by rw [density, local_count hp]
  have pos : 0 < period (k+1) := Finset.prod_pos fun p hp =>
    pow_pos (square_units p hp).1.pos _
  have hz : (period (k+1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr pos.ne'
  rw [←h, density, div_mul_cancel₀ _ hz] at number
  exact_mod_cast number

/-- Distinct classes in the two native periods. -/
theorem native_counts :
    LocalSumMenu.count 94579 (period 2) = 2984521616384 ∧
    LocalSumMenu.count 94579 (period 8) =
      1576562722276229904104650898372515313409599700207211928000000 :=
  ⟨count_certificate 1 _ (by decide +kernel), count_certificate 7 _ (by decide +kernel)⟩

/-- On the eighth-power period the second-power classes recur this many
times in total. Both populations below are measured over the same interval. -/
theorem common_period_counts :
    period 2 ∣ period 8 ∧
    (period 8 / period 2)*LocalSumMenu.count 94579 (period 2) =
      5749219607619793742597131367543523867563684614264966704000000 ∧
    LocalSumMenu.count 94579 (period 8) =
      1576562722276229904104650898372515313409599700207211928000000 := by
  rw [native_counts.1, native_counts.2]
  decide +kernel

/-- Full-period density improvement for this input lies strictly between
3.6466 and 3.6467. -/
theorem density_ratio :
    (36466 : ℚ)/10000 < density 94579 (period 2) / density 94579 (period 8) ∧
    density 94579 (period 2) / density 94579 (period 8) < (36467 : ℚ)/10000 := by
  simp only [density, native_counts.1, native_counts.2]
  decide +kernel

end PrimeFactors.DeepDigitDensityExample
