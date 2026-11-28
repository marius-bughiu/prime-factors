import PrimeFactors.FractionalSelectedProgression

/-! For the two prescribed congruences, the wheel gcd depends on the lift
index. These are the nearest indices on either side of zero where it is one. -/

namespace PrimeFactors.FractionalWheelNeighbours

/-- The index-dependent gcd for the wheel through 1000 and auxiliary prime 1009. -/
private def atWheel (w : ℕ) (j : ℤ) : ℕ :=
  Nat.gcd (j+1).natAbs w * Nat.gcd (j+2).natAbs 1009

def indexGcd (j : ℤ) : ℕ := atWheel (primorial 1000) j

private theorem prime_range {a : ℕ} (prime : a.Prime) (bound : a ≤ 1008) : a ≤ 1000 := by
  by_contra! lo
  interval_cases a <;> norm_num at prime

private theorem first_gcd {k : ℕ} (low : 1 < k) (high : k ≤ 1008) :
    Nat.gcd k (primorial 1000) ≠ 1 := by
  let a := k.minFac
  have prime : a.Prime := Nat.minFac_prime (by omega)
  have small := prime_range prime ((Nat.minFac_le (by omega : 0 < k)).trans high)
  have wheel : a ∣ primorial 1000 := Finset.dvd_prod_of_mem id
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le small),prime⟩)
  exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨a,prime,Nat.minFac_dvd k,wheel⟩

/-- Inside the open interval, indices −1 and −2 are covered separately.
At every other nonzero index, |j+1| lies between 2 and 1008 and has a
prime divisor through 1000. -/
theorem interior {j : ℤ} (low : -1010 < j) (high : j < 1008) (off : j ≠ 0) :
    indexGcd j ≠ 1 := by
  intro one
  have factors {a b : ℕ} (product : a*b=1) : a=1 ∧ b=1 :=
    ⟨Nat.dvd_one.mp (product ▸ dvd_mul_right a b), Nat.dvd_one.mp (product ▸ dvd_mul_left b a)⟩
  obtain ⟨left,right⟩ := factors (a:=Nat.gcd (j+1).natAbs (primorial 1000))
    (b:=Nat.gcd (j+2).natAbs 1009) one
  by_cases special : j = -2
  · subst j
    exact (by decide : Nat.gcd ((-2 : ℤ)+2).natAbs 1009 ≠ 1) right
  by_cases first : j = -1
  · subst j
    have even : 2 ∣ primorial 1000 := Finset.dvd_prod_of_mem id
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by decide : 2<1001), Nat.prime_two⟩)
    have two : 2 ∣ Nat.gcd ((-1 : ℤ)+1).natAbs (primorial 1000) := Nat.dvd_gcd (by decide) even
    exact (by decide : ¬2 ∣ 1) (left ▸ two)
  have abs := Int.natCast_natAbs (j+1)
  have abs_lo : (1 : ℤ) < |j+1| := by
    rcases le_total 0 (j+1) with sign | sign
    · rw [abs_of_nonneg sign]; omega
    · rw [abs_of_nonpos sign]; omega
  have abs_hi : |j+1| ≤ (1008 : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
  exact first_gcd (by omega) (by omega) left

private theorem endpoints (f : ℤ → ℕ) {w : ℕ} (eqn : ∀ j, f j = atWheel w j)
    (cop : w.Coprime 1009) : f (-1010) = 1 ∧ f 0 = 1 ∧ f 1008 = 1 := by
  have unit : Nat.gcd 1009 w = 1 := cop.symm
  have negative : ((-1010 : ℤ)+1).natAbs = 1009 := by decide
  have positive : ((1008 : ℤ)+1).natAbs = 1009 := by decide
  have center : ((0 : ℤ)+1).natAbs = 1 := by decide
  simp only [eqn, atWheel, negative, positive, center, unit, Nat.gcd_one_left, one_mul]
  decide

/-- At −1010 and 1008 the first argument of the wheel gcd has absolute
value 1009, coprime to the primorial. Zero gives first argument one. -/
theorem neighbours : indexGcd (-1010) = 1 ∧ indexGcd 0 = 1 ∧ indexGcd 1008 = 1 :=
  endpoints indexGcd (w := primorial 1000) (fun _ => rfl)
    FractionalSelectedProgression.aux_coprime

end PrimeFactors.FractionalWheelNeighbours
