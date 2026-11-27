import PrimeFactors.MinimalPrimeSquarePeriod

/-! Least periods of admissible factor sums at every positive precision of an
odd prime. For a square unit the number of additional residues excluded by a
single digit depends only on the parity of the preceding precision. -/

namespace PrimeFactors.PrimePowerEssentialDigits

open MinimalPrimeSquarePeriod
open scoped Classical

variable {p n : ℕ} [Fact p.Prime]

private theorem square_count_unit (odd : p ≠ 2) (k : ℕ) :
    ¬ p ∣ primePowerSquareCount p k := by
  have prime := (Fact.out : p.Prime)
  have three : 2 < p := by have := prime.two_le; omega
  match k with
  | 0 => exact prime.not_dvd_one
  | 1 =>
    change ¬p ∣ (p-1)/2+1
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  | k+2 =>
    rw [primePowerSquareCount]
    have d : p ∣ ((p-1)/2)*p^(k+1) :=
      dvd_mul_of_dvd_right (dvd_pow_self _ (Nat.succ_ne_zero k)) _
    exact fun h => square_count_unit odd k ((Nat.dvd_add_iff_right d).mpr h)

private theorem sum_count_unit (odd : p ≠ 2) (k : ℕ) :
    ¬p ∣ primePowerSumCount p true (k+1) := by
  have prime := (Fact.out : p.Prime)
  have three : 2 < p := by have := prime.two_le; omega
  cases k with
  | zero =>
    simp only [primePowerSumCount, collidingDigitCount, Bool.true_eq, if_true,
      pow_zero, mul_one]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  | succ k =>
    have d : p ∣ ((p-3)/2)*p^(k+1) :=
      dvd_mul_of_dvd_right (dvd_pow_self _ (Nat.succ_ne_zero k)) _
    change ¬p ∣ (p-3)/2*p^(k+1) + 2 * primePowerSquareCount p k
    intro h
    exact (prime.dvd_mul.mp ((Nat.dvd_add_iff_right d).mpr h)).elim
      (Nat.not_dvd_of_pos_of_lt (by decide) three)
      (square_count_unit odd k)

/-- When the unit product is a quadratic residue, all positive depths have
the entire modulus as their least positive period. -/
theorem square_period (odd : p ≠ 2) (unitN : ¬p ∣ n) (sq : IsSquare (n : ZMod p))
    (k t : ℕ) : Period n (p^(k+1)) t ↔ p^(k+1) ∣ t := by
  classical
  constructor
  · intro h
    have d := modulus_dvd_card_mul (AdmissibleSum (n : ZMod (p^(k+1)))) h
    have nz : firstPrimeDigit p k (n : ZMod (p^(k+1))) ≠ 0 := by
      rw [map_natCast]
      exact (ZMod.natCast_zmod_eq_zero_iff_dvd n p).mp.mt unitN
    rw [card_primePower_admissibleSum odd k _ nz, map_natCast, decide_eq_true sq] at d
    have co := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (sum_count_unit odd k)
    exact (Nat.Coprime.pow_left _ co).dvd_of_dvd_mul_left d
  · intro h x
    rw [(ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr h, add_zero]

/-- For a nonsquare product, at every positive precision a natural-number
sum passes exactly when it passes the first-digit test. -/
theorem nonsquare_pullback (odd : p ≠ 2) (sq : ¬IsSquare (n : ZMod p)) (k s : ℕ) :
    AdmissibleSum (n : ZMod (p^(k+1))) (s : ZMod (p^(k+1))) ↔
      AdmissibleSum (n : ZMod p) (s : ZMod p) := by
  have two : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have reg : (((s : ℤ)^2-4*n : ℤ) : ZMod p) ≠ 0 := by
    intro zero
    push_cast at zero
    apply sq
    refine ⟨(s : ZMod p)/2, ?_⟩
    field_simp [two]
    linear_combination -zero
  simpa only [Int.cast_natCast] using
    admissibleSum_primePow_iff_of_regular odd (n : ℤ) (s : ℤ) reg k

private theorem period_nat (n m t : ℕ) [NeZero m] : Period n m t ↔ ∀ s : ℕ,
    AdmissibleSum (n : ZMod m) ((s+t : ℕ) : ZMod m) ↔
      AdmissibleSum (n : ZMod m) (s : ZMod m) := by
  constructor
  · intro h s
    simpa only [Nat.cast_add] using h (s : ZMod m)
  · intro h x
    obtain ⟨s,rfl⟩ := ZMod.natCast_zmod_surjective x
    simpa only [Nat.cast_add] using h s

/-- A nonsquare unit product has least period p at every positive depth. -/
theorem nonsquare_period (odd : p ≠ 2) (unitN : ¬p ∣ n) (sq : ¬IsSquare (n : ZMod p))
    (k t : ℕ) : Period n (p^(k+1)) t ↔ p ∣ t := by
  rw [← MinimalPrimeSquarePeriod.nonsquare_iff odd unitN sq, period_nat, period_nat]
  simp only [nonsquare_pullback odd sq, MinimalPrimeSquarePeriod.nonsquare_pullback odd sq]

private theorem reduce {a b n s : ℕ} (h : a ∣ b)
    (pass : AdmissibleSum (n : ZMod b) (s : ZMod b)) :
    AdmissibleSum (n : ZMod a) (s : ZMod a) := by
  obtain ⟨x,y,prod,sum⟩ := pass
  let f := ZMod.castHom h (ZMod a)
  exact ⟨f x,f y,by simpa only [map_mul,map_natCast] using congrArg f prod,
    by simpa only [map_add,map_natCast] using congrArg f sum⟩

/-- Some sum accepted at the old depth fails at the next depth if and only
if the unit product is square modulo p. This concerns the entire residue set. -/
theorem next_digit_essential (odd : p ≠ 2) (unitN : ¬p ∣ n) (k : ℕ) :
    (∃ s : ℕ, AdmissibleSum (n : ZMod (p^(k+1))) (s : ZMod (p^(k+1))) ∧
      ¬AdmissibleSum (n : ZMod (p^(k+2))) (s : ZMod (p^(k+2)))) ↔
      IsSquare (n : ZMod p) := by
  constructor
  · rintro ⟨s,low,high⟩
    by_contra ns
    exact high ((nonsquare_pullback odd ns (k+1) s).mpr ((nonsquare_pullback odd ns k s).mp low))
  · intro sq
    by_contra! no
    have same (s : ℕ) : AdmissibleSum (n : ZMod (p^(k+2))) (s : ZMod (p^(k+2))) ↔
        AdmissibleSum (n : ZMod (p^(k+1))) (s : ZMod (p^(k+1))) :=
      ⟨reduce (pow_dvd_pow p (by omega)), no s⟩
    have periodic : Period n (p^(k+2)) (p^(k+1)) := by
      rw [period_nat]
      intro s
      rw [same,same,Nat.cast_add,ZMod.natCast_self,add_zero]
    have pos : 0 < p^(k+1) := pow_pos (Fact.out : p.Prime).pos _
    have bound : p^(k+1) < p^(k+2) := (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega))
    exact (Nat.not_dvd_of_pos_of_lt pos bound) ((square_period odd unitN sq (k+1) _).mp periodic)

private theorem colliding_gap (odd : p ≠ 2) (k : ℕ) :
    p*collidingDigitCount p k = collidingDigitCount p (k+1) +
      (if Even k then p-1 else (p-1)/2) := by
  obtain ⟨i,hi⟩ := (Fact.out : p.Prime).odd_of_ne_two odd
  have step (j : ℕ) : collidingDigitCount p (j+2) =
      (p-1)/2*p^j+collidingDigitCount p j := by
    cases j with
    | zero => simp [collidingDigitCount,primePowerSquareCount]
    | succ j => rfl
  match k with
  | 0 => simp [collidingDigitCount,primePowerSquareCount]; omega
  | 1 => simp [collidingDigitCount,primePowerSquareCount]; omega
  | k+2 =>
    have parity : Even (k+2) ↔ Even k := by simp [Nat.even_add]
    rw [step k,step (k+1),if_congr parity rfl rfl,Nat.mul_add,colliding_gap odd k,pow_succ]
    ring

/-- If the lower exponent is odd, the square-unit count loses exactly
2(p−1) of its possible lifts. At an even lower exponent it loses p−1. -/
theorem square_digit_loss (odd : p ≠ 2) (k : ℕ) :
    p*primePowerSumCount p true (k+1) =
      primePowerSumCount p true (k+2) + (if Even k then 2*(p-1) else p-1) := by
  change p*((p-3)/2*p^k+2*collidingDigitCount p k) =
    (p-3)/2*p^(k+1)+2*collidingDigitCount p (k+1)+_
  rw [Nat.mul_add,show p*(2*collidingDigitCount p k) =
    2*(p*collidingDigitCount p k) by ring,colliding_gap odd k,pow_succ]
  obtain ⟨i,hi⟩ := (Fact.out : p.Prime).odd_of_ne_two odd
  have half : 2*((p-1)/2) = p-1 := by omega
  by_cases even : Even k <;> simp only [even,if_true,if_false,Nat.mul_add,half] <;> ring

/-- Nonsquare units keep every lift of each accepted residue. -/
theorem nonsquare_digit_loss (p k : ℕ) :
    p*primePowerSumCount p false (k+1) = primePowerSumCount p false (k+2) := by
  change p*((p-1)/2*p^k) = (p-1)/2*p^(k+1)
  rw [pow_succ]
  ring

/-- The count identity in terms of the actual local factor-sum predicates.
Each allowed lower residue has p possible lifts before the next test. -/
theorem admissible_digit_loss (odd : p ≠ 2) (unitN : ¬p ∣ n) (k : ℕ) :
    p * Nat.card {s : ZMod (p^(k+1)) // AdmissibleSum (n : ZMod (p^(k+1))) s} =
      Nat.card {s : ZMod (p^(k+2)) // AdmissibleSum (n : ZMod (p^(k+2))) s} +
      (if IsSquare (n : ZMod p) then (if Even k then 2*(p-1) else p-1) else 0) := by
  classical
  have count (j : ℕ) :
      Nat.card {s : ZMod (p^(j+1)) // AdmissibleSum (n : ZMod (p^(j+1))) s} =
        primePowerSumCount p (decide (IsSquare (n : ZMod p))) (j+1) := by
    have nz : firstPrimeDigit p j (n : ZMod (p^(j+1))) ≠ 0 := by
      rw [map_natCast]
      exact (ZMod.natCast_zmod_eq_zero_iff_dvd n p).mp.mt unitN
    simpa only [map_natCast] using card_primePower_admissibleSum odd j _ nz
  rw [count k,count (k+1)]
  by_cases sq : IsSquare (n : ZMod p)
  · simpa only [sq,decide_true,if_true] using square_digit_loss (p := p) odd k
  · simpa only [sq,decide_false,if_false,add_zero] using nonsquare_digit_loss p k

end PrimeFactors.PrimePowerEssentialDigits
