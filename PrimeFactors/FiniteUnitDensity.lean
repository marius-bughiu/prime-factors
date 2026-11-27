import PrimeFactors.QuotientBudget

/-! A finite primorial certificate for the density of units at the
moduli used in the discriminant prime-witness bound. -/
namespace PrimeFactors.FiniteUnitDensity

open Finset
open private PrimeFactors.primeLoss PrimeFactors.primeLoss_antitone
  PrimeFactors.primeLoss_prod PrimeFactors.mem_budgetPrimes from PrimeFactors.QuotientBudget

private def trialPrimes : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37]

private def trial (n : ℕ) : Bool :=
  decide (2 ≤ n) && trialPrimes.all (fun d => decide (n ≤ d ∨ n%d ≠ 0))

private theorem trial_correct {n : ℕ} (h : n ≤ 1600) : trial n = true ↔ n.Prime := by
  simp only [trial, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨lo,test⟩
    by_contra bad
    have sq := Nat.minFac_sq_le_self (by omega : 0 < n) bad
    have bound : n.minFac < 41 := by
      by_contra! far
      have := Nat.pow_le_pow_left far 2
      omega
    have covers : ∀ i : Fin 41, i.val.Prime → i.val ∈ trialPrimes := by decide +kernel
    have pp := Nat.minFac_prime (by omega : n ≠ 1)
    have reject := test n.minFac (covers ⟨_,bound⟩ pp)
    have lt := (Nat.not_prime_iff_minFac_lt lo).mp bad
    exact (reject.resolve_left (by omega)) (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd _))
  · intro prime
    refine ⟨prime.two_le, fun d hd => ?_⟩
    by_contra! fail
    have limits : ∀ d ∈ trialPrimes, 2 ≤ d := by decide +kernel
    have := limits d hd
    have := (Nat.dvd_prime prime).mp (Nat.dvd_of_mod_eq_zero fail.2)
    omega

private theorem trial_primes :
    quotientBudgetPrimes 1600 = (range 1601).filter (fun p => trial p = true) := by
  ext p
  simp only [PrimeFactors.mem_budgetPrimes, mem_filter, mem_range, Nat.lt_succ_iff]
  apply and_congr_right
  exact fun h => (trial_correct h).symm

private def certificate (s : Finset ℕ) : Prop :=
  2^2057 < ∏ p ∈ s, p ∧ (∏ p ∈ s, p) < 14*∏ p ∈ s, (p-1)

private theorem transfer {k : ℕ} {s : Finset ℕ}
    (eq : quotientBudgetPrimes k = s) (bounds : certificate s) :
    2^2057 < quotientBudgetWheel k ∧ quotientBudgetWheel k < 14*(quotientBudgetWheel k).totient := by
  subst s
  rw [quotientBudgetWheel_totient]
  exact bounds

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem first_primes :
    2^2057 < quotientBudgetWheel 1600 ∧
    quotientBudgetWheel 1600 < 14*(quotientBudgetWheel 1600).totient := by
  apply transfer trial_primes
  unfold certificate
  decide +kernel

private theorem density_below {M k : ℕ} (pos : 0 < M) (hk : 2 ≤ k)
    (size : M < quotientBudgetWheel k)
    (ratio : quotientBudgetWheel k < 14*(quotientBudgetWheel k).totient) :
    M < 14*M.totient := by
  have count := quotientBudget_primeFactors_below pos (by omega : 1 ≤ k) size
  have loss : 1 ≤ PrimeFactors.primeLoss k := by
    unfold PrimeFactors.primeLoss
    rw [one_le_div (by exact_mod_cast (show 0 < k-1 by omega))]
    exact_mod_cast Nat.sub_le k 1
  have bound := quotientBudget_product_exchange (s:=M.primeFactors) (t:=quotientBudgetPrimes k)
    PrimeFactors.primeLoss (cut:=PrimeFactors.primeLoss k) loss
    count.le (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by
      intro p hp
      obtain ⟨inside,outside⟩ := mem_sdiff.mp hp
      have prime := Nat.prime_of_mem_primeFactors inside
      have above : ¬p ≤ k := fun h => outside (PrimeFactors.mem_budgetPrimes.mpr ⟨h,prime⟩)
      exact PrimeFactors.primeLoss_antitone hk (by omega)) (by
      intro p hp
      obtain ⟨le,prime⟩ := PrimeFactors.mem_budgetPrimes.mp (mem_sdiff.mp hp).1
      exact PrimeFactors.primeLoss_antitone prime.two_le le)
  rw [PrimeFactors.primeLoss_prod, PrimeFactors.primeLoss_prod, ←quotientBudgetWheel_totient] at bound
  change _ ≤ (quotientBudgetWheel k:ℚ)/(quotientBudgetWheel k).totient at bound
  have wheel : (quotientBudgetWheel k:ℚ)/(quotientBudgetWheel k).totient < 14 := by
    apply (div_lt_iff₀ (by exact_mod_cast Nat.totient_pos.mpr (primorial_pos k))).mpr
    exact_mod_cast ratio
  let D := ∏ p ∈ M.primeFactors, (p-1)
  have dpos : 0 < D := Finset.prod_pos fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have prime_bound : (∏ p ∈ M.primeFactors, p) < 14*D := by
    exact_mod_cast (div_lt_iff₀ (show (0:ℚ)<D by exact_mod_cast dpos)).mp (bound.trans_lt wheel)
  have final := Nat.mul_lt_mul_of_pos_left prime_bound (Nat.totient_pos.mpr pos)
  rw [Nat.totient_mul_prod_primeFactors] at final
  exact (mul_lt_mul_right dpos).mp (by simpa [D, Nat.mul_assoc, Nat.mul_left_comm] using final)

/-- At every positive modulus below 2^2057, more than one fourteenth of
the residue classes are units. The loss is maximal at the smallest primes. -/
theorem density {M : ℕ} (pos : 0 < M) (high : M < 2^2057) : M < 14*M.totient :=
  density_below pos (by decide : 2 ≤ 1600) (high.trans first_primes.1) first_primes.2

end PrimeFactors.FiniteUnitDensity
