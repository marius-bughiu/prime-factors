import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PrimeFactors

open Finset

set_option exponentiation.threshold 3000

/-- The primes up to and including the cutoff. -/
noncomputable def quotientBudgetPrimes (k : ℕ) : Finset ℕ :=
  (range (k + 1)).filter Nat.Prime

/-- Mathlib's primorial, written with the same prime set as the cardinal bounds. -/
abbrev quotientBudgetWheel := primorial

private theorem mem_budgetPrimes {p k : ℕ} :
    p ∈ quotientBudgetPrimes k ↔ p ≤ k ∧ p.Prime := by
  simp [quotientBudgetPrimes, Nat.lt_succ_iff]

private theorem totient_of_prime_product (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    (∏ p ∈ s, p).totient = ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have pa := hs a (mem_insert_self a s)
    have ps : ∀ p ∈ s, Nat.Prime p := fun p hp => hs p (mem_insert_of_mem hp)
    have cop : a.Coprime (∏ p ∈ s, p) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro p hp
      apply pa.coprime_iff_not_dvd.mpr
      intro dvd
      have := (Nat.dvd_prime (ps p hp)).mp dvd
      rcases this with h | h
      · exact pa.ne_one h
      · exact ha (h ▸ hp)
    rw [prod_insert ha, prod_insert ha, Nat.totient_mul cop, Nat.totient_prime pa, ih ps]

theorem quotientBudgetWheel_totient (k : ℕ) :
    (quotientBudgetWheel k).totient = ∏ p ∈ quotientBudgetPrimes k, (p - 1) :=
  totient_of_prime_product _ fun _ h => (mem_budgetPrimes.mp h).2

-- Trial divisors below 32 suffice for the three finite checks.
private noncomputable def budgetTrial (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range 32).all (fun d => decide (d < 2 ∨ n ≤ d ∨ n % d ≠ 0))

private theorem budgetTrial_correct {n : ℕ} (small : n ≤ 991) :
    budgetTrial n = true ↔ n.Prime := by
  simp only [budgetTrial, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hn, h⟩
    by_contra composite
    have square := Nat.minFac_sq_le_self (by omega : 0 < n) composite
    have below : n.minFac < 32 := by
      by_contra! large
      have comp := Nat.pow_le_pow_left large 2
      omega
    have point := h _ below
    have prime := Nat.minFac_prime (by omega : n ≠ 1)
    have lt := (Nat.not_prime_iff_minFac_lt hn).mp composite
    have divides := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)
    have := prime.two_le
    omega
  · intro prime
    refine ⟨prime.two_le, fun d _ => ?_⟩
    by_contra! h
    have sides := (Nat.dvd_prime prime).mp (Nat.dvd_of_mod_eq_zero h.2.2)
    omega

private theorem budgetPrimes_trial (k : ℕ) (h : k ≤ 991) :
    quotientBudgetPrimes k = (range (k+1)).filter (fun p => budgetTrial p = true) := by
  ext p
  simp only [mem_budgetPrimes, mem_filter, mem_range, Nat.lt_succ_iff]
  exact and_congr_right fun hp => (budgetTrial_correct (hp.trans h)).symm

private def budgetFacts (a b c : Finset ℕ) : Prop :=
  a.card = 167 ∧ 2^1366 < ∏ p ∈ a, p ∧ b.card = 166 ∧
  (∏ p ∈ b, p) < 13*(∏ p ∈ b, (p-1)) ∧ 11*(∏ p ∈ c, (p-1)) < (∏ p ∈ c, p) ∧
    (∏ p ∈ c, p) < 2^641

private theorem facts_transfer {i j k : ℕ} {a b c : Finset ℕ}
    (hi : quotientBudgetPrimes i = a) (hj : quotientBudgetPrimes j = b)
    (hk : quotientBudgetPrimes k = c) (facts : budgetFacts a b c) :
    (quotientBudgetPrimes i).card = 167 ∧ 2^1366 < quotientBudgetWheel i ∧
    (quotientBudgetPrimes j).card = 166 ∧
    quotientBudgetWheel j < 13*(quotientBudgetWheel j).totient ∧
    11*(quotientBudgetWheel k).totient < quotientBudgetWheel k ∧
    quotientBudgetWheel k < 2^641 := by
  subst a b c
  rw [quotientBudgetWheel_totient j, quotientBudgetWheel_totient k]
  exact facts

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
theorem quotientBudget_primorial_constants :
    (quotientBudgetPrimes 991).card = 167 ∧ 2^1366 < quotientBudgetWheel 991 ∧
    (quotientBudgetPrimes 983).card = 166 ∧
    quotientBudgetWheel 983 < 13 * (quotientBudgetWheel 983).totient ∧
    11 * (quotientBudgetWheel 463).totient < quotientBudgetWheel 463 ∧
    quotientBudgetWheel 463 < 2^641 := by
  apply facts_transfer (budgetPrimes_trial 991 (by decide))
    (budgetPrimes_trial 983 (by decide)) (budgetPrimes_trial 463 (by decide))
  unfold budgetFacts
  decide +kernel

/-- Complete an exchange of differing entries by comparing every entry to the same cutoff. -/
theorem quotientBudget_product_exchange {R : Type*} [CommMonoidWithZero R] [PartialOrder R]
    [ZeroLEOneClass R] [PosMulMono R] [MulPosMono R] {s t : Finset ℕ} (f : ℕ → R) {cut : R}
    (hc : 1 ≤ cut) (card : s.card ≤ t.card) (pos : ∀ x ∈ s, 0 ≤ f x)
    (lo : ∀ x ∈ s \ t, f x ≤ cut) (hi : ∀ x ∈ t \ s, cut ≤ f x) :
    ∏ x ∈ s, f x ≤ ∏ x ∈ t, f x := by
  have hcard : (s \ t).card ≤ (t \ s).card := by
    have a := card_sdiff_add_card_inter s t
    have b := card_sdiff_add_card_inter t s
    rw [inter_comm t s] at b
    omega
  have a : ∏ x ∈ s \ t, f x ≤ cut^(s \ t).card := by
    simpa using Finset.prod_le_prod (fun x hx => pos x (mem_sdiff.mp hx).1) lo
  have b : cut^(t \ s).card ≤ ∏ x ∈ t \ s, f x := by
    simpa using Finset.prod_le_prod (fun _ _ => zero_le_one.trans hc) hi
  have diff := a.trans ((pow_le_pow_right₀ hc hcard).trans b)
  have full := mul_le_mul_of_nonneg_right diff
    (Finset.prod_nonneg (s := s ∩ t) (f := f) fun x hx => pos x (mem_inter.mp hx).1)
  rw [← Finset.prod_union (disjoint_sdiff_inter s t), sdiff_union_inter] at full
  rwa [inter_comm s t, ← Finset.prod_union (disjoint_sdiff_inter t s), sdiff_union_inter] at full

/-- A wheel below a primorial has fewer distinct prime factors than it.
For equal cardinalities, replacing a small prime by a larger one increases the product. -/
theorem quotientBudget_primeFactors_below {m k : ℕ} (positive : 0 < m) (hk : 1 ≤ k)
    (bound : m < quotientBudgetWheel k) :
    m.primeFactors.card < (quotientBudgetPrimes k).card := by
  by_contra! many
  have h := quotientBudget_product_exchange (s := quotientBudgetPrimes k) (t := m.primeFactors)
    (fun p => p) (cut := k) hk many (by simp)
    (fun _ hp => (mem_budgetPrimes.mp (mem_sdiff.mp hp).1).1) (by
      intro p hp
      obtain ⟨inside, outside⟩ := mem_sdiff.mp hp
      have pp := Nat.prime_of_mem_primeFactors inside
      have large : ¬ p ≤ k := fun hpk => outside (mem_budgetPrimes.mpr ⟨hpk, pp⟩)
      exact Nat.le_of_lt (lt_of_not_ge large))
  exact (not_le_of_gt bound) (h.trans (Nat.le_of_dvd positive (Nat.prod_primeFactors_dvd m)))

/-- Any wheel with 167 distinct prime factors is at least the 167th primorial. -/
theorem quotientBudget_primeFactors_card {m : ℕ} (positive : 0 < m) (bound : m ≤ 2^1366) :
    m.primeFactors.card ≤ 166 := by
  obtain ⟨card, primorial, _⟩ := quotientBudget_primorial_constants
  have := quotientBudget_primeFactors_below positive (by decide : 1 ≤ 991) (bound.trans_lt primorial)
  omega


private noncomputable def primeLoss (p : ℕ) : ℚ := p / ((p - 1 : ℕ) : ℚ)

private theorem primeLoss_antitone {p q : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    primeLoss q ≤ primeLoss p := by
  have posp : 0 < (p - 1 : ℕ) := by omega
  have posq : 0 < (q - 1 : ℕ) := by omega
  have hp' : ((p-1 : ℕ):ℚ) = (p:ℚ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
  have hq' : ((q-1 : ℕ):ℚ) = (q:ℚ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ q)]; norm_num
  apply (div_le_div_iff₀ (by exact_mod_cast posq) (by exact_mod_cast posp)).mpr
  rw [hp', hq']
  have hcast : (p:ℚ) ≤ q := by exact_mod_cast hpq
  linarith

private theorem primeLoss_prod (s : Finset ℕ) :
    ∏ p ∈ s, primeLoss p = ((∏ p ∈ s, p : ℕ) : ℚ) / ((∏ p ∈ s, (p-1) : ℕ) : ℚ) := by
  simp only [primeLoss, ← Finset.prod_div_distrib, Nat.cast_prod]

/-- The first 166 primes maximize the loss from retaining only reduced residue classes. -/
theorem quotientBudget_wheel_ratio {m : ℕ} (positive : 0 < m) (bound : m ≤ 2^1366) :
    m < 13 * m.totient := by
  obtain ⟨_, _, card, ratio, _⟩ := quotientBudget_primorial_constants
  have count := quotientBudget_primeFactors_card positive bound
  have h := quotientBudget_product_exchange (s := m.primeFactors) (t := quotientBudgetPrimes 983)
    primeLoss (cut := primeLoss 983) (by norm_num [primeLoss]) (by omega)
    (fun p _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by
      intro p hp
      obtain ⟨inside, outside⟩ := mem_sdiff.mp hp
      have pp := Nat.prime_of_mem_primeFactors inside
      have large : ¬ p ≤ 983 := fun hpk => outside (mem_budgetPrimes.mpr ⟨hpk, pp⟩)
      exact primeLoss_antitone (by decide) (Nat.le_of_lt (lt_of_not_ge large))) (by
      intro p hp
      obtain ⟨le, prime⟩ := mem_budgetPrimes.mp (mem_sdiff.mp hp).1
      exact primeLoss_antitone prime.two_le le)
  rw [primeLoss_prod, primeLoss_prod, ← quotientBudgetWheel_totient] at h
  change _ ≤ (quotientBudgetWheel 983 : ℚ) / (quotientBudgetWheel 983).totient at h
  have wheelpos : 0 < quotientBudgetWheel 983 := Finset.prod_pos fun _ hp =>
    (mem_budgetPrimes.mp hp).2.pos
  have hratio : (quotientBudgetWheel 983 : ℚ) / (quotientBudgetWheel 983).totient < 13 := by
    apply (div_lt_iff₀ (by exact_mod_cast (Nat.totient_pos.mpr wheelpos))).mpr
    exact_mod_cast ratio
  have denom : 0 < ∏ p ∈ m.primeFactors, (p-1) := Finset.prod_pos fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hsmall : (∏ p ∈ m.primeFactors, p) < 13 * ∏ p ∈ m.primeFactors, (p-1) := by
    have := (div_lt_iff₀ (by exact_mod_cast denom)).mp (h.trans_lt hratio)
    exact_mod_cast this
  have hmul := Nat.mul_lt_mul_of_pos_left hsmall (Nat.totient_pos.mpr positive)
  rw [Nat.totient_mul_prod_primeFactors] at hmul
  have reshuffle : m.totient * (13 * ∏ p ∈ m.primeFactors, (p-1)) =
      (13 * m.totient) * ∏ p ∈ m.primeFactors, (p-1) := by ring
  rw [reshuffle] at hmul
  exact (mul_lt_mul_right (by omega : 0 < ∏ p ∈ m.primeFactors, (p-1))).mp hmul

/-- Cubic volume lower bound, after the totient loss has been controlled. -/
theorem quotientBudget_lower_of_ratio {N m φ C : ℕ} (hN : 2^2047 ≤ N)
    (hφ : 0 < φ) (ratio : m ≤ 13 * φ) (volume : N * φ^3 ≤ (3*m*C)^3) :
    2^677 < C := by
  by_contra! hc
  have width : 3*m*C ≤ φ*(39*2^677) := calc
    3*m*C ≤ 3*(13*φ)*2^677 := Nat.mul_le_mul (Nat.mul_le_mul_left _ ratio) hc
    _ = φ*(39*2^677) := by ring
  have comp := volume.trans (Nat.pow_le_pow_left width 3)
  rw [mul_pow, mul_comm N] at comp
  have small := Nat.le_of_mul_le_mul_left comp (Nat.pow_pos hφ)
  have cut : (39*2^677)^3 < (2:ℕ)^2047 := by decide +kernel
  omega

/-- The explicit upper wheel obtains strictly fewer than 2^678 cells under
the displayed real-valued scheduling bound. -/
theorem quotientBudget_upper {C N : ℕ} {x : ℝ} (range : N < 2^2048)
    (cube : x^3 = N)
    (cells : (C : ℝ) ≤ (quotientBudgetWheel 463).totient + (5/132)*x) :
    C < 2^678 := by
  have hroot : x < 26*2^678 := by
    by_contra! large
    have a : ((26*2^678:ℝ)^3) ≤ x^3 := by gcongr
    rw [cube] at a
    have edge : (2:ℕ)^2048 ≤ (26*2^678)^3 := by decide +kernel
    have an : (26*2^678)^3 ≤ N := by exact_mod_cast a
    omega
  have wheel := quotientBudget_primorial_constants.2.2.2.2.2
  have hphi : ((quotientBudgetWheel 463).totient : ℝ) < 2^641 := by
    exact_mod_cast (Nat.totient_le _).trans_lt wheel
  have room : (2:ℝ)^641 + (5/132)*(26*2^678) < 2^678 := by norm_num
  have csmall : (C:ℝ) < 2^678 := by linarith only [cells, hphi, hroot, room]
  exact_mod_cast csmall

/-- Any modulus is bounded by twice the square of its totient. Only the prime
2 requires the factor two in the squarefree product. -/
theorem quotientBudget_totient_square (m : ℕ) : m ≤ 2 * m.totient^2 := by
  let s := m.primeFactors
  let rad := ∏ p ∈ s, p
  let small := ∏ p ∈ s, (p-1)
  have pointwise : ∀ p ∈ s, p ≤ (if p = 2 then 2 else 1) * (p-1)^2 := by
    intro p hp
    have pp := (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases two : p = 2
    · simp [two]
    · simp only [if_neg two, one_mul]
      obtain ⟨k, hk⟩ : ∃ k, p = k + 3 := ⟨p-3, by omega⟩
      rw [hk]
      have sub : k+3-1 = k+2 := by omega
      rw [sub]
      nlinarith
  have comp := Finset.prod_le_prod (fun p (_ : p ∈ s) => Nat.zero_le p) pointwise
  rw [Finset.prod_mul_distrib, Finset.prod_pow,
    Finset.prod_ite_eq' s 2 (fun _ => (2:ℕ))] at comp
  have radical : rad ≤ 2 * small^2 := comp.trans (Nat.mul_le_mul_right _ (by split <;> decide))
  have hr : m / rad * rad = m := Nat.div_mul_cancel (Nat.prod_primeFactors_dvd _)
  have hφ : m.totient = m / rad * small := Nat.totient_eq_div_primeFactors_mul _
  calc
    m = (m/rad)*rad := hr.symm
    _ ≤ (m/rad)^2 * (2 * small^2) := Nat.mul_le_mul (Nat.le_self_pow (by decide) _) radical
    _ = 2 * m.totient^2 := by rw [hφ]; ring

/-- The lower bound for every positive wheel includes the large-modulus case,
where merely retaining each reduced residue class already exceeds the budget. -/
theorem quotientBudget_lower {N m C : ℕ} (positive : 0 < m) (hN : 2^2047 ≤ N)
    (rows : m.totient ≤ C) (volume : N*m.totient^3 ≤ (3*m*C)^3) : 2^677 < C := by
  by_cases hm : m ≤ 2^1366
  · exact quotientBudget_lower_of_ratio hN (Nat.totient_pos.mpr positive)
      (quotientBudget_wheel_ratio positive hm).le volume
  · by_contra! hC
    have lim := (quotientBudget_totient_square m).trans
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (rows.trans hC) 2))
    have edge : 2*(2^677)^2 ≤ (2:ℕ)^1366 := by decide +kernel
    exact hm (lim.trans edge)

end PrimeFactors
