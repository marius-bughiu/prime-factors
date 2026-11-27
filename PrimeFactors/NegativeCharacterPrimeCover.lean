import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-! Elementary counting of negative character values when every small prime
has nonnegative sign. Both counts keep only cofactors coprime to the modulus. -/
namespace PrimeFactors.NegativeCharacterPrimeCover

open Finset

noncomputable def negative (χ : ℕ →* ℝ) (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter fun n => χ n < 0

noncomputable def units (q X : ℕ) : Finset ℕ := (Icc 1 X).filter (·.Coprime q)

noncomputable def primes (Y X : ℕ) : Finset ℕ := (Ioc Y X).filter Nat.Prime

/-- A negative product of prime factors has at least one negative factor. -/
theorem negative_prime (χ : ℕ →* ℝ) {n : ℕ} (pos : 0 < n) (neg : χ n < 0) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ χ p < 0 := by
  induction n using induction_on_primes with
  | h₀ => omega
  | h₁ => norm_num at neg
  | h p a hp ih =>
    by_cases bad : χ p < 0
    · exact ⟨p, hp, dvd_mul_right .., bad⟩
    have aneg : χ a < 0 := by
      apply lt_of_not_ge
      intro ha
      exact (not_lt_of_ge (mul_nonneg (le_of_not_gt bad) ha)) (map_mul χ p a ▸ neg)
    obtain ⟨r, hr, div, sign⟩ := ih (Nat.pos_of_mul_pos_left pos) aneg
    exact ⟨r, hr, div.trans (dvd_mul_left ..), sign⟩

private theorem negative_pair {χ : ℕ →* ℝ} {q X Y n : ℕ}
    (support : ∀ k, χ k ≠ 0 ↔ k.Coprime q)
    (small : ∀ p : ℕ, p.Prime → p ≤ Y → 0 ≤ χ p) (hn : n ∈ negative χ X) :
    ∃ p m : ℕ, p.Prime ∧ Y < p ∧ 0 < m ∧ m.Coprime q ∧ n = p*m := by
  obtain ⟨inside, sign⟩ := mem_filter.mp hn
  obtain ⟨low, _⟩ := mem_Icc.mp inside
  obtain ⟨p, hp, ⟨m, hm⟩, bad⟩ := negative_prime χ low sign
  have cop := (support n).mp sign.ne
  rw [hm] at low cop
  exact ⟨p, m, hp, by_contra fun h => (not_lt_of_ge (small p hp (by omega))) bad,
    Nat.pos_of_mul_pos_left low, (Nat.coprime_mul_iff_left.mp cop).2, hm⟩

/-- For each possible large prime, count its positive coprime cofactors. -/
theorem negative_le_prime_sum {χ : ℕ →* ℝ} {q X Y : ℕ}
    (support : ∀ n, χ n ≠ 0 ↔ n.Coprime q)
    (small : ∀ p : ℕ, p.Prime → p ≤ Y → 0 ≤ χ p) :
    (negative χ X).card ≤ ∑ p ∈ primes Y X, (units q (X/p)).card := by
  let row (p : ℕ) := (units q (X/p)).image (p*·)
  have subset : negative χ X ⊆ (primes Y X).biUnion row := by
    intro n hn
    have range := mem_Icc.mp (mem_filter.mp hn).1
    obtain ⟨p, m, hp, above, mp, cop, rfl⟩ := negative_pair support small hn
    have px : p ≤ X := (Nat.le_mul_of_pos_right p mp).trans range.2
    have mx : m ≤ X/p := (Nat.le_div_iff_mul_le hp.pos).mpr (by
      simpa only [Nat.mul_comm m p] using range.2)
    exact mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨mem_Ioc.mpr ⟨above, px⟩, hp⟩,
      mem_image.mpr ⟨m, mem_filter.mpr ⟨mem_Icc.mpr ⟨mp, mx⟩, cop⟩, rfl⟩⟩
  exact (card_le_card subset).trans (card_biUnion_le.trans (sum_le_sum fun _ _ => card_image_le))

/-- Grouping by the coprime cofactor instead gives a sum of prime counts. -/
theorem negative_le_cofactor_sum {χ : ℕ →* ℝ} {q X Y : ℕ}
    (support : ∀ n, χ n ≠ 0 ↔ n.Coprime q)
    (small : ∀ p : ℕ, p.Prime → p ≤ Y → 0 ≤ χ p) :
    (negative χ X).card ≤ ∑ m ∈ units q (X/(Y+1)), Nat.primeCounting (X/m) := by
  let row (m : ℕ) := (X/m+1).primesBelow.image (·*m)
  have subset : negative χ X ⊆ (units q (X/(Y+1))).biUnion row := by
    intro n hn
    have range := mem_Icc.mp (mem_filter.mp hn).1
    obtain ⟨p, m, hp, above, mp, cop, rfl⟩ := negative_pair support small hn
    have mx := (Nat.le_div_iff_mul_le (Nat.succ_pos Y)).mpr
      ((Nat.mul_le_mul_left m above).trans (by simpa only [Nat.mul_comm m p] using range.2))
    have px := (Nat.le_div_iff_mul_le mp).mpr range.2
    exact mem_biUnion.mpr ⟨m, mem_filter.mpr ⟨mem_Icc.mpr ⟨mp, mx⟩, cop⟩,
      mem_image.mpr ⟨p, mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le px), hp⟩, rfl⟩⟩
  apply (card_le_card subset).trans (card_biUnion_le.trans (sum_le_sum fun m _ => ?_))
  exact card_image_le.trans_eq (Nat.primesBelow_card_eq_primeCounting' _)

/-- For values in {-1,0,1}, only negative values lower the signed sum from
the number of positive integers coprime to the modulus. Each costs exactly two. -/
theorem signed_sum {χ : ℕ →* ℝ} {q : ℕ} (X : ℕ)
    (support : ∀ n, χ n ≠ 0 ↔ n.Coprime q)
    (signs : ∀ n, χ n = -1 ∨ χ n = 0 ∨ χ n = 1) :
    ∑ n ∈ Icc 1 X, χ n = ((units q X).card : ℝ) - 2*((negative χ X).card : ℝ) := by
  classical
  have step (n : ℕ) : χ n = (if n.Coprime q then (1:ℝ) else 0) -
      2*(if χ n < 0 then 1 else 0) := by
    simp only [←support n]
    rcases signs n with h|h|h <;> simp [h] <;> norm_num
  rw [sum_congr rfl (fun n _ => step n)]
  rw [sum_sub_distrib, ←mul_sum]
  simp [units, negative, sum_boole]

/-- Any stronger upper bound on the signed sum forces a negative prime at
most Y. All analytic estimates can be supplied separately. -/
theorem exists_negative_prime_le {χ : ℕ →* ℝ} {q X Y : ℕ}
    (support : ∀ n, χ n ≠ 0 ↔ n.Coprime q)
    (signs : ∀ n, χ n = -1 ∨ χ n = 0 ∨ χ n = 1)
    (below : (∑ n ∈ Icc 1 X, χ n) <
      ((units q X).card : ℝ) - 2*((∑ p ∈ primes Y X, (units q (X/p)).card : ℕ) : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ Y ∧ χ p < 0 := by
  by_contra no
  have small (p : ℕ) (hp : p.Prime) (le : p ≤ Y) : 0 ≤ χ p :=
    le_of_not_gt fun neg => no ⟨p, hp, le, neg⟩
  have bound : ((negative χ X).card : ℝ) ≤ (∑ p ∈ primes Y X, (units q (X/p)).card : ℕ) := by
    exact_mod_cast negative_le_prime_sum support small
  rw [signed_sum X support signs] at below
  linarith

end PrimeFactors.NegativeCharacterPrimeCover
