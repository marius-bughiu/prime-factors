import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring
import PrimeFactors.ThetaResidues

namespace PrimeFactors

open PowerSeries

variable {R : Type*} [CommRing R]

/-- The weighted multiples of one allowed part size. -/
noncomputable def partitionMultiples (R : Type*) [CommRing R] (d : ℕ) : PowerSeries R :=
  mk fun n => if 0 < n ∧ d ∣ n then (d : R) else 0

private theorem partitionMultiples_step {d : ℕ} (hd : 0 < d) :
    (1 - X ^ d) * partitionMultiples R d = C R (d : R) * X ^ d := by
  ext n
  simp only [sub_mul, one_mul, map_sub, coeff_X_pow_mul', partitionMultiples, coeff_mk,
    coeff_C_mul_X_pow]
  rcases lt_trichotomy n d with h | rfl | h
  · have hnone : ¬ (0 < n ∧ d ∣ n) := fun hn => (Nat.not_le.mpr h) (Nat.le_of_dvd hn.1 hn.2)
    simp [hnone, Nat.not_le.mpr h, h.ne]
  · simp [hd]
  · have hsame : d ∣ n - d ↔ d ∣ n := by
      calc
        d ∣ n - d ↔ d ∣ (n - d) + d := Nat.dvd_add_self_right.symm
        _ ↔ d ∣ n := by rw [Nat.sub_add_cancel h.le]
    have hpos : 0 < n - d := by omega
    simp [h.le, h.ne', hpos, hsame, Nat.zero_lt_of_lt h]

private theorem part_log_equation {d : ℕ} (hd : 0 < d) :
    (1 - X ^ d) * partitionMultiples R d =
      -(derivative R (1 - X ^ d) * X) := by
  rw [partitionMultiples_step hd, map_sub, Derivation.map_one_eq_zero, zero_sub,
    neg_mul, neg_neg]
  ext n
  cases n with
  | zero => simp [hd.ne', coeff_C_mul_X_pow]
  | succ n =>
    rw [coeff_succ_mul_X, coeff_derivative, coeff_X_pow, coeff_C_mul_X_pow]
    split_ifs with h
    · subst d
      simp
    · simp

/-- The weighted-divisor series satisfies the logarithmic derivative equation for any
finite set of positive allowed parts, including over rings of even characteristic. -/
theorem finitePartition_log_equation (parts : Finset ℕ) (hpos : ∀ d ∈ parts, 0 < d) :
    (∏ d ∈ parts, (1 - X ^ d)) * (∑ d ∈ parts, partitionMultiples R d) =
      -(derivative R (∏ d ∈ parts, (1 - X ^ d)) * X) := by
  classical
  induction parts using Finset.induction_on with
  | empty => simp
  | @insert d ds hd ih =>
    have he := part_log_equation (R := R) (hpos d (Finset.mem_insert_self d ds))
    have hs := ih (fun j hj => hpos j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hd, Finset.sum_insert hd, Derivation.leibniz]
    simp only [smul_eq_mul]
    linear_combination (∏ j ∈ ds, (1 - X ^ j : PowerSeries R)) * he + (1 - X ^ d) * hs

/-- Coefficient update at a positive index. Zero coefficients of the denominator contribute
nothing; the proof does not divide by the index or any coefficient. -/
theorem partition_log_recurrence {F A : PowerSeries R} (h0 : coeff R 0 F = 1)
    (h : F * A = -(derivative R F * X)) (n : ℕ) :
    coeff R (n + 1) A = - (coeff R (n + 1) F * ((n : R) + 1)) -
      ∑ j ∈ Finset.range (n + 1), coeff R (j + 1) F * coeff R (n - j) A := by
  have eq := congrArg (coeff R (n + 1)) h
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ', h0, Nat.sub_zero, one_mul, map_neg,
      coeff_succ_mul_X, coeff_derivative] at eq
  simp only [Nat.add_sub_add_right] at eq
  rw [eq_sub_iff_add_eq]
  simpa only [add_comm] using eq

/-- Parts divisible by five added by the triple product cannot contribute at a coprime index. -/
theorem partition_parts_at_index {N : ℕ} (h5 : ¬5 ∣ N) :
    N.divisors.filter (fun d => d % 5 = 0 ∨ d % 5 = 1 ∨ d % 5 = 4) =
      N.divisors.filter (fun d => d % 5 = 1 ∨ d % 5 = 4) := by
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hd, h | h⟩
    · exact (h5 ((Nat.dvd_of_mod_eq_zero h).trans (Nat.mem_divisors.mp hd).1)).elim
    · exact ⟨hd, h⟩
  · exact fun h => ⟨h.1, Or.inr h.2⟩

/-- Each pair of consecutive powers of an odd integer contributes an even local sum. -/
theorem partition_even_local_sum (a : ℤ) (ha : Odd a) (m : ℕ) :
    2 ∣ ∑ j ∈ Finset.range (2 * m), a ^ j := by
  obtain ⟨t, ht⟩ := ha
  have hd : 2 ∣ (1 + a) := ⟨t + 1, by omega⟩
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, add_assoc,
      pow_succ a (2 * m), ← mul_one_add]
    exact dvd_add ih (dvd_mul_of_dvd_right hd _)

/-- Combining two divisor products each containing k+1 even local factors produces a
zero projected coefficient modulo 2^k, including for a projection with a negative sign. -/
theorem partition_projection_vanish {ι : Type*} (s : Finset ι)
    (f g : ι → ℤ) (hf : ∀ i ∈ s, 2 ∣ f i) (hg : ∀ i ∈ s, 2 ∣ g i)
    (u v c : ℤ) (k : ℕ) (hcard : s.card = k + 1)
    (hc : 2 * c = u * ∏ i ∈ s, f i + v * ∏ i ∈ s, g i) : (2 : ℤ) ^ k ∣ c := by
  have prod_dvd (b : ι → ℤ) (hb : ∀ i ∈ s, 2 ∣ b i) :
      (2 : ℤ) ^ (k + 1) ∣ ∏ i ∈ s, b i := by
    simpa [hcard] using
      (Finset.prod_dvd_prod_of_dvd (f := fun _ => (2 : ℤ)) (g := b) (s := s) hb)
  obtain ⟨x, hx⟩ := prod_dvd f hf
  obtain ⟨y, hy⟩ := prod_dvd g hg
  refine ⟨u * x + v * y, ?_⟩
  rw [hx, hy, pow_succ] at hc
  apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
  linear_combination hc

/-- Contribution of one divisor to the single-theta coefficient at level five. -/
def partitionFiveWeight (d : ℕ) : ℕ :=
  if d % 5 = 0 ∨ d % 5 = 1 ∨ d % 5 = 4 then d else 0

private theorem partition_weight_double {d : ℕ} (hd : ¬ 5 ∣ d) :
    2 * partitionFiveWeight d + partitionFiveWeight (2*d) = 2*d := by
  have h := mt Nat.dvd_of_mod_eq_zero hd
  have hr : d % 5 = 1 ∨ d % 5 = 2 ∨ d % 5 = 3 ∨ d % 5 = 4 := by omega
  have double : (2*d)%5 = (2*(d%5))%5 := Nat.mul_mod 2 d 5
  rcases hr with h | h | h | h <;> norm_num [partitionFiveWeight, double, h]

/-- For an odd index coprime to five, the two theta coefficients at m and 2m
sum to twice the full divisor sum. -/
theorem partition_double_sum {m : ℕ} (odd : ¬ 2 ∣ m) (unit : ¬ 5 ∣ m) :
    (∑ d ∈ m.divisors, partitionFiveWeight d) +
    (∑ d ∈ (2*m).divisors, partitionFiveWeight d) = 2 * ∑ d ∈ m.divisors, d := by
  classical
  let S := m.divisors
  have union : (2*m).divisors = S ∪ S.image (2 * ·) := by
    ext z
    rw [Nat.divisors_mul, Nat.prime_two.divisors, Finset.mem_mul, Finset.mem_union,
      Finset.mem_image]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨a,ha,b,hb,rfl⟩
      rcases ha with rfl | rfl
      · exact Or.inl (by simpa only [one_mul] using hb)
      · exact Or.inr ⟨b,hb,rfl⟩
    · rintro (hz | ⟨b,hb,rfl⟩)
      · exact ⟨1,Or.inl rfl,z,hz,one_mul _⟩
      · exact ⟨2,Or.inr rfl,b,hb,rfl⟩
  have disj : Disjoint S (S.image (2 * ·)) := by
    apply Finset.disjoint_left.mpr
    intro z hz him
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp him
    exact odd ((dvd_mul_right 2 b).trans (Nat.mem_divisors.mp hz).1)
  change (∑ d ∈ S, partitionFiveWeight d) + _ = 2 * ∑ d ∈ S, d
  rw [union, Finset.sum_union disj, Finset.sum_image]
  · rw [← add_assoc, ← two_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun d hd => partition_weight_double
      (fun h => unit (h.trans (Nat.mem_divisors.mp hd).1)))
  · intro x hx y hy h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h

/-- A pair of zero coefficients at precision k+1 forces the divisor sum to
have at least k factors of two. -/
theorem partition_double_zero_dvd {m k : ℕ} (odd : ¬ 2 ∣ m) (unit : ¬ 5 ∣ m)
    (first : 2^(k+1) ∣ ∑ d ∈ m.divisors, partitionFiveWeight d)
    (second : 2^(k+1) ∣ ∑ d ∈ (2*m).divisors, partitionFiveWeight d) :
    2^k ∣ ∑ d ∈ m.divisors, d := by
  have h := dvd_add first second
  rw [partition_double_sum odd unit, pow_succ, Nat.mul_comm (2^k) 2] at h
  exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) h


end PrimeFactors
