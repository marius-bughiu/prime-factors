import PrimeFactors.FactorSum
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.ModEq

namespace PrimeFactors

/-- Ordered input assignments in the half-open square that multiply to the target. -/
noncomputable def acceptedBox (n B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range B ×ˢ Finset.range B).filter (fun xy => xy.1 * xy.2 = n)

/-- The upper bound excludes both trivial assignments involving the factor 1. -/
theorem acceptedBox_semiprime {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p < q) (inside : q < B) (upper : B ≤ p * q) :
    acceptedBox (p * q) B = {(p, q), (q, p)} := by
  ext ⟨x, y⟩
  simp only [acceptedBox, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hx, hy⟩, hxy⟩
    have left_nontrivial : 1 < x := by
      by_contra! h
      have : x * y ≤ y := by simpa using Nat.mul_le_mul_right y h
      omega
    have right_nontrivial : 1 < y := by
      by_contra! h
      have : x * y ≤ x := by simpa using Nat.mul_le_mul_left x h
      omega
    rcases le_total x y with le | le
    · exact Or.inl (ordered_semiprime_pair_unique hp hq ordered.le le left_nontrivial hxy)
    · have pair := ordered_semiprime_pair_unique hp hq ordered.le le right_nontrivial
          ((Nat.mul_comm y x).trans hxy)
      exact Or.inr ⟨pair.2, pair.1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨ordered.trans inside, inside⟩, rfl⟩
    · exact ⟨⟨inside, ordered.trans inside⟩, Nat.mul_comm ..⟩

/-- Products of local weights retain their constant and linear terms modulo T². -/
theorem digit_weight_product_mod (T : ℕ) (cs : List ℕ) :
    Nat.ModEq (T ^ 2) ((cs.map (fun c => 1 + T * c)).prod) (1 + T * cs.sum) := by
  induction cs with
  | nil => simp [Nat.ModEq]
  | cons c cs ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ((Nat.ModEq.refl (1 + T * c)).mul ih).trans ?_
    have expansion : (1 + T * c) * (1 + T * cs.sum) =
        1 + T * (c + cs.sum) + (c * cs.sum) * T ^ 2 := by ring
    rw [expansion]
    exact Nat.add_mul_mod_self_right ..

/-- The local wire at position i carries d * radix^i for the first input digit d. -/
noncomputable def inputDigitWeight (radix T x : ℕ) : ℕ :=
  let cs := (radix.digits x).mapIdx (fun i d => d * radix ^ i)
  (cs.map (fun c => 1 + T * c)).prod

/-- The first-order weight recovers the input for every positional radix. -/
theorem inputDigitWeight_mod (radix T x : ℕ) :
    Nat.ModEq (T ^ 2) (inputDigitWeight radix T x) (1 + T * x) := by
  unfold inputDigitWeight
  simpa only [← Nat.ofDigits_eq_sum_mapIdx, Nat.ofDigits_digits] using
    digit_weight_product_mod T ((radix.digits x).mapIdx (fun i d => d * radix ^ i))

/-- Sum the digit weights of the first input over all ordered accepting assignments.
The box and target determine the whole expression. -/
noncomputable def multiplicationReadout (radix n B : ℕ) : ℕ :=
  let T := 2 * B + 1
  (∑ xy ∈ acceptedBox n B, inputDigitWeight radix T xy.1) % T ^ 2

/-- The constant term counts the two orientations. Together their linear terms
give the exact sum of the two primes without wrapping modulo T². -/
theorem multiplicationReadout_semiprime (radix : ℕ) {p q B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ordered : p < q) (inside : q < B) (upper : B ≤ p * q) :
    multiplicationReadout radix (p * q) B = 2 + (2 * B + 1) * (p + q) := by
  let T := 2 * B + 1
  have distinct : (p, q) ∉ ({(q, p)} : Finset (ℕ × ℕ)) := by simp [ordered.ne]
  change (∑ xy ∈ acceptedBox (p * q) B, inputDigitWeight radix T xy.1) % T ^ 2 = _
  rw [acceptedBox_semiprime hp hq ordered inside upper, Finset.sum_insert distinct,
    Finset.sum_singleton]
  have h := (inputDigitWeight_mod radix T p).add (inputDigitWeight_mod radix T q)
  have collect : 1 + T * p + (1 + T * q) = 2 + T * (p + q) := by ring
  rw [collect] at h
  have two_lt : 2 < T := by dsimp [T]; omega
  have fit : p + q + 1 ≤ T := by dsimp [T]; omega
  have room : 2 + T * (p + q) < T ^ 2 := by
    nlinarith only [two_lt, Nat.mul_le_mul_left T fit]
  exact Eq.trans h (Nat.mod_eq_of_lt room)

/-- Ordinary integer division of the readout recovers the exact factor sum. -/
theorem multiplicationReadout_div (radix : ℕ) {p q B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ordered : p < q) (inside : q < B) (upper : B ≤ p * q) :
    multiplicationReadout radix (p * q) B / (2 * B + 1) = p + q := by
  rw [multiplicationReadout_semiprime radix hp hq ordered inside upper,
    Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]

/-- Independently enumerate the four-bit input square and evaluate its binary weights. -/
theorem binary_readout_143 : multiplicationReadout 2 143 16 = 794 := by
  have box : acceptedBox 143 16 = {(11, 13), (13, 11)} := by decide +kernel
  have digits11 : Nat.digits 2 11 = [1, 1, 0, 1] := by norm_num [Nat.digits_of_two_le_of_pos]
  have digits13 : Nat.digits 2 13 = [1, 0, 1, 1] := by norm_num [Nat.digits_of_two_le_of_pos]
  simp [multiplicationReadout, box, inputDigitWeight, digits11, digits13]

end PrimeFactors
