import PrimeFactors.CountingReadout
import Mathlib.Algebra.Polynomial.Derivative

namespace PrimeFactors

/-- The sum in the three-element field counts accepting assignments whose first
factor has bit `i` set, with both factor orientations included. -/
noncomputable def bitMarginal (n B i : ℕ) : ZMod 3 :=
  ∑ xy ∈ acceptedBox n B, ((xy.1.testBit i).toNat : ZMod 3)

/-- Each accepted orientation contributes at most one. The canonical residue
therefore retains the exact count, including a count of two. -/
theorem bitMarginal_val_semiprime {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p < q) (inside : q < B) (upper : B ≤ p * q) (i : ℕ) :
    (bitMarginal (p * q) B i).val = (p.testBit i).toNat + (q.testBit i).toNat := by
  have distinct : (p, q) ∉ ({(q, p)} : Finset (ℕ × ℕ)) := by simp [ordered.ne]
  rw [bitMarginal, acceptedBox_semiprime hp hq ordered inside upper,
    Finset.sum_insert distinct, Finset.sum_singleton, ← Nat.cast_add]
  apply ZMod.val_natCast_of_lt
  cases p.testBit i <;> cases q.testBit i <;> decide

/-- Reassembling the low binary digits returns the reduction modulo their place value. -/
theorem sum_binary_positions (x b : ℕ) :
    ∑ i ∈ Finset.range b, 2 ^ i * (x.testBit i).toNat = x % 2 ^ b := by
  induction b with
  | zero => simp [Nat.mod_one]
  | succ b ih => rw [Finset.sum_range_succ, ih, Nat.toNat_testBit, Nat.mod_pow_succ]

/-- Assemble the output as an ordinary natural number after reading each field element. -/
noncomputable def sumFromBitMarginals (n B b : ℕ) : ℕ :=
  ∑ i ∈ Finset.range b, 2 ^ i * (bitMarginal n B i).val

/-- An upper bound of `b` bits on both factors suffices to recover the full factor sum. -/
theorem sumFromBitMarginals_semiprime {p q B b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p < q) (inside : q < B) (upper : B ≤ p * q) (width : q < 2 ^ b) :
    sumFromBitMarginals (p * q) B b = p + q := by
  unfold sumFromBitMarginals
  simp_rw [bitMarginal_val_semiprime hp hq ordered inside upper, Nat.mul_add]
  rw [Finset.sum_add_distrib, sum_binary_positions, sum_binary_positions,
    Nat.mod_eq_of_lt (ordered.trans width), Nat.mod_eq_of_lt width]

/-- Tag every set bit on the first input with its own scalar. All other local weights are one. -/
noncomputable def bitTagPartition {R : Type*} [CommSemiring R] (n B b : ℕ) (tag : ℕ → R) : R :=
  ∑ xy ∈ acceptedBox n B, ∏ j ∈ Finset.range b, tag j ^ (xy.1.testBit j).toNat

private theorem bitTagWord_coordinate {R : Type*} [CommSemiring R] (x b i : ℕ)
    (hi : i < b) (t : R) :
    (∏ j ∈ Finset.range b, (if j = i then t else 1) ^ (x.testBit j).toNat) =
      t ^ (x.testBit i).toNat := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp [hi]

/-- The coordinate slice of the actual partition polynomial leaves just the selected bit tag. -/
theorem bitTagPartition_coordinate {R : Type*} [CommSemiring R] (n B b i : ℕ)
    (hi : i < b) (t : R) :
    bitTagPartition n B b (fun j => if j = i then t else 1) =
      ∑ xy ∈ acceptedBox n B, t ^ (xy.1.testBit i).toNat := by
  simp only [bitTagPartition, bitTagWord_coordinate _ b i hi]

/-- With other tags set to one, the formal derivative in the selected tag,
evaluated at one, is exactly its field-valued bit count. -/
theorem derivative_bitTagPartition (n B b i : ℕ) (hi : i < b) :
    Polynomial.eval 1 (Polynomial.derivative (bitTagPartition n B b
      (fun j => if j = i then (Polynomial.X : Polynomial (ZMod 3)) else 1))) =
        bitMarginal n B i := by
  rw [bitTagPartition_coordinate n B b i hi, Polynomial.derivative_sum,
    Polynomial.eval_finset_sum]
  simp [Polynomial.derivative_X_pow, bitMarginal]

/-- The four-bit product 143 has orientation counts 2, 1, 1, 2 and factor sum 24. -/
theorem bitMarginals_143 :
    (List.range 4).map (fun i => (bitMarginal 143 16 i).val) = [2, 1, 1, 2] ∧
    sumFromBitMarginals 143 16 4 = 24 := by decide

/-- Increasing the side past the target introduces precisely the two trivial orientations. -/
theorem acceptedBox_past_target {n B : ℕ} (hn : 1 < n) (wide : n < B) :
    acceptedBox n B = insert (1, n) (insert (n, 1) (acceptedBox n n)) := by
  ext ⟨x, y⟩
  simp only [acceptedBox, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_insert, Prod.mk.injEq]
  constructor
  · rintro ⟨_, hxy⟩
    by_cases hx : x = 1
    · exact Or.inl ⟨hx, by simpa [hx] using hxy⟩
    by_cases hy : y = 1
    · exact Or.inr (Or.inl ⟨by simpa [hy] using hxy, hy⟩)
    have hxpos : 0 < x := by
      by_contra! h; have : x = 0 := by omega
      simp [this] at hxy; omega
    have hypos : 0 < y := by
      by_contra! h; have : y = 0 := by omega
      simp [this] at hxy; omega
    refine Or.inr (Or.inr ⟨⟨?_, ?_⟩, hxy⟩)
    · simpa [hxy] using Nat.mul_lt_mul_of_pos_left (show 1 < y by omega) hxpos
    · simpa [hxy] using Nat.mul_lt_mul_of_pos_right (show 1 < x by omega) hypos
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨⟨hx, hy⟩, hxy⟩)
    · exact ⟨⟨hn.trans wide, wide⟩, one_mul _⟩
    · exact ⟨⟨wide, hn.trans wide⟩, mul_one _⟩
    · exact ⟨⟨hx.trans wide, hy.trans wide⟩, hxy⟩

/-- On the full input square, the trivial factors' bit contributions are public. -/
noncomputable def correctedBitMarginal (n B i : ℕ) : ZMod 3 :=
  bitMarginal n B i - ((1 : ℕ).testBit i).toNat - (n.testBit i).toNat

theorem correctedBitMarginal_eq {n B : ℕ} (hn : 1 < n) (wide : n < B) (i : ℕ) :
    correctedBitMarginal n B i = bitMarginal n n i := by
  have left : (1, n) ∉ insert (n, 1) (acceptedBox n n) := by
    simp [acceptedBox, Nat.ne_of_lt hn]
  have right : (n, 1) ∉ acceptedBox n n := by simp [acceptedBox]
  unfold correctedBitMarginal bitMarginal
  rw [acceptedBox_past_target hn wide, Finset.sum_insert left, Finset.sum_insert right]
  dsimp only
  ring

/-- Unbalanced distinct primes are allowed. A single characteristic-three gradient on the
unrestricted `b`-bit multiplication square gives their sum after public subtraction. -/
theorem correctedBitMarginals_fullWidth {p q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p < q) (fits : p * q < 2 ^ b) :
    ∑ i ∈ Finset.range b, 2 ^ i * (correctedBitMarginal (p * q) (2 ^ b) i).val = p + q := by
  have hqN : q < p * q := by simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hq.pos
  simp_rw [correctedBitMarginal_eq (hq.one_lt.trans hqN) fits]
  exact sumFromBitMarginals_semiprime hp hq ordered hqN le_rfl (hqN.trans fits)

/-- Over the binary field the first pass detects every bit where the factors differ. -/
noncomputable def bitMarginalTwo (n B i : ℕ) : ZMod 2 :=
  ∑ xy ∈ acceptedBox n B, ((xy.1.testBit i).toNat : ZMod 2)

theorem derivative_bitTagPartition_two (n B b i : ℕ) (hi : i < b) :
    Polynomial.eval 1 (Polynomial.derivative (bitTagPartition n B b
      (fun j => if j = i then (Polynomial.X : Polynomial (ZMod 2)) else 1))) =
        bitMarginalTwo n B i := by
  rw [bitTagPartition_coordinate n B b i hi, Polynomial.derivative_sum,
    Polynomial.eval_finset_sum]
  simp [Polynomial.derivative_X_pow, bitMarginalTwo]

theorem bitMarginalTwo_eq_one_iff {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p < q) (inside : q < B) (upper : B ≤ p * q) (i : ℕ) :
    bitMarginalTwo (p * q) B i = 1 ↔ p.testBit i ≠ q.testBit i := by
  have distinct : (p, q) ∉ ({(q, p)} : Finset (ℕ × ℕ)) := by simp [ordered.ne]
  rw [bitMarginalTwo, acceptedBox_semiprime hp hq ordered inside upper,
    Finset.sum_insert distinct, Finset.sum_singleton]
  change ((p.testBit i).toNat : ZMod 2) + (q.testBit i).toNat = 1 ↔ _
  cases p.testBit i <;> cases q.testBit i <;> decide

/-- A visible nonzero first-pass output always exists within the given width. -/
theorem exists_bitMarginalTwo_one {p q B b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p < q) (inside : q < B) (upper : B ≤ p * q) (width : q < 2 ^ b) :
    ∃ k < b, bitMarginalTwo (p * q) B k = 1 := by
  by_contra! h
  have equal : ∀ i < b, p.testBit i = q.testBit i := by
    intro i hi
    by_contra ne
    exact h i hi ((bitMarginalTwo_eq_one_iff hp hq ordered inside upper i).mpr ne)
  have same : p % 2 ^ b = q % 2 ^ b := by
    rw [← sum_binary_positions, ← sum_binary_positions]
    exact Finset.sum_congr rfl fun i hi => by rw [equal i (Finset.mem_range.mp hi)]
  rw [Nat.mod_eq_of_lt (ordered.trans width), Nat.mod_eq_of_lt width] at same
  exact ordered.ne same

/-- A zero tag at bit `k` retains the orientations whose first factor has this bit clear. -/
noncomputable def zeroBitBox (n B k : ℕ) : Finset (ℕ × ℕ) :=
  (acceptedBox n B).filter fun xy => xy.1.testBit k = false

noncomputable def pinnedBitMarginal (n B k i : ℕ) : ZMod 2 :=
  ∑ xy ∈ zeroBitBox n B k, ((xy.1.testBit i).toNat : ZMod 2)

/-- Reweight the same partition by a zero at `k` and vary bit `i`.
The zero tag stays pinned even if the varied coordinate is `k`. -/
theorem bitTagPartition_pinned_coordinate {R : Type*} [CommSemiring R] (n B b k i : ℕ)
    (hk : k < b) (hi : i < b) (t : R) :
    bitTagPartition n B b (fun j => (if j = k then 0 else 1) * (if j = i then t else 1)) =
      ∑ xy ∈ zeroBitBox n B k, t ^ (xy.1.testBit i).toNat := by
  simp only [bitTagPartition, mul_pow, Finset.prod_mul_distrib,
    bitTagWord_coordinate _ b k hk, bitTagWord_coordinate _ b i hi, zeroBitBox, Finset.sum_filter]
  refine Finset.sum_congr rfl fun xy _ => ?_
  cases xy.1.testBit k <;> simp

theorem derivative_bitTagPartition_pinned (n B b k i : ℕ) (hk : k < b) (hi : i < b) :
    Polynomial.eval 1 (Polynomial.derivative (bitTagPartition n B b (fun j =>
      (if j = k then 0 else 1) * (if j = i then (Polynomial.X : Polynomial (ZMod 2)) else 1)))) =
        pinnedBitMarginal n B k i := by
  rw [bitTagPartition_pinned_coordinate n B b k i hk hi, Polynomial.derivative_sum,
    Polynomial.eval_finset_sum]
  simp [Polynomial.derivative_X_pow, pinnedBitMarginal]

/-- Assemble the single remaining orientation using binary field outputs. -/
noncomputable def factorFromPinnedBits (n B b k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range b, 2 ^ i * (pinnedBitMarginal n B k i).val

private theorem factorFromPinnedBits_singleton {n B b k x y : ℕ}
    (single : zeroBitBox n B k = {(x, y)}) (width : x < 2 ^ b) :
    factorFromPinnedBits n B b k = x := by
  unfold factorFromPinnedBits pinnedBitMarginal
  simp only [single, Finset.sum_singleton]
  have bitval (i : ℕ) : ((x.testBit i).toNat : ZMod 2).val = (x.testBit i).toNat := by
    apply ZMod.val_natCast_of_lt
    cases x.testBit i <;> decide
  simp only [bitval, sum_binary_positions, Nat.mod_eq_of_lt width]

/-- Any nonzero first-pass coordinate selects one factor for the second pass.
The second pass returns that factor directly, using the product and the selected index. -/
theorem factorFromPinnedBits_semiprime {p q B b k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p < q) (inside : q < B) (upper : B ≤ p * q) (width : q < 2 ^ b)
    (selected : bitMarginalTwo (p * q) B k = 1) :
    factorFromPinnedBits (p * q) B b k = if p.testBit k then q else p := by
  have different := (bitMarginalTwo_eq_one_iff hp hq ordered inside upper k).mp selected
  have box := acceptedBox_semiprime hp hq ordered inside upper
  cases hpbit : p.testBit k <;> cases hqbit : q.testBit k
  · exact False.elim (different (hpbit.trans hqbit.symm))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply factorFromPinnedBits_singleton (y := q) _ (ordered.trans width)
    simp [zeroBitBox, box, hpbit, hqbit, Finset.filter_insert, Finset.filter_singleton]
  · simp only [↓reduceIte]
    apply factorFromPinnedBits_singleton (y := p) _ width
    simp [zeroBitBox, box, hpbit, hqbit, Finset.filter_insert, Finset.filter_singleton]
  · exact False.elim (different (hpbit.trans hqbit.symm))

/-- In 143 the two orientations differ at bit 1. Pinning it to zero selects 13. -/
theorem pinnedBitMarginals_143 :
    bitMarginalTwo 143 16 1 = 1 ∧ factorFromPinnedBits 143 16 4 1 = 13 := by decide

end PrimeFactors
