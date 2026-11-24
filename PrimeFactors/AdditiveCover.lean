import PrimeFactors.SieveInterval

namespace PrimeFactors

/-- Any two finite tables covering every accepted offset by a pair of entries
must have at least as many pairs as there are survivors in the complete periods.
The rule that decodes a pair into an offset can be arbitrary. -/
theorem periodic_pair_cover_card {M : ℕ} (hM : 0 < M) (P : ZMod M → Prop)
    (start W : ℕ) {α β : Type*} [Finite α] [Finite β] (decode : α × β → ℕ)
    (cover : ∀ k : Fin W, P ((start + k.val : ℕ) : ZMod M) → ∃ pair, decode pair = k.val) :
    W / M * Nat.card {r : ZMod M // P r} ≤ Nat.card α * Nat.card β := by
  classical
  let hits := {k : Fin W // P ((start + k.val : ℕ) : ZMod M)}
  let choosePair (k : hits) := Classical.choose (cover k.val k.property)
  have decodes (k : hits) : decode (choosePair k) = k.val.val :=
    Classical.choose_spec (cover k.val k.property)
  have injective : Function.Injective choosePair := by
    intro x y h
    apply Subtype.ext
    apply Fin.ext
    rw [← decodes x, h, decodes y]
  have upper := Nat.card_le_card_of_injective choosePair injective
  rw [Nat.card_prod] at upper
  exact (periodic_interval_lower_bound hM P start W).trans upper

/-- For finite additive tables of signed offsets, their combined size must be
at least twice the square root of the guaranteed survivor count. This allows
overlapping sum representations and tables producing additional false sums. -/
theorem periodic_additive_cover_size {M : ℕ} (hM : 0 < M) (P : ZMod M → Prop)
    (start W : ℕ) (A B : Finset ℤ)
    (cover : ∀ k : Fin W, P ((start + k.val : ℕ) : ZMod M) →
      ∃ a ∈ A, ∃ b ∈ B, a + b = (k.val : ℤ)) :
    4 * (W / M * Nat.card {r : ZMod M // P r}) ≤ (A.card + B.card) ^ 2 := by
  let decode (pair : A × B) := (pair.1.val + pair.2.val).toNat
  have covers (k : Fin W) (hk : P ((start + k.val : ℕ) : ZMod M)) :
      ∃ pair : A × B, decode pair = k.val := by
    obtain ⟨a, ha, b, hb, sum⟩ := cover k hk
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), by simp [decode, sum]⟩
  have productBound := periodic_pair_cover_card hM P start W decode covers
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe] at productBound
  calc
    _ ≤ 4 * (A.card * B.card) := Nat.mul_le_mul_left 4 productBound
    _ ≤ _ := by simpa only [Nat.mul_assoc] using four_mul_le_sq_add A.card B.card

/-- Two tables of `m` entries cover every offset in any interval with width at
most `m²`, by taking the quotient and remainder of the offset. -/
theorem square_stride_covers_offsets {m W : ℕ} (hm : 0 < m) (width : W ≤ m ^ 2)
    (k : Fin W) : ∃ i j : Fin m, i.val * m + j.val = k.val := by
  have quotient : k.val / m < m := (Nat.div_lt_iff_lt_mul hm).mpr (by
    simpa only [pow_two] using k.isLt.trans_le width)
  exact ⟨⟨k.val / m, quotient⟩, ⟨k.val % m, Nat.mod_lt _ hm⟩, Nat.div_add_mod' _ _⟩

end PrimeFactors
