import PrimeFactors.CyclotomicEnergyResidues

/-! The ordinary sum of the least residues of two units with fixed product. -/
namespace PrimeFactors.FractionalPrefixResidues

/-- The two least nonnegative representatives are added as natural numbers. -/
def correction {m : ℕ} (u x : (ZMod m)ˣ) : ℕ :=
  (x : ZMod m).val + ((u / x : (ZMod m)ˣ) : ZMod m).val

private theorem val_pair {m : ℕ} [NeZero m] (hm : 2 ≤ m) (x : (ZMod m)ˣ) :
    (x : ZMod m).val + ((-x : (ZMod m)ˣ) : ZMod m).val = m := by
  letI : Nontrivial (ZMod m) := ZMod.nontrivial_iff.mpr (by omega)
  letI : NeZero (x : ZMod m) := ⟨x.ne_zero⟩
  rw [Units.val_neg, ZMod.val_neg_of_ne_zero]
  have := ZMod.val_lt (x : ZMod m)
  omega

/-- Negating both factors reflects the sum about the modulus. -/
theorem reflection {m : ℕ} [NeZero m] (hm : 2 ≤ m) (u x : (ZMod m)ˣ) :
    correction u x + correction u (-x) = 2*m := by
  have quotient : u / (-x) = -(u / x) := by simp [div_eq_mul_inv]
  simp only [correction, quotient]
  have := val_pair hm x
  have := val_pair hm (u/x)
  omega

private theorem all_squares_iff {m : ℕ} [NeZero m] :
    (∀ x : (ZMod m)ˣ, x^2 = 1) ↔ m ∣ 24 := by
  constructor
  · intro sqs
    have signed : CyclotomicEnergyResidues.SignedSquares m := fun x => Or.inl (sqs x)
    rcases CyclotomicEnergyResidues.classification.mp
      ((CyclotomicEnergyResidues.productOnly_iff m).mpr signed) with hd | rfl | rfl
    · exact hd
    · have counter := congrArg Units.val (sqs (ZMod.unitOfCoprime 2 (by decide)))
      change (2 : ZMod 5)^2 = 1 at counter
      exact False.elim ((by decide +kernel : (2 : ZMod 5)^2 ≠ 1) counter)
    · have counter := congrArg Units.val (sqs (ZMod.unitOfCoprime 3 (by decide)))
      change (3 : ZMod 10)^2 = 1 at counter
      exact False.elim ((by decide +kernel : (3 : ZMod 10)^2 ≠ 1) counter)
  · intro hd x
    obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hd x
    have at24 : ∀ y : (ZMod 24)ˣ, y^2=1 := by decide +kernel
    simpa only [map_pow, map_one] using congrArg (ZMod.unitsMap hd) (at24 v)

/-- Every divisor of 24 gives the constant sum m for the product −1. -/
theorem correction_of_dvd {m : ℕ} [NeZero m] (hm : 2 ≤ m) (dvd : m ∣ 24)
    (x : (ZMod m)ˣ) : correction (-1) x = m := by
  have inv : x⁻¹ = x := by
    apply mul_right_cancel (b := x)
    simpa only [inv_mul_cancel, ← sq] using ((all_squares_iff.mpr dvd) x).symm
  simpa only [correction, div_eq_mul_inv, inv, neg_one_mul] using val_pair hm x

/-- The value of any constant correction and the complete classification of its moduli. -/
theorem constant_value_iff {m : ℕ} [NeZero m] (hm : 2 ≤ m) (u : (ZMod m)ˣ) (c : ℕ) :
    (∀ x, correction u x = c) ↔ c = m ∧ u = -1 ∧ m ∣ 24 := by
  constructor
  · intro h
    have symm := reflection hm u 1
    rw [h, h] at symm
    have cm : c = m := by omega
    have opposite (x : (ZMod m)ˣ) : u / x = -x := by
      have val := congrArg (fun a : ℕ => (a : ZMod m)) ((h x).trans cm)
      simp only [correction, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self] at val
      exact Units.ext (eq_neg_of_add_eq_zero_right val)
    have neg : u = -1 := by simpa using opposite 1
    refine ⟨cm, neg, all_squares_iff.mp (fun x => ?_)⟩
    have prod := congrArg (fun y => y*x) (opposite x)
    simpa only [div_mul_cancel, neg_mul, neg, neg_inj, ← sq] using prod.symm
  · rintro ⟨rfl, rfl, hd⟩
    exact correction_of_dvd hm hd

theorem constant_iff {m : ℕ} [NeZero m] (hm : 2 ≤ m) (u : (ZMod m)ˣ) :
    (∃ c : ℕ, ∀ x, correction u x = c) ↔ u = -1 ∧ m ∣ 24 := by
  constructor
  · rintro ⟨c,h⟩
    exact ((constant_value_iff hm u c).mp h).2
  · intro h
    exact ⟨m,(constant_value_iff hm u m).mpr ⟨rfl,h⟩⟩

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 4096 in
/-- Even the shortest interval with a universally constant correction
contains more than 2^2042 positive integers for a 2048-bit input. -/
theorem full_width_cutoff {n m : ℕ} [NeZero m] (hn : 2^2047 ≤ n) (hm : 2 ≤ m)
    (u : (ZMod m)ˣ) (constant : ∃ c : ℕ, ∀ x, correction u x = c) :
    2^2042 < n/m := by
  have bound := Nat.le_of_dvd (by decide : 0 < 24) ((constant_iff hm u).mp constant).2
  apply (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr
  exact (Nat.mul_le_mul_left (2^2042+1) bound).trans
    ((by norm_num : (2^2042+1)*24 ≤ (2^2047 : ℕ)).trans hn)

end PrimeFactors.FractionalPrefixResidues
