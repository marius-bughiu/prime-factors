import PrimeFactors.FactorSum
import PrimeFactors.OppositeSquareScaleBands
import Mathlib.Tactic.FinCases

/-! A prefix of the balanced sum interval for 34387 has a witness for each
pair of three local tests. The witnesses occupy different positions and the
full intersection is empty. -/

namespace PrimeFactors.PairwiseSumObstruction

/-- If each test rules out exactly its own position, the intersection on a
subfamily contains exactly the positions indexed outside that subfamily.
This assertion assumes the pass pattern and makes no claim about realizing
arbitrary patterns inside a product's balanced interval. -/
theorem passes_subfamily_iff {ι α : Type*} {test : ι → α → Prop} {row : ι → α}
    (pattern : ∀ i j, test i (row j) ↔ i ≠ j) (I : Set ι) (j : ι) :
    (∀ i ∈ I, test i (row j)) ↔ j ∉ I := by
  constructor
  · exact fun h hj => (pattern j j).mp (h j hj) rfl
  · intro hj i hi
    exact (pattern i j).mpr (fun eq => hj (eq ▸ hi))

/-- The first three sums in the product-determined class modulo four. -/
def candidate (j : Fin 3) : ℕ := 372 + 4 * j.val

/-- The order matches the position each prime excludes. -/
def modulus (i : Fin 3) : ℕ :=
  match i.val with
  | 0 => 3
  | 1 => 13
  | _ => 11

def passes (i : Fin 3) (s : ℕ) : Prop :=
  AdmissibleSum (34387 : ZMod (modulus i)) (s : ZMod (modulus i))

/-- The nine entries of the local admissibility table. Thus 372 witnesses
the pair 13,11, 376 witnesses 3,11, and 380 witnesses 3,13. -/
theorem pass_table (i j : Fin 3) : passes i (candidate j) ↔ i ≠ j := by
  fin_cases i <;> fin_cases j <;> dsimp [passes, modulus, candidate, AdmissibleSum] <;>
    decide +kernel

/-- These candidates lie in the actual balanced window and satisfy the
same modulo-four factor-pair test as the true sum. -/
def inBand (s : ℕ) : Prop :=
  OppositeSquareScaleBands.InSumWindow 34387 s ∧ AdmissibleSum (34387 : ZMod 4) (s : ZMod 4)

private theorem band_bounds {s : ℕ} (band : inBand s) : 371 ≤ s ∧ s % 4 = 0 := by
  obtain ⟨⟨lower, _⟩, four⟩ := band
  constructor
  · by_contra! small
    have := Nat.pow_le_pow_left (show s ≤ 370 by omega) 2
    omega
  · have residue : ∀ z : ZMod 4, AdmissibleSum 34387 z → z = 0 := by
      unfold AdmissibleSum
      decide +kernel
    simpa only [ZMod.val_natCast, ZMod.val_zero] using congrArg ZMod.val (residue _ four)

/-- Cutting the balanced interval just before 384 leaves exactly the three
tested positions. -/
theorem prefix_iff {s : ℕ} : inBand s ∧ s < 384 ↔ ∃ j, s = candidate j := by
  constructor
  · rintro ⟨band, hi⟩
    obtain ⟨lo, four⟩ := band_bounds band
    have : s = 372 ∨ s = 376 ∨ s = 380 := by omega
    rcases this with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨j, rfl⟩
    fin_cases j <;> unfold inBand OppositeSquareScaleBands.InSumWindow AdmissibleSum <;>
      decide +kernel

/-- Every subfamily of the three primes has a witness in this prefix if
and only if at least one prime has been omitted. In particular all three
pairs pass the existence test and the full set fails it. -/
theorem prefix_has_witness_iff (I : Set (Fin 3)) :
    (∃ s, (inBand s ∧ s < 384) ∧ ∀ i ∈ I, passes i s) ↔ ∃ j, j ∉ I := by
  constructor
  · rintro ⟨s, band, hits⟩
    obtain ⟨j, rfl⟩ := prefix_iff.mp band
    exact ⟨j, (passes_subfamily_iff pass_table I j).mp hits⟩
  · rintro ⟨j, missing⟩
    exact ⟨candidate j, prefix_iff.mpr ⟨j, rfl⟩,
      (passes_subfamily_iff pass_table I j).mpr missing⟩

/-- The fifth possible sum is the first to pass the three tests jointly. -/
theorem first_joint : IsLeast {s | inBand s ∧ ∀ i, passes i s} 388 := by
  constructor
  · constructor
    · unfold inBand OppositeSquareScaleBands.InSumWindow AdmissibleSum
      decide +kernel
    · intro i
      fin_cases i <;> dsimp [passes, modulus, AdmissibleSum] <;> decide +kernel
  · intro s hs
    obtain ⟨band, hits⟩ := hs
    apply Nat.le_of_not_gt
    intro earlier
    have four := (band_bounds band).2
    by_cases cut : s < 384
    · obtain ⟨j, rfl⟩ := prefix_iff.mp ⟨band, cut⟩
      exact (pass_table j j).mp (hits j) rfl
    · have eq : s = 384 := by omega
      subst s
      have fails : ¬passes 0 384 := by
        change ¬AdmissibleSum (34387 : ZMod 3) 384
        unfold AdmissibleSum
        decide +kernel
      exact fails (hits 0)

end PrimeFactors.PairwiseSumObstruction
