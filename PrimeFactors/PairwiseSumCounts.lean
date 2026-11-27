import PrimeFactors.Certificate
import PrimeFactors.PairwiseSumObstruction

/-! Two balanced semiprimes have identical local sum tables at 3, 13 and 11.
Their first four possible sums give equal counts for every one- and two-prime
test, but different counts for all three. -/

namespace PrimeFactors.PairwiseSumCounts

open PairwiseSumObstruction (modulus)
open OppositeSquareScaleBands (InSumWindow)

/-- Both products are 665 modulo 4·3·13·11. Their starts differ by 660,
which preserves the alignment at 4, 3 and 11 and shifts it at 13. -/
theorem controls :
    ExactFactorization 10961 [97, 113] ∧ 97 < 113 ∧ 113 < 2*97 ∧
    ExactFactorization 187709 [337, 557] ∧ 337 < 557 ∧ 557 < 2*337 ∧
    10961 % (4*3*13*11) = 665 ∧ 187709 % (4*3*13*11) = 665 ∧
    (870-210) % (4*3*11) = 0 ∧ (870-210) % 13 = 10 := by
  norm_num [ExactFactorization]

/-- The full local factor-sum table is the same at each prime for any
fixed integer sum. -/
theorem same_local_tables (i : Fin 3) (s : ℕ) :
    AdmissibleSum (10961 : ZMod (modulus i)) (s : ZMod (modulus i)) ↔
    AdmissibleSum (187709 : ZMod (modulus i)) (s : ZMod (modulus i)) := by
  have h : (10961 : ZMod (modulus i)) = 187709 := by
    fin_cases i <;> dsimp [modulus] <;> decide +kernel
  rw [h]

/-- Sums in the public balanced interval, compatible modulo four, up to
the end of the four-position prefix beginning at a proposed start. -/
def inPrefix (n start s : ℕ) : Prop :=
  InSumWindow n s ∧ AdmissibleSum (n : ZMod 4) (s : ZMod 4) ∧ s < start + 16

private theorem prefix_positions {n start : ℕ} (phase : n % 4 = 1) (aligned : start % 4 = 2)
    (startPos : 4 ≤ start) (before : (start - 4)^2 ≤ 4*n) (lo : 4*n < start^2)
    (hi : 2*(start+12)^2 ≤ 9*n) (s : ℕ) :
    inPrefix n start s ↔ ∃ j : Fin 4, s = start + 4*j.val := by
  have modN : (n : ZMod 4) = 1 := by
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast] using phase
  have table : ∀ z : ZMod 4, AdmissibleSum 1 z ↔ z.val = 2 := by
    unfold AdmissibleSum
    decide +kernel
  simp only [inPrefix, InSumWindow, modN, table, ZMod.val_natCast]
  constructor
  · rintro ⟨⟨above, _⟩, four, cut⟩
    have h : start - 4 < s := by
      apply Nat.lt_of_not_ge
      intro below
      exact (not_le_of_gt above) ((Nat.pow_le_pow_left below 2).trans before)
    have : s = start ∨ s = start + 4 ∨ s = start + 8 ∨ s = start + 12 := by omega
    rcases this with h | h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  · rintro ⟨j, rfl⟩
    have left := Nat.pow_le_pow_left (show start ≤ start + 4*j.val by omega) 2
    have right := Nat.pow_le_pow_left (show start + 4*j.val ≤ start+12 by omega) 2
    exact ⟨⟨lo.trans_le left, by omega⟩, by omega, by omega⟩

/-- Both inspected blocks begin at their product's actual lower bound
after applying its modulo-four test. -/
theorem public_prefixes (s : ℕ) :
    (inPrefix 10961 210 s ↔ ∃ j : Fin 4, s = 210 + 4*j.val) ∧
    (inPrefix 187709 870 s ↔ ∃ j : Fin 4, s = 870 + 4*j.val) := by
  constructor <;> apply prefix_positions <;> decide

private noncomputable def localDec (n s : ℕ) (i : Fin 3) :
    Decidable (AdmissibleSum (n : ZMod (modulus i)) (s : ZMod (modulus i))) := by
  letI : NeZero (modulus i) := ⟨by fin_cases i <;> decide⟩
  unfold AdmissibleSum
  infer_instance

/-- Positions accepted by the local sum predicate for one prime. -/
noncomputable def positions (n start : ℕ) (i : Fin 3) : Finset (Fin 4) := by
  letI (j : Fin 4) := localDec n (start+4*j.val) i
  exact Finset.univ.filter fun j => AdmissibleSum (n : ZMod (modulus i))
    ((start+4*j.val : ℕ) : ZMod (modulus i))

private def mask (shifted : Bool) (i : Fin 3) : Finset (Fin 4) :=
  match i.val with
  | 0 => {0, 3}
  | 1 => if shifted then {1, 3} else {0, 2}
  | _ => {0, 1}

private theorem tables (i : Fin 3) :
    positions 10961 210 i = mask false i ∧ positions 187709 870 i = mask true i := by
  constructor <;> ext j <;> simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and] <;>
    fin_cases i <;> fin_cases j <;> dsimp [modulus, mask, AdmissibleSum] <;> decide +kernel

/-- Number of positions surviving every test in the selected family. -/
noncomputable def count (rows : Fin 3 → Finset (Fin 4)) (I : Finset (Fin 3)) : ℕ :=
  (Finset.univ.filter fun j => ∀ i ∈ I, j ∈ rows i).card

/-- All singleton counts are two and all pair counts are one in both
prefixes. With all three tests, the first count is one and the second zero. -/
theorem exact_counts (I : Finset (Fin 3)) :
    count (positions 10961 210) I = (if I.card = 0 then 4 else if I.card = 1 then 2 else 1) ∧
    count (positions 187709 870) I =
      (if I.card = 0 then 4 else if I.card = 1 then 2 else if I.card = 2 then 1 else 0) := by
  rw [show positions 10961 210 = mask false from funext fun i => (tables i).1,
    show positions 187709 870 = mask true from funext fun i => (tables i).2]
  revert I
  decide +kernel

/-- Retaining aligned positions distinguishes the examples. The lists for
3 and 11 coincide in order. Only the modulo-13 menu changes position. -/
theorem aligned_positions :
    positions 10961 210 0 = positions 187709 870 0 ∧
    positions 10961 210 2 = positions 187709 870 2 ∧
    positions 10961 210 1 = {0, 2} ∧ positions 187709 870 1 = {1, 3} := by
  simp only [(tables _).1, (tables _).2]
  decide +kernel

end PrimeFactors.PairwiseSumCounts
