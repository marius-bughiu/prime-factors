import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import PrimeFactors.CountingReadout

namespace PrimeFactors

/-- Across the two whole group inputs, a prescribed product has one accepting column per row. -/
noncomputable def groupProductIndicator {G K : Type*} [Group G] [DecidableEq G] [Field K]
    (target : G) : Matrix G G K :=
  fun x y => if x * y = target then 1 else 0

/-- Permuting rows of the identity by `x ↦ x⁻¹ * target` gives the indicator,
including for a noncommutative input group. -/
theorem rank_groupProductIndicator {G K : Type*} [Group G] [DecidableEq G] [Fintype G]
    [Field K] (target : G) :
    (groupProductIndicator (K := K) target).rank = Fintype.card G := by
  let partner : G ≃ G :=
    { toFun := fun x => x⁻¹ * target
      invFun := fun y => target * y⁻¹
      left_inv := by intro x; simp
      right_inv := by intro y; simp }
  have partner_iff (x y : G) : x * y = target ↔ partner x = y := by
    change x * y = target ↔ x⁻¹ * target = y
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  have matrix_eq : groupProductIndicator (K := K) target =
      (1 : Matrix G G K).submatrix partner (Equiv.refl G) := by
    ext x y
    simp [groupProductIndicator, Matrix.submatrix, Matrix.one_apply, partner_iff]
  rw [matrix_eq, Matrix.rank_submatrix, Matrix.rank_one]

/-- A sum of `r` products of a row function and a column function factors through
a matrix with only `r` columns. This lower bound also applies after restricting inputs. -/
theorem matrix_rank_le_separable_length {I J K : Type*} [Fintype I] [Fintype J] [Field K]
    (A : Matrix I J K) (r : ℕ) (row : I → Fin r → K) (col : Fin r → J → K)
    (rep : ∀ x y, A x y = ∑ a, row x a * col a y) : A.rank ≤ r := by
  let U : Matrix I (Fin r) K := row
  let V : Matrix (Fin r) J K := col
  have factor : A = U * V := Matrix.ext rep
  rw [factor]
  simpa using (Matrix.rank_mul_le_left U V).trans U.rank_le_card_width

/-- Low `k+1` bits of an integer product, with both inputs restricted to odd residues. -/
noncomputable def lowProductIndicator (k n : ℕ) :
    Matrix (ZMod (2 ^ (k + 1)))ˣ (ZMod (2 ^ (k + 1)))ˣ (ZMod 3) :=
  fun x y => if (x : ZMod (2 ^ (k + 1))) * (y : ZMod (2 ^ (k + 1))) = n then 1 else 0

/-- Every odd target gives full rank on the odd residue classes, exactly half the modulus. -/
theorem rank_lowProductIndicator (k n : ℕ) (hn : Odd n) :
    (lowProductIndicator k n).rank = 2 ^ k := by
  let u := ZMod.unitOfCoprime n (hn.coprime_two_right.pow_right (k + 1))
  have asGroup : lowProductIndicator k n = groupProductIndicator (K := ZMod 3) u := by
    ext x y
    have h (x y : (ZMod (2 ^ (k + 1)))ˣ) :
        x * y = u ↔ (x : ZMod (2 ^ (k + 1))) * (y : ZMod (2 ^ (k + 1))) = n := by
      simpa [u] using (Units.ext_iff (a₁ := x * y) (a₂ := u))
    simp [lowProductIndicator, groupProductIndicator, h]
  rw [asGroup, rank_groupProductIndicator, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ Nat.prime_two]
  simp

/-- Any exact separated representation of the low-bit indicator over the three-element
field needs at least one term per odd residue in the chosen input cut. -/
theorem lowProduct_separable_length (k n r : ℕ) (hn : Odd n)
    (row : (ZMod (2 ^ (k + 1)))ˣ → Fin r → ZMod 3)
    (col : Fin r → (ZMod (2 ^ (k + 1)))ˣ → ZMod 3)
    (rep : ∀ x y, lowProductIndicator k n x y = ∑ a, row x a * col a y) :
    2 ^ k ≤ r := by
  rw [← rank_lowProductIndicator k n hn]
  exact matrix_rank_le_separable_length _ r row col rep

/-- A representation valid on all residue pairs must also work on the odd submatrix. -/
theorem lowProduct_all_residues_separable_length (k n r : ℕ) (hn : Odd n)
    (row : ZMod (2 ^ (k + 1)) → Fin r → ZMod 3)
    (col : Fin r → ZMod (2 ^ (k + 1)) → ZMod 3)
    (rep : ∀ x y, (if x * y = (n : ZMod (2 ^ (k + 1))) then 1 else 0 : ZMod 3) =
      ∑ a, row x a * col a y) : 2 ^ k ≤ r :=
  lowProduct_separable_length k n r hn (fun x => row x.val) (fun a y => col a y.val)
    (fun x y => rep x.val y.val)

/-- Exact natural multiplication on the full square of side `B`. -/
noncomputable def exactBoxIndicator (n B : ℕ) : Matrix (Fin B) (Fin B) (ZMod 3) :=
  fun x y => if x.val * y.val = n then 1 else 0

/-- When the box contains both prime factors and excludes the two trivial orientations,
the exact product equation has rank two on the same whole-input cut. -/
theorem rank_exactBoxIndicator_semiprime {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p < q) (inside : q < B) (upper : B ≤ p * q) :
    (exactBoxIndicator (p * q) B).rank = 2 := by
  have box := acceptedBox_semiprime hp hq ordered inside upper
  have valid (x y : Fin B) :
      x.val * y.val = p * q ↔ (x.val = p ∧ y.val = q) ∨ (x.val = q ∧ y.val = p) := by
    have memb := Finset.ext_iff.mp box (x.val, y.val)
    simpa [acceptedBox, x.isLt, y.isLt] using memb
  apply le_antisymm
  · apply matrix_rank_le_separable_length _ 2
      (fun (x : Fin B) (i : Fin 2) => if x.val = (if i = 0 then p else q) then 1 else 0)
      (fun (i : Fin 2) (y : Fin B) => if y.val = (if i = 0 then q else p) then 1 else 0)
    intro x y
    simp only [exactBoxIndicator, valid, Fin.sum_univ_two, show (1 : Fin 2) ≠ 0 by decide,
      if_false, if_true]
    clear valid box
    split_ifs <;> simp_all [ordered.ne, Ne.symm ordered.ne]
  · let small : Fin B := ⟨p, ordered.trans inside⟩
    let large : Fin B := ⟨q, inside⟩
    let row (i : Fin 2) := if i = 0 then small else large
    let col (i : Fin 2) := if i = 0 then large else small
    have minor : (exactBoxIndicator (p * q) B).submatrix row col =
        (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.submatrix, Matrix.one_apply, exactBoxIndicator, valid,
          row, col, small, large, ordered.ne, Ne.symm ordered.ne]
    have h := (exactBoxIndicator (p * q) B).cRank_submatrix_le row col
    have finiteRank := (exactBoxIndicator (p * q) B).cRank_le_card_width.trans_lt
      (Cardinal.nat_lt_aleph0 _)
    simpa [minor, Matrix.cRank_toNat_eq_rank] using Cardinal.toNat_le_toNat h finiteRank

end PrimeFactors
