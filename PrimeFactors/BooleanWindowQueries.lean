import PrimeFactors.BooleanMarginalAmbiguity
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Sublists
import Mathlib.Data.Finset.Option

/-! A window of w named positions and k previously located Boolean tests.
Knowing their failures at each position partitions the window into cells.
The only queries charged below are evaluations of a final test. -/

namespace PrimeFactors.BooleanWindowQueries

open Finset Function
open BooleanMarginalAmbiguity (SameFaces cell_difference)

variable {k w : ℕ}

/-- The supplied aligned failures of the first k tests determine this set. -/
noncomputable def cell (known : Fin w → Finset (Fin k)) (s : Finset (Fin k)) :=
  univ.filter fun j => known j = s

/-- Read the final test only at the positions in one cell. -/
noncomputable def hits (known : Fin w → Finset (Fin k)) (last : Fin w → Bool)
    (s : Finset (Fin k)) := ((cell known s).filter fun j => last j).card

theorem sum_sizes (known : Fin w → Finset (Fin k)) :
    ∑ s, (cell known s).card = w := by
  simpa [cell] using sum_card_fiberwise_eq_card_filter
    (univ : Finset (Fin w)) (univ : Finset (Finset (Fin k))) known

/-- An explicit list of every possible set of failures, including empty cells. -/
private def masks (k : ℕ) : List (Finset (Fin k)) :=
  (List.finRange k).sublists.map List.toFinset

private theorem mem_masks (s : Finset (Fin k)) : s ∈ masks k := by
  apply List.mem_map.mpr
  refine ⟨(List.finRange k).filter (· ∈ s), List.mem_sublists.mpr List.filter_sublist, ?_⟩
  ext
  simp

/-- Pick a least populated cell from the aligned tests before reading the final test. -/
noncomputable def smallest (known : Fin w → Finset (Fin k)) : Finset (Fin k) :=
  ((masks k).argmin (fun s => (cell known s).card)).getD ∅

theorem smallest_le (known : Fin w → Finset (Fin k)) (s : Finset (Fin k)) :
    (cell known (smallest known)).card ≤ (cell known s).card := by
  unfold smallest
  cases h : (masks k).argmin (fun s => (cell known s).card) with
  | none =>
    have empty := List.argmin_eq_none.mp h
    simpa [empty] using mem_masks s
  | some u =>
    exact List.le_of_mem_argmin (f := fun t => (cell known t).card) (m := u) (mem_masks s) h

theorem query_bound (known : Fin w → Finset (Fin k)) :
    (cell known (smallest known)).card ≤ w / 2^k := by
  apply (Nat.le_div_iff_mul_le (by positivity)).mpr
  have le := Finset.sum_le_sum (s := (univ : Finset (Finset (Fin k))))
    (fun s _ => smallest_le known s)
  rw [sum_sizes] at le
  simpa [Fintype.card_finset, Nat.mul_comm] using le

/-- The faces needed for reconstruction count final passes in two adjacent
old cells. Each such total leaves one old test unspecified. -/
def SuppliesFaces (known : Fin w → Finset (Fin k)) (last : Fin w → Bool)
    (faces : Finset (Fin k) → Fin k → ℕ) : Prop :=
  ∀ s i, i ∉ s → faces s i = hits known last s + hits known last (insert i s)

/-- Remove failures one at a time by subtracting the known cell from a supplied face. -/
def readback {α : Type*} [DecidableEq α] (faces : Finset α → α → ℕ) : List α → ℕ → ℕ
  | [], value => value
  | i :: rest, value => readback faces rest (faces rest.toFinset i - value)

private theorem readback_hits {known : Fin w → Finset (Fin k)} {last : Fin w → Bool}
    {faces : Finset (Fin k) → Fin k → ℕ} (supplied : SuppliesFaces known last faces)
    (path : List (Fin k)) (unique : path.Nodup) :
    readback faces path (hits known last path.toFinset) = hits known last ∅ := by
  induction path with
  | nil => rfl
  | cons i rest ih =>
    obtain ⟨fresh, distinct⟩ := List.nodup_cons.mp unique
    rw [readback, supplied _ _ (by simpa using fresh), List.toFinset_cons, Nat.add_sub_cancel]
    exact ih distinct

/-- Return the number of common passes using the final-test values on the selected cell.
The path uses one supplied face per failed old test in that cell. -/
theorem recover_count (known : Fin w → Finset (Fin k)) (last : Fin w → Bool)
    (faces : Finset (Fin k) → Fin k → ℕ) (supplied : SuppliesFaces known last faces) :
    readback faces ((smallest known).sort (· ≤ ·)) (hits known last (smallest known)) =
      hits known last ∅ := by
  simpa using readback_hits supplied _ ((smallest known).sort_nodup (· ≤ ·))

/-- For four positions and two located tests, deciding the three-way count
requires at most one additional final-test evaluation. -/
theorem four_positions (known : Fin 4 → Finset (Fin 2)) :
    (cell known (smallest known)).card ≤ 1 := query_bound known

/-- Full failure counts. The label none is the final test and some i denotes old test i. -/
noncomputable def table (known : Fin w → Finset (Fin k)) (last : Fin w → Bool)
    (s : Finset (Option (Fin k))) :=
  (univ.filter fun j => (if last j then (known j).map Embedding.some
    else insert none ((known j).map Embedding.some)) = s).card

private theorem table_pass (known : Fin w → Finset (Fin k)) (last : Fin w → Bool)
    (s : Finset (Fin k)) : table known last (s.map Embedding.some) = hits known last s := by
  unfold table hits
  congr 1
  ext j
  cases h : last j with
  | true => simp [h, cell]
  | false =>
    have diff : insert none ((known j).map Embedding.some) ≠ s.map Embedding.some := by
      intro eq
      have : none ∈ s.map Embedding.some := eq ▸ mem_insert_self ..
      simp at this
    simp [h, cell, diff]

/-- A supplied full collection of proper face counts contains the particular
faces requested by the reconstruction. -/
theorem supplied_by_full_faces (known : Fin w → Finset (Fin k)) (last : Fin w → Bool)
    (faces : Finset (Option (Fin k)) → Option (Fin k) → ℕ)
    (correct : ∀ s i, i ∉ s → faces s i = table known last s + table known last (insert i s)) :
    SuppliesFaces known last (fun s i => faces (s.map Embedding.some) (some i)) := by
  intro s i hi
  have lifted : some i ∉ s.map Embedding.some := by simpa using hi
  change faces _ _ = _
  rw [correct _ _ lifted, table_pass, ← table_pass known last (insert i s), Finset.map_insert]
  rfl

/-- The abstract parity identity shows why any measured cell suffices, including an empty cell. -/
theorem count_agrees_of_cell {known : Fin w → Finset (Fin k)} {a b : Fin w → Bool}
    (same : SameFaces (table known a) (table known b)) {s : Finset (Fin k)}
    (observed : hits known a s = hits known b s) : hits known a ∅ = hits known b ∅ := by
  have h := congrArg abs (cell_difference same (s.map Embedding.some))
  have empty (last : Fin w → Bool) : table known last ∅ = hits known last ∅ := by
    simpa using table_pass known last ∅
  simp only [table_pass, observed, sub_self, abs_zero, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, empty, eq_comm (a := (0 : ℤ)), abs_eq_zero, sub_eq_zero] at h
  exact_mod_cast h

/-- Ambiguity between two compatible completions requires every old cell to contain
at least one position. With four positions split four ways, every cell is a singleton.
Thus reading the unique all-old-pass row also locates the winner if it passes. -/
theorem four_ambiguous_cells {known : Fin 4 → Finset (Fin 2)} {a b : Fin 4 → Bool}
    (same : SameFaces (table known a) (table known b))
    (different : hits known a ∅ ≠ hits known b ∅) (s : Finset (Fin 2)) :
    (cell known s).card = 1 := by
  have pos (t : Finset (Fin 2)) : 1 ≤ (cell known t).card := by
    by_contra! zero
    have empty := Finset.card_eq_zero.mp (show (cell known t).card = 0 by omega)
    exact different (count_agrees_of_cell same (s := t) (by simp [hits, empty]))
  by_contra ne
  have lt : 1 < (cell known s).card := lt_of_le_of_ne (pos s) (Ne.symm ne)
  have strict := Finset.sum_lt_sum (s := (univ : Finset (Finset (Fin 2))))
    (fun t _ => pos t) ⟨s, mem_univ _, lt⟩
  simp [sum_sizes, Fintype.card_finset] at strict

/-- The aligned old tests specify the one index to read in the ambiguous
four-row case. Its final-test bit determines the entire set of common passes. -/
theorem locate_four {known : Fin 4 → Finset (Fin 2)} {a b : Fin 4 → Bool}
    (same : SameFaces (table known a) (table known b))
    (different : hits known a ∅ ≠ hits known b ∅) :
    ∃ j, cell known ∅ = {j} ∧ ∀ last : Fin 4 → Bool,
      (cell known ∅).filter (fun t => last t) = if last j then {j} else ∅ := by
  obtain ⟨j, hj⟩ := card_eq_one.mp (four_ambiguous_cells same different ∅)
  refine ⟨j, hj, fun last => ?_⟩
  cases h : last j <;> ext t <;> by_cases eq : t = j <;> simp [hj, h, eq]

/-- A known count of one can leave its location undetermined. Both old tests
pass everywhere. The two completions have identical full tables and no queries
are needed on the smallest cell, but their sole common pass changes position. -/
theorem one_count_two_locations :
    let known : Fin 4 → Finset (Fin 2) := fun _ => ∅
    let a : Fin 4 → Bool := fun j => decide (j = 0)
    let b : Fin 4 → Bool := fun j => decide (j = 1)
    (∀ s, table known a s = table known b s) ∧
    hits known a ∅ = 1 ∧ hits known b ∅ = 1 ∧
    (cell known (smallest known)).card = 0 ∧
    ((cell known ∅).filter (fun j => a j)) = {0} ∧
    ((cell known ∅).filter (fun j => b j)) = {1} := by
  decide +kernel

end PrimeFactors.BooleanWindowQueries
