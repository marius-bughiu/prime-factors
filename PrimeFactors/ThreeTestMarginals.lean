import Mathlib.Data.List.Count
import Mathlib.Tactic

/-! The exact possible three-way overlap when the size of a finite window
and all singleton and pair counts are known. Rows are arbitrary Boolean
test outcomes. Attainability does not require independence. -/

namespace PrimeFactors.ThreeTestMarginals

abbrev Row := Bool × Bool × Bool

@[ext] structure Margins where
  width : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  ab : ℕ
  ac : ℕ
  bc : ℕ
  deriving DecidableEq

noncomputable def observe (rows : List Row) : Margins :=
  ⟨rows.length, rows.countP (·.1), rows.countP (·.2.1), rows.countP (·.2.2),
   rows.countP (fun x => x.1 && x.2.1), rows.countP (fun x => x.1 && x.2.2),
   rows.countP (fun x => x.2.1 && x.2.2)⟩

noncomputable def triple (rows : List Row) : ℕ := rows.countP (fun x => x.1 && x.2.1 && x.2.2)

/-- Some finite window has exactly the supplied seven margins and triple count. -/
def Attainable (m : Margins) (t : ℕ) : Prop :=
  ∃ rows : List Row, observe rows = m ∧ triple rows = t

/-- Signed subtraction also detects inconsistent input margins. -/
def lower (m : Margins) : ℤ := max 0 (max ((m.ab:ℤ)+m.ac-m.a)
  (max ((m.ab:ℤ)+m.bc-m.b) ((m.ac:ℤ)+m.bc-m.c)))

def upper (m : Margins) : ℤ := min (m.ab:ℤ) (min (m.ac:ℤ)
  (min (m.bc:ℤ) ((m.width:ℤ)+m.ab+m.ac+m.bc-m.a-m.b-m.c)))

/-- Seven nontrivial cell nonnegativity conditions. The eighth count is the
natural number `t` itself. -/
private def cellsNonnegative (m : Margins) (t : ℕ) : Prop :=
  m.ab+m.ac ≤ m.a+t ∧ m.ab+m.bc ≤ m.b+t ∧ m.ac+m.bc ≤ m.c+t ∧
  t ≤ m.ab ∧ t ≤ m.ac ∧ t ≤ m.bc ∧ m.a+m.b+m.c+t ≤ m.width+m.ab+m.ac+m.bc

private theorem cells_iff (m : Margins) (t : ℕ) :
    cellsNonnegative m t ↔ lower m ≤ t ∧ (t:ℤ) ≤ upper m := by
  simp only [cellsNonnegative, lower, upper, max_le_iff, le_min_iff]
  omega

private theorem observed_cells (rows : List Row) :
    cellsNonnegative (observe rows) (triple rows) := by
  induction rows with
  | nil => simp [cellsNonnegative, observe, triple]
  | cons row rows ih =>
    obtain ⟨a, b, c⟩ := row
    simp only [cellsNonnegative, observe, triple] at ih ⊢
    cases a <;> cases b <;> cases c <;> simp [List.countP_cons] <;> omega

/-- Every actual window obeys both endpoints. -/
theorem bounds (rows : List Row) :
    lower (observe rows) ≤ triple rows ∧ (triple rows : ℤ) ≤ upper (observe rows) :=
  (cells_iff ..).mp (observed_cells rows)

private def blocks (n000 n001 n010 n011 n100 n101 n110 n111 : ℕ) : List Row :=
  List.replicate n000 (false,false,false) ++ List.replicate n001 (false,false,true) ++
  List.replicate n010 (false,true,false) ++ List.replicate n011 (false,true,true) ++
  List.replicate n100 (true,false,false) ++ List.replicate n101 (true,false,true) ++
  List.replicate n110 (true,true,false) ++ List.replicate n111 (true,true,true)

/-- An explicit list realizing any proposed nonnegative collection of cells. -/
private theorem realize {m : Margins} {t : ℕ} (h : cellsNonnegative m t) : Attainable m t := by
  rcases m with ⟨w,a,b,c,ab,ac,bc⟩
  let rows := blocks (w+ab+ac+bc-(a+b+c+t)) (c+t-(ac+bc)) (b+t-(ab+bc))
    (bc-t) (a+t-(ab+ac)) (ac-t) (ab-t) t
  simp only [cellsNonnegative] at h
  refine ⟨rows, ?_, ?_⟩
  · apply Margins.ext <;> simp [rows, blocks, observe, List.countP_replicate] <;> omega
  · simp [rows, blocks, triple, List.countP_replicate]

/-- The endpoints describe the full integer interval, including both endpoints.
For inconsistent margins the signed interval contains no natural number. -/
theorem attainable_iff (m : Margins) (t : ℕ) :
    Attainable m t ↔ lower m ≤ t ∧ (t:ℤ) ≤ upper m := by
  constructor
  · rintro ⟨rows,rfl,rfl⟩
    exact bounds rows
  · exact fun h => realize ((cells_iff ..).mpr h)

theorem lower_nonneg (m : Margins) : 0 ≤ lower m := le_max_left _ _

/-- Feasibility requires no additional parity condition. -/
theorem consistent_iff (m : Margins) :
    (∃ t, Attainable m t) ↔ lower m ≤ upper m := by
  constructor
  · rintro ⟨t,ht⟩
    exact ((attainable_iff ..).mp ht).1.trans ((attainable_iff ..).mp ht).2
  · intro fit
    have h := Int.toNat_of_nonneg (lower_nonneg m)
    exact ⟨(lower m).toNat, (attainable_iff ..).mpr (by omega)⟩

/-- For consistent counts, they force an empty intersection exactly at upper endpoint zero. -/
theorem force_empty_iff (m : Margins) (fit : lower m ≤ upper m) :
    (∀ t, Attainable m t → t = 0) ↔ upper m = 0 := by
  have un := (lower_nonneg m).trans fit
  have h := Int.toNat_of_nonneg un
  constructor
  · intro all
    have att : Attainable m (upper m).toNat := (attainable_iff ..).mpr (by omega)
    have := all _ att
    omega
  · intro eq t ht
    have := (attainable_iff ..).mp ht
    omega

/-- For consistent counts, they force a common passing row exactly at positive lower endpoint. -/
theorem force_nonempty_iff (m : Margins) (fit : lower m ≤ upper m) :
    (∀ t, Attainable m t → 0 < t) ↔ 0 < lower m := by
  have h := Int.toNat_of_nonneg (lower_nonneg m)
  constructor
  · intro all
    have att : Attainable m (lower m).toNat := (attainable_iff ..).mpr (by omega)
    have := all _ att
    omega
  · intro pos t ht
    have := (attainable_iff ..).mp ht
    omega

end PrimeFactors.ThreeTestMarginals
