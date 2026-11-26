import PrimeFactors.TraceProgression

/-! Linear traversal of a covering schedule whose active rows are listed in
cell order. Any unused rows can be placed after the last active row. -/

namespace PrimeFactors.SequentialTraceCover

open TraceCoverCertificate

/-- The head row pays for the first segment. The existing singleton upper
checker validates both endpoints with the same strict first-omitted threshold. -/
def check (n m : ℕ) (left right : Point) : List (Slope × ℕ) → List Point → Bool
  | row::rows, r::cuts => upperCheck n m [row] left r [(r,0)] &&
      (if cuts.isEmpty then decide (r=right) else check n m r right rows cuts)
  | _, _ => false

/-- Every real ratio from the first cut through the last is covered. -/
theorem real_cover {n m : ℕ} {L R : Point} {rows : List (Slope × ℕ)} {cuts : List Point}
    (ok : check n m L R rows cuts) {x : ℝ} (lo : (L.value:ℝ)≤x) (hi : x≤(R.value:ℝ)) :
    ∃ e∈rows, (n:ℝ)*((e.1.a:ℝ)+e.1.b*x)^2 < (cutoff m e.1 e.2:ℝ)^2*x := by
  induction rows generalizing L cuts with
  | nil => simp [check] at ok
  | cons row rows ih =>
    cases cuts with
    | nil => simp [check] at ok
    | cons r cuts =>
      simp only [check,Bool.and_eq_true] at ok
      by_cases before : x≤(r.value:ℝ)
      · obtain ⟨e,mem,hit⟩ := upper_real ok.1 lo before
        exact ⟨e,List.mem_cons.mpr (Or.inl (List.mem_singleton.mp mem)),hit⟩
      · have more := ok.2
        split at more
        · have eq := of_decide_eq_true more; subst r; exact (before hi).elim
        · obtain ⟨e,mem,hit⟩ := ih more (le_of_not_ge before)
          exact ⟨e,List.mem_cons_of_mem _ mem,hit⟩

/-- The same checked segments certify the integer test on every rational ratio. -/
theorem rational_cover {n m : ℕ} {L R : Point} {rows : List (Slope × ℕ)} {cuts : List Point}
    (ok : check n m L R rows cuts) : CoversRange n m rows L R := by
  intro x xd lo hi
  induction rows generalizing L cuts with
  | nil => simp [check] at ok
  | cons row rows ih =>
    cases cuts with
    | nil => simp [check] at ok
    | cons r cuts =>
      simp only [check,Bool.and_eq_true] at ok
      by_cases cut : before x r
      · obtain ⟨e,mem,hit⟩ := upper_sound xd ok.1 lo cut
        exact ⟨e,List.mem_cons.mpr (Or.inl (List.mem_singleton.mp mem)),hit⟩
      · have more := ok.2
        split at more
        · have eq := of_decide_eq_true more; subst r; exact (cut hi).elim
        · have later : before r x := by
            simp only [before,decide_eq_true_eq] at cut ⊢; omega
          obtain ⟨e,mem,hit⟩ := ih more later
          exact ⟨e,List.mem_cons_of_mem _ mem,hit⟩

/-- A balanced index for a schedule in canonical catalogue order. The stored
split is the first index routed to the right subtree. Membership is sound for
any stored split, and each chosen row still has to pass its endpoint checks. -/
inductive RowTree where
  | leaf (row : Slope × ℕ)
  | split (index : ℕ) (left right : RowTree)

namespace RowTree

def rows : RowTree → List (Slope × ℕ)
  | .leaf e => [e]
  | .split _ l r => l.rows ++ r.rows

def read (tree : RowTree) (i : ℕ) : Slope × ℕ :=
  match tree with
  | .leaf e => e
  | .split j l r => if i<j then l.read i else r.read i

private theorem read_mem (tree : RowTree) (i : ℕ) : tree.read i ∈ tree.rows := by
  induction tree with
  | leaf e => simp [read,rows]
  | split j l r il ir =>
    simp only [read,rows,List.mem_append]; split
    · exact Or.inl il
    · exact Or.inr ir

end RowTree

/-- Price each geometric segment through logarithmic-depth lookup in a balanced
row tree. The entries may stay in the order used by the canonical catalogue. -/
def indexedCheck (n m : ℕ) (L R : Point) (tree : RowTree) : List (Point × ℕ) → Bool
  | [] => false
  | (r,i)::cuts => upperCheck n m [tree.read i] L r [(r,0)] &&
      (if cuts.isEmpty then decide (r=R) else indexedCheck n m r R tree cuts)

private theorem indexed_eq {n m : ℕ} {L R : Point} {tree : RowTree} {cuts : List (Point × ℕ)} :
    indexedCheck n m L R tree cuts =
      check n m L R (cuts.map (fun c => tree.read c.2)) (cuts.map Prod.fst) := by
  induction cuts generalizing L with
  | nil => rfl
  | cons c cuts ih =>
    rcases c with ⟨r,i⟩
    have empty : (cuts.map Prod.fst).isEmpty = cuts.isEmpty := by cases cuts <;> rfl
    simp only [indexedCheck,List.map_cons,check,empty,ih]

private theorem selected {tree : RowTree} {cuts : List (Point × ℕ)} {e : Slope × ℕ}
    (mem : e∈cuts.map (fun c => tree.read c.2)) : e∈tree.rows := by
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp mem
  exact tree.read_mem c.2

theorem indexed_real {n m : ℕ} {L R : Point} {tree : RowTree} {cuts : List (Point × ℕ)}
    (ok : indexedCheck n m L R tree cuts) {x : ℝ} (lo : (L.value:ℝ)≤x) (hi : x≤(R.value:ℝ)) :
    ∃ e∈tree.rows, (n:ℝ)*((e.1.a:ℝ)+e.1.b*x)^2 < (cutoff m e.1 e.2:ℝ)^2*x := by
  rw [indexed_eq] at ok
  obtain ⟨e,mem,hit⟩ := real_cover ok lo hi
  exact ⟨e,selected mem,hit⟩

theorem indexed_rational {n m : ℕ} {L R : Point} {tree : RowTree} {cuts : List (Point × ℕ)}
    (ok : indexedCheck n m L R tree cuts) : CoversRange n m tree.rows L R := by
  intro x xd lo hi
  rw [indexed_eq] at ok
  obtain ⟨e,mem,hit⟩ := rational_cover ok x xd lo hi
  exact ⟨e,selected mem,hit⟩

end PrimeFactors.SequentialTraceCover
