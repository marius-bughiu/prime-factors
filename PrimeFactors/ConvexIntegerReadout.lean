import Mathlib.Tactic

/-! Exact thresholds on integer intervals with a counted comparison budget.
Three such thresholds suffice for a strictly convex sequence, including a
pair of equal neighboring minimum values. -/
namespace PrimeFactors.ConvexIntegerReadout

/-- Search the half-open interval starting at lo with w entries.
Return its first true index (the right endpoint on a miss), and the number
of calls to P. A fuel bound is proved sufficient below. -/
@[nospecialize] def boundary (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ → ℕ → ℕ×ℕ
  | 0, lo, _ => (lo,0)
  | k+1, lo, w =>
    if w=0 then (lo,0) else
      let mid := lo+w/2
      let child := if P mid then boundary P k lo (w/2)
        else boundary P k (mid+1) (w-w/2-1)
      (child.1,child.2+1)

def IsCut (P : ℕ → Prop) (lo hi cut : ℕ) : Prop :=
  lo ≤ cut ∧ cut ≤ hi ∧
    (∀ i : ℕ, lo ≤ i → i < cut → ¬ P i) ∧ (∀ i : ℕ, cut ≤ i → i < hi → P i)

theorem boundary_spec (P : ℕ→Prop) [DecidablePred P] (k lo w : ℕ) (budget : w < 2^k)
    (up : ∀ i j : ℕ, lo ≤ i → i ≤ j → j < lo+w → P i → P j) :
    IsCut P lo (lo+w) (boundary P k lo w).1 ∧ (boundary P k lo w).2 ≤ k := by
  induction k generalizing lo w with
  | zero =>
    have empty : w=0 := by simpa using budget
    subst w
    simp [IsCut,boundary]
    constructor <;> intro i h₁ h₂ <;> omega
  | succ k ih =>
    by_cases empty : w=0
    · subst w
      simp [IsCut,boundary]
      constructor <;> intro i h₁ h₂ <;> omega
    have size := budget
    rw [pow_succ] at size
    have left : w/2 < 2^k := by omega
    have right : w-w/2-1 < 2^k := by omega
    have middle : lo+w/2 < lo+w := by omega
    by_cases yes : P (lo+w/2)
    · simp only [boundary,if_neg empty,if_pos yes]
      obtain ⟨⟨low,high,pre,post⟩,cost⟩ := ih lo (w/2) left
        (fun i j hi le hj => up i j hi le (by omega))
      refine ⟨⟨low,high.trans middle.le,pre,?_⟩,Nat.succ_le_succ cost⟩
      intro i lower_i below
      by_cases h : i < lo+w/2
      · exact post i lower_i h
      · exact up _ i (by omega) (by omega) below yes
    · simp only [boundary,if_neg empty,if_neg yes]
      have end_eq : lo+w/2+1+(w-w/2-1)=lo+w := by omega
      obtain ⟨⟨low,high,pre,post⟩,cost⟩ := ih (lo+w/2+1) (w-w/2-1) right
        (fun i j hi le hj => up i j (by omega) le (by omega))
      rw [end_eq] at high post
      refine ⟨⟨(by omega),high,?_,post⟩,Nat.succ_le_succ cost⟩
      intro i lower_i below
      by_cases h : i ≤ lo+w/2
      · exact fun pi => yes (up i _ lower_i h middle pi)
      · exact pre i (by omega) below

/-- Returned boundary indices can be sentinels. The count includes each
threshold comparison in all three searches. -/
structure Reading where
  left : ℕ
  right : ℕ
  comparisons : ℕ

/-- Split after the first index with a nonnegative outgoing slope. Search for
the level on the two disjoint remaining intervals. -/
def read (f : ℕ→ℚ) (H : ℚ) (k lo hi : ℕ) : Reading :=
  let turn := boundary (fun i => f i ≤ f (i+1)) k lo (hi-lo)
  let left := boundary (fun i => f i ≤ H) k lo (turn.1+1-lo)
  let right := boundary (fun i => H ≤ f i) k (turn.1+1) (hi-turn.1)
  ⟨left.1, right.1, turn.2+left.2+right.2⟩

/-- The recursion uses at most one comparison per unit of fuel,
even when the predicate is arbitrary or the input interval is too wide. -/
theorem boundary_cost (P : ℕ→Prop) [DecidablePred P] (k lo w : ℕ) :
    (boundary P k lo w).2 ≤ k := by
  induction k generalizing lo w with
  | zero => simp [boundary]
  | succ k ih =>
    by_cases empty : w=0
    · simp [boundary, empty]
    · by_cases yes : P (lo+w/2)
      · simpa only [boundary, if_neg empty, if_pos yes] using
          Nat.succ_le_succ (ih lo (w/2))
      · simpa only [boundary, if_neg empty, if_neg yes] using
          Nat.succ_le_succ (ih (lo+w/2+1) (w-w/2-1))

/-- Three searches have a fixed comparison ceiling even on an interval
where there is no solution or the slope hypothesis fails. -/
theorem read_cost (f : ℕ→ℚ) (H : ℚ) (k lo hi : ℕ) :
    (read f H k lo hi).comparisons ≤ 3*k := by
  let m := (boundary (fun i => f i ≤ f (i+1)) k lo (hi-lo)).1
  have a := boundary_cost (fun i => f i ≤ f (i+1)) k lo (hi-lo)
  have b := boundary_cost (fun i => f i≤H) k lo (m+1-lo)
  have c := boundary_cost (fun i => H≤f i) k (m+1) (hi-m)
  unfold read
  dsimp only
  dsimp only [m] at b c
  omega

private theorem at_first {P : ℕ→Prop} {lo hi c j : ℕ} (cut : IsCut P lo hi c)
    (lower : lo ≤ j) (upper : j < hi) (hit : P j)
    (before : ∀ i, lo ≤ i → i < j → ¬P i) : j=c := by
  obtain ⟨base,_,no,yes⟩ := cut
  rcases lt_trichotomy j c with h|h|h
  · exact False.elim (no j lower h hit)
  · exact h
  · exact False.elim (before c base h (yes c le_rfl (h.trans upper)))

/-- Every solution on the inclusive interval occurs at one of the two returned
indices. This includes both solutions at a pair of tied neighboring minima.
The budget counts comparisons of slopes or levels against their thresholds. -/
theorem read_spec (f : ℕ→ℚ) (H : ℚ) (k lo hi : ℕ)
    (ordered : lo ≤ hi) (budget : hi-lo+1 < 2^k)
    (convex : ∀ j, lo ≤ j → j+1 < hi → f (j+1)-f j < f (j+2)-f (j+1)) :
    (read f H k lo hi).comparisons ≤ 3*k ∧
    ∀ j, lo ≤ j → j ≤ hi → f j=H →
      j=(read f H k lo hi).left ∨ j=(read f H k lo hi).right := by
  let slope := fun i => f (i+1)-f i
  let turn := boundary (fun i => f i ≤ f (i+1)) k lo (hi-lo)
  let m := turn.1
  let left := boundary (fun i => f i ≤ H) k lo (m+1-lo)
  let right := boundary (fun i => H ≤ f i) k (m+1) (hi-m)
  change turn.2+left.2+right.2 ≤ 3*k ∧
    ∀ j, lo ≤ j → j ≤ hi → f j=H → j=left.1 ∨ j=right.1
  have slopes : StrictMonoOn slope (Set.Ico lo hi) := by
    apply strictMonoOn_of_lt_add_one Set.ordConnected_Ico
    intro i _ hin next
    exact convex i hin.1 next.2
  have edge : lo+(hi-lo)=hi := by omega
  have turn_spec := boundary_spec (fun i => f i ≤ f (i+1)) k lo (hi-lo) (by omega)
    (by
      intro i j lower step upper hit
      exact sub_nonneg.mp ((sub_nonneg.mpr hit).trans
        (slopes.monotoneOn ⟨lower,by omega⟩ ⟨by omega,by omega⟩ step)))
  change IsCut (fun i => f i ≤ f (i+1)) lo (lo+(hi-lo)) m ∧ turn.2 ≤ k at turn_spec
  rw [edge] at turn_spec
  obtain ⟨⟨lm,mh,neg,nonneg⟩,_⟩ := turn_spec
  have down : StrictAntiOn f (Set.Icc lo m) := by
    apply strictAntiOn_of_add_one_lt Set.ordConnected_Icc
    intro i _ hin next
    have h := lt_of_not_ge (neg i hin.1 (by have := next.2; omega))
    exact h
  have up : StrictMonoOn f (Set.Icc (m+1) hi) := by
    apply strictMonoOn_of_lt_add_one Set.ordConnected_Icc
    intro i _ hin next
    have low : m < i := hin.1
    have high : i < hi := next.2
    have sm := nonneg m le_rfl (low.trans high)
    have si := slopes ⟨lm,low.trans high⟩ ⟨lm.trans low.le,high⟩ low
    exact sub_pos.mp ((sub_nonneg.mpr sm).trans_lt si)
  have left_edge : lo+(m+1-lo)=m+1 := by omega
  have right_edge : m+1+(hi-m)=hi+1 := by omega
  have left_spec := boundary_spec (fun i => f i ≤ H) k lo (m+1-lo) (by omega)
    (by
      intro i j lower step upper hit
      exact (down.antitoneOn ⟨lower,by omega⟩ ⟨by omega,by omega⟩ step).trans hit)
  have right_spec := boundary_spec (fun i => H ≤ f i) k (m+1) (hi-m) (by omega)
    (by
      intro i j lower step upper hit
      exact hit.trans (up.monotoneOn ⟨lower,by omega⟩ ⟨by omega,by omega⟩ step))
  change IsCut (fun i => f i ≤ H) lo (lo+(m+1-lo)) left.1 ∧ left.2 ≤ k at left_spec
  change IsCut (fun i => H ≤ f i) (m+1) (m+1+(hi-m)) right.1 ∧ right.2 ≤ k at right_spec
  rw [left_edge] at left_spec
  rw [right_edge] at right_spec
  obtain ⟨lc,_⟩ := left_spec
  obtain ⟨rc,_⟩ := right_spec
  refine ⟨read_cost f H k lo hi, ?_⟩
  intro j lower upper hit
  by_cases leftside : j ≤ m
  · left
    apply at_first lc lower (by omega) hit.le
    intro i low lt
    have less := down ⟨low,lt.le.trans leftside⟩ ⟨lower,leftside⟩ lt
    exact not_le_of_gt (hit ▸ less)
  · right
    have low : m+1 ≤ j := by omega
    apply at_first rc low (by omega) hit.ge
    intro i ilo lt
    have less := up ⟨ilo,lt.le.trans upper⟩ ⟨low,upper⟩ lt
    exact not_le_of_gt (hit ▸ less)

/-- Both neighboring minima are retained, including when the first slope
comparison finds their common value. -/
theorem tied_minima :
    let r := read (fun i => ((i:ℚ)-2)*((i:ℚ)-3)) 0 3 0 5
    r.left=2 ∧ r.right=3 ∧ r.comparisons=6 := by norm_num [read, boundary]

end PrimeFactors.ConvexIntegerReadout
