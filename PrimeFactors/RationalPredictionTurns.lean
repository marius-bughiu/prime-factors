import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Topology
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! A rational function has finitely many monotone intervals. Poles and
critical points get separate labels, so an integer lying at a pole belongs to
no piece. No bound on the coefficients or on denominator values is needed. -/

namespace PrimeFactors.RationalPredictionTurns

open Finset Polynomial Set
open scoped Classical

private noncomputable def slope (A B : ℝ[X]) := A.derivative * B - A * B.derivative

private noncomputable def cuts (A B : ℝ[X]) :=
  B.roots.toFinset ∪ (slope A B).roots.toFinset

/-- Total number of available interval labels, including singleton labels
for roots and possibly empty intervals. -/
noncomputable def budget (A B : ℝ[X]) : ℕ := 2*(A.natDegree+2*B.natDegree)+1

theorem budget_le {A B : ℝ[X]} {d : ℕ} (ha : A.natDegree ≤ d) (hb : B.natDegree ≤ d) :
    budget A B ≤ 6*d+1 := by unfold budget; omega

private theorem count_cuts (A B : ℝ[X]) : (cuts A B).card ≤ A.natDegree+2*B.natDegree := by
  have left := (Multiset.toFinset_card_le B.roots).trans B.card_roots'
  have right := (Multiset.toFinset_card_le (slope A B).roots).trans (slope A B).card_roots'
  have diff := Polynomial.natDegree_sub_le (A.derivative*B) (A*B.derivative)
  have first := Polynomial.natDegree_mul_le (p:=A.derivative) (q:=B)
  have second := Polynomial.natDegree_mul_le (p:=A) (q:=B.derivative)
  have u := Finset.card_union_le B.roots.toFinset (slope A B).roots.toFinset
  dsimp only [cuts,slope] at *
  have da := Polynomial.natDegree_derivative_le A
  have db := Polynomial.natDegree_derivative_le B
  omega

private noncomputable def position (c x : ℝ) : ℕ :=
  if x<c then 0 else if x=c then 1 else 2

private theorem position_mono (c : ℝ) : Monotone (position c) := by
  intro x y xy
  by_cases lt : x<c
  · simp [position,lt]
  by_cases eq : x=c
  · subst x
    by_cases yc : y=c <;> simp [position,yc,not_lt_of_ge xy]
  · have cy := (lt_of_le_of_ne (le_of_not_gt lt) (Ne.symm eq)).trans_le xy
    simp [position,lt,eq,not_lt_of_ge cy.le,cy.ne']

private noncomputable def label (C : Finset ℝ) (x : ℝ) := ∑ c ∈ C, position c x

private theorem label_mono (C : Finset ℝ) : Monotone (label C) :=
  fun _ _ xy => sum_le_sum fun c _ => position_mono c xy

private theorem isolated {C : Finset ℝ} {c x : ℝ} (hc : c∈C) (eq : label C x=label C c) :
    x=c := by
  rcases lt_trichotomy x c with lt|same|gt
  · have sep : label C x < label C c := sum_lt_sum
      (fun v _ => position_mono v lt.le) ⟨c,hc,by simp [position,lt]⟩
    omega
  · exact same
  · have sep : label C c < label C x := sum_lt_sum
      (fun v _ => position_mono v gt.le) ⟨c,hc,by simp [position,gt.ne',not_lt_of_ge gt.le]⟩
    omega

private def realCell (A B : ℝ[X]) (i : ℕ) : Set ℝ :=
  {x | label (cuts A B) x=i ∧ B.eval x≠0}

private theorem convex_cell (A B : ℝ[X]) (i : ℕ) : Convex ℝ (realCell A B i) := by
  apply convex_iff_ordConnected.mpr
  apply Set.ordConnected_iff.mpr
  intro x hx y hy _ z hz
  have eq : label (cuts A B) z=i :=
    le_antisymm ((label_mono _ hz.2).trans_eq hy.1) (hx.1 ▸ label_mono _ hz.1)
  refine ⟨eq, ?_⟩
  intro zero
  have bn : B≠0 := by intro h; exact hx.2 (by simp [h])
  have root : z∈cuts A B := mem_union_left _ (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots bn).mpr zero))
  have same := isolated root (hx.1.trans eq.symm)
  exact hx.2 (same ▸ zero)

/-- Exact real ratio, with domain restricted to nonzero denominators by the pieces. -/
noncomputable def ratio (A B : ℝ[X]) (x : ℝ) : ℝ := A.eval x/B.eval x

private theorem real_turns (A B : ℝ[X]) (i : ℕ) :
    MonotoneOn (ratio A B) (realCell A B i) ∨ AntitoneOn (ratio A B) (realCell A B i) := by
  let D := realCell A B i
  by_cases point : ∃ c ∈ D, c∈cuts A B
  · obtain ⟨c,hc,cut⟩ := point
    left
    intro x hx y hy _
    have xe := isolated cut (hx.1.trans hc.1.symm)
    have ye := isolated cut (hy.1.trans hc.1.symm)
    exact le_of_eq (congrArg (ratio A B) (xe.trans ye.symm))
  have convex := convex_cell A B i
  have sign : (∀ x ∈ D, 0 ≤ (slope A B).eval x) ∨ (∀ x ∈ D, (slope A B).eval x ≤ 0) := by
    by_cases pos : ∀ x ∈ D, 0 ≤ (slope A B).eval x
    · exact Or.inl pos
    right
    push_neg at pos
    obtain ⟨x,hx,neg⟩ := pos
    intro y hy
    by_contra! above
    have zero : (0:ℝ) ∈ Set.Icc ((slope A B).eval x) ((slope A B).eval y) := ⟨neg.le,above.le⟩
    obtain ⟨z,hz,root⟩ := convex.isPreconnected.intermediate_value hx hy
      (slope A B).continuous.continuousOn zero
    have nonzero : slope A B≠0 := by intro h; simp [h] at neg
    exact point ⟨z,hz,mem_union_right _ (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots nonzero).mpr root))⟩
  have der (x : ℝ) (hx : x∈D) :
      HasDerivAt (ratio A B) ((slope A B).eval x / (B.eval x)^2) x := by
    simpa [ratio,slope] using (A.hasDerivAt x).div (B.hasDerivAt x) hx.2
  have cont : ContinuousOn (ratio A B) D := fun x hx => (der x hx).continuousAt.continuousWithinAt
  have inside {x : ℝ} (hx : x∈interior D) := (der x (interior_subset hx)).hasDerivWithinAt (s:=interior D)
  rcases sign with pos|neg
  · exact Or.inl (monotoneOn_of_hasDerivWithinAt_nonneg convex cont (fun _ hx => inside hx)
      (fun x hx => div_nonneg (pos x (interior_subset hx)) (sq_nonneg _)))
  · exact Or.inr (antitoneOn_of_hasDerivWithinAt_nonpos convex cont (fun _ hx => inside hx)
      (fun x hx => div_nonpos_of_nonpos_of_nonneg (neg x (interior_subset hx)) (sq_nonneg _)))

/-- Part of the i-th interval lying in the natural-number input domain. -/
def piece (A B : ℝ[X]) (i : ℕ) : Set ℕ := {n | (n : ℝ)∈realCell A B i}

theorem covers (A B : ℝ[X]) (n : ℕ) (defined : B.eval (n:ℝ)≠0) :
    ∃ i ∈ range (budget A B), n∈piece A B i := by
  refine ⟨label (cuts A B) n, mem_range.mpr ?_,rfl,defined⟩
  have cap : label (cuts A B) n ≤ (cuts A B).card*2 := by
    calc
      _ ≤ ∑ _ ∈ cuts A B, 2 := sum_le_sum fun c _ => by unfold position; split_ifs <;> decide
      _ = _ := by simp
  have total := count_cuts A B
  unfold budget
  omega

theorem unique {A B : ℝ[X]} {n i j : ℕ} (hi : n∈piece A B i) (hj : n∈piece A B j) : i=j :=
  hi.1.symm.trans hj.1

/-- Every defined input has exactly one piece, and every pole has none. -/
theorem domain (A B : ℝ[X]) (n : ℕ) : B.eval (n:ℝ)≠0 ↔
    ∃! i, i∈range (budget A B) ∧ n∈piece A B i := by
  constructor
  · intro defined
    obtain ⟨i, hi, mem⟩ := covers A B n defined
    exact ⟨i, ⟨hi,mem⟩, fun _ h => unique h.2 mem⟩
  · rintro ⟨_, ⟨_, mem⟩, _⟩
    exact mem.2

/-- Smaller labels lie strictly to the left of larger labels. -/
theorem ordered {A B : ℝ[X]} {m n i j : ℕ} (hm : m∈piece A B i)
    (hn : n∈piece A B j) (ij : i<j) : m<n := by
  by_contra! flip
  have back := label_mono (cuts A B) (show (n:ℝ)≤m by exact_mod_cast flip)
  rw [hm.1,hn.1] at back
  omega

theorem interval (A B : ℝ[X]) (i : ℕ) : (piece A B i).OrdConnected := by
  apply Set.ordConnected_iff.mpr
  intro x hx y hy _ z hz
  exact (convex_cell A B i).ordConnected.1 hx hy ⟨by exact_mod_cast hz.1,by exact_mod_cast hz.2⟩

/-- The unrestricted real-valued predictor on integer inputs is monotone or
antitone on each of the same intervals. -/
theorem ratio_on (A B : ℝ[X]) (i : ℕ) :
    MonotoneOn (fun n : ℕ => ratio A B n) (piece A B i) ∨
    AntitoneOn (fun n : ℕ => ratio A B n) (piece A B i) := by
  rcases real_turns A B i with inc|dec
  · exact Or.inl (fun _ hx _ hy le => inc hx hy (by exact_mod_cast le))
  · exact Or.inr (fun _ hx _ hy le => dec hx hy (by exact_mod_cast le))

/-- Natural floor agrees with integer floor on nonnegative outputs and
returns zero on negative outputs. -/
noncomputable def rounded (A B : ℝ[X]) (n : ℕ) : ℕ := ⌊ratio A B n⌋₊

/-- The real ratio, hence its floor, changes in only one direction on each
piece. -/
theorem rounded_on (A B : ℝ[X]) (i : ℕ) :
    MonotoneOn (rounded A B) (piece A B i) ∨ AntitoneOn (rounded A B) (piece A B i) := by
  rcases real_turns A B i with inc|dec
  · exact Or.inl (fun _ hx _ hy le => Nat.floor_mono (inc hx hy (by exact_mod_cast le)))
  · exact Or.inr (fun _ hx _ hy le => Nat.floor_mono (dec hx hy (by exact_mod_cast le)))

theorem integer_floor_on (A B : ℝ[X]) (i : ℕ) :
    MonotoneOn (fun n : ℕ => ⌊ratio A B n⌋) (piece A B i) ∨
    AntitoneOn (fun n : ℕ => ⌊ratio A B n⌋) (piece A B i) := by
  rcases real_turns A B i with inc|dec
  · exact Or.inl (fun _ hx _ hy le => Int.floor_mono (inc hx hy (by exact_mod_cast le)))
  · exact Or.inr (fun _ hx _ hy le => Int.floor_mono (dec hx hy (by exact_mod_cast le)))

end PrimeFactors.RationalPredictionTurns
