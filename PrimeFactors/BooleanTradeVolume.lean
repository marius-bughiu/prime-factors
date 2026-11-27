import PrimeFactors.BooleanMarginalAmbiguity

/-! Minimum volume of a nonempty Boolean trade. Each cell records the tests a
row passes. Ghorbani, Kamali, Khosrovshahi and Krotov give the classical result
in Lemma 4 of *On the Volumes and Affine Types of Trades* (2020),
https://doi.org/10.37236/8367. -/
namespace PrimeFactors.BooleanTradeVolume
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def mass (T : Finset ι → ℕ) : ℕ := ∑ s, T s

/-- Count rows passing every test in A, with all other tests unspecified. -/
noncomputable def intersection (T : Finset ι → ℕ) (A : Finset ι) : ℕ :=
  ∑ s, if A ⊆ s then T s else 0

/-- The empty intersection records the common sample size. -/
def SameThrough (r : ℕ) (T U : Finset ι → ℕ) : Prop :=
  ∀ A : Finset ι, A.card ≤ r → intersection T A = intersection U A

private theorem total_eq {r : ℕ} {T U : Finset ι → ℕ} (h : SameThrough r T U) :
    mass T = mass U := by
  simpa [mass,intersection] using h ∅ (by simp)

private def slice (T : Finset ι → ℕ) (i : ι) (present : Bool) (s : Finset ι) : ℕ :=
  if decide (i ∈ s) = present then T s else 0

private theorem intersection_present (T : Finset ι → ℕ) (i : ι) (A : Finset ι) :
    intersection (slice T i true) A = intersection T (insert i A) := by
  unfold intersection
  apply sum_congr rfl
  intro s _
  by_cases h : i ∈ s <;> by_cases a : A ⊆ s <;> simp [insert_subset_iff,slice,h,a]

private theorem intersection_split (T : Finset ι → ℕ) (i : ι) (A : Finset ι) :
    intersection (slice T i true) A + intersection (slice T i false) A = intersection T A := by
  unfold intersection
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro s _
  by_cases h : i ∈ s <;> by_cases a : A ⊆ s <;> simp [slice,h,a]

private theorem slices_agree {r : ℕ} {T U : Finset ι → ℕ} (h : SameThrough (r+1) T U) (i : ι) :
    SameThrough r (slice T i true) (slice U i true) ∧
    SameThrough r (slice T i false) (slice U i false) := by
  have present : SameThrough r (slice T i true) (slice U i true) := by
    intro A small
    rw [intersection_present,intersection_present]
    exact h _ ((Finset.card_insert_le ..).trans (by omega))
  refine ⟨present,?_⟩
  intro A small
  have t := intersection_split T i A
  have u := intersection_split U i A
  have e := present A small
  have e' := h A (by omega)
  omega

/-- Equal totals and unequal tables require at least two different row
patterns with unequal multiplicities. A coordinate separates two such cells. -/
private theorem split_differences {T U : Finset ι → ℕ} (total : mass T = mass U) (ne : T ≠ U) :
    ∃ i : ι, slice T i true ≠ slice U i true ∧ slice T i false ≠ slice U i false := by
  obtain ⟨a,ha⟩ := Function.ne_iff.mp ne
  have other : ∃ b, b ≠ a ∧ T b ≠ U b := by
    by_contra! only
    have rest : ∑ s ∈ univ.erase a, T s = ∑ s ∈ univ.erase a, U s :=
      sum_congr rfl fun s hs => only s (mem_erase.mp hs).1
    have t := sum_erase_add univ T (mem_univ a)
    have u := sum_erase_add univ U (mem_univ a)
    unfold mass at total
    omega
  obtain ⟨b,ba,hb⟩ := other
  obtain ⟨i,hi⟩ : ∃ i, ¬(i ∈ a ↔ i ∈ b) := by
    by_contra! same
    exact ba (Finset.ext fun i => (same i).symm)
  have atCell {s : Finset ι} (hs : T s ≠ U s) (v : Bool) (val : decide (i ∈ s) = v) :
      slice T i v ≠ slice U i v := by
    intro eq
    exact hs (by simpa [slice,val] using congrFun eq s)
  refine ⟨i,?_⟩
  by_cases ia : i ∈ a
  · have ib : i ∉ b := fun h => hi ⟨fun _ => h, fun _ => ia⟩
    exact ⟨atCell ha true (by simp [ia]),atCell hb false (by simp [ib])⟩
  · have ib : i ∈ b := by by_contra h; exact hi (by simp [ia,h])
    exact ⟨atCell hb true (by simp [ib]),atCell ha false (by simp [ia])⟩

/-- Distinct row-multiplicity tables with identical intersection counts through
order r each have at least 2^r observations. No dependence on the number of
tests enters the lower bound. -/
theorem minimum {r : ℕ} {T U : Finset ι → ℕ} (h : SameThrough r T U) (ne : T ≠ U) :
    2^r ≤ mass T := by
  induction r generalizing T U with
  | zero =>
    have sizes := total_eq h
    by_contra! small
    apply ne
    funext s
    have t := single_le_sum (f:=T) (fun _ _ => Nat.zero_le _) (mem_univ s)
    have u := single_le_sum (f:=U) (fun _ _ => Nat.zero_le _) (mem_univ s)
    unfold mass at sizes small
    simp only [pow_zero] at small
    omega
  | succ r ih =>
    obtain ⟨i,positive,negative⟩ := split_differences (total_eq h) ne
    obtain ⟨yes,no⟩ := slices_agree h i
    have yp := ih yes positive
    have np := ih no negative
    have parts : mass (slice T i true) + mass (slice T i false) = mass T := by
      simpa [mass,intersection] using intersection_split T i ∅
    rw [pow_succ]
    omega

/-- A table specifies an unordered sample, with the multiplicity of every
test pattern. Below 2^r the given intersections determine the whole sample. -/
theorem unique_of_small {r : ℕ} {T U : Finset ι → ℕ} (h : SameThrough r T U)
    (small : mass T < 2^r) : T = U := by
  by_contra ne
  exact (not_le_of_gt small) (minimum h ne)

/-- For observed lists the same uniqueness is literal equality up to a
permutation of the rows, including any duplicate signatures. -/
theorem perm_of_small {r : ℕ} {xs ys : List (Finset ι)}
    (h : SameThrough r (fun s => xs.count s) (fun s => ys.count s))
    (small : xs.length < 2^r) : xs.Perm ys := by
  have size : mass (fun s => xs.count s) = xs.length := by
    simpa [mass] using (Multiset.sum_count_eq_card (s:=univ) (m:=(xs:Multiset (Finset ι)))
      (fun a _ => mem_univ a))
  exact List.perm_iff_count.mpr (congrFun (unique_of_small h (size.trans_lt small)))

/-- Extend a table on the coordinates in C by fixing every other test to false. -/
private def embed (C : Finset ι) (T : Finset ι → ℕ) (s : Finset ι) :=
  if s ⊆ C then T s else 0

private theorem intersection_embed (C A : Finset ι) (T : Finset ι → ℕ) :
    intersection (embed C T) A = if A ⊆ C then
      BooleanMarginalAmbiguity.marginal T A (C \ A) else 0 := by
  have range : C.powerset = univ.filter (· ⊆ C) := by ext; simp
  have expand : intersection (embed C T) A = ∑ s ∈ C.powerset.filter (A ⊆ ·), T s := by
    rw [range,sum_filter,sum_filter]
    unfold intersection embed
    apply sum_congr rfl
    intro s _
    by_cases a : A ⊆ s <;> by_cases c : s ⊆ C <;> simp [a,c]
  rw [expand]
  split_ifs with ac
  · unfold BooleanMarginalAmbiguity.marginal
    refine sum_bij' (fun s _ => s \ A) (fun b _ => A ∪ b) ?_ ?_ ?_ ?_ ?_
    · intro s hs
      obtain ⟨sc,_⟩ := mem_filter.mp hs
      apply mem_powerset.mpr
      intro i hi
      obtain ⟨ins, out⟩ := mem_sdiff.mp hi
      exact mem_sdiff.mpr ⟨mem_powerset.mp sc ins, out⟩
    · intro b hb
      have bc : b ⊆ C := (mem_powerset.mp hb).trans sdiff_subset
      exact mem_filter.mpr ⟨mem_powerset.mpr (union_subset ac bc),subset_union_left⟩
    · intro s hs
      exact union_sdiff_of_subset (mem_filter.mp hs).2
    · intro b hb
      apply union_sdiff_cancel_left
      exact disjoint_left.mpr fun a ha ab => (mem_sdiff.mp (mem_powerset.mp hb ab)).2 ha
    · intro s hs
      rw [union_sdiff_of_subset (mem_filter.mp hs).2]
  · apply sum_eq_zero
    intro s hs
    exact (ac ((mem_filter.mp hs).2.trans (mem_powerset.mp (mem_filter.mp hs).1))).elim

/-- On any larger ground set, the two parity classes on r+1 coordinates
realize a difference with exactly 2^r rows on each side. -/
theorem sharp {r : ℕ} (more : r < Fintype.card ι) :
    ∃ T U : Finset ι → ℕ, SameThrough r T U ∧ mass T = 2^r ∧ mass U = 2^r ∧ T ≠ U := by
  obtain ⟨C,_,card⟩ := exists_subset_card_eq (s:=univ)
    (show r+1 ≤ (univ:Finset ι).card by simpa using more)
  let T := embed C (BooleanMarginalAmbiguity.parityTable 1 true)
  let U := embed C (BooleanMarginalAmbiguity.parityTable 1 false)
  have same : SameThrough r T U := by
    intro A small
    unfold T U
    rw [intersection_embed,intersection_embed]
    split_ifs with ac
    · apply BooleanMarginalAmbiguity.proper_marginals (BooleanMarginalAmbiguity.parity_faces 1)
      · exact disjoint_left.mpr fun i h hi => (mem_sdiff.mp hi).2 h
      · apply sdiff_nonempty.mpr
        intro ca
        have le := card_le_card ca
        omega
    · rfl
  have counts (v : Bool) : mass (embed C (BooleanMarginalAmbiguity.parityTable 1 v)) =
      ∑ b ∈ C.powerset, BooleanMarginalAmbiguity.parityTable 1 v b := by
    simpa [mass,intersection,BooleanMarginalAmbiguity.marginal] using
      intersection_embed C ∅ (BooleanMarginalAmbiguity.parityTable 1 v)
  have sum : mass T + mass U = 2^C.card := by
    unfold T U
    rw [counts,counts,←sum_add_distrib]
    have one (b : Finset ι) : BooleanMarginalAmbiguity.parityTable 1 true b +
        BooleanMarginalAmbiguity.parityTable 1 false b = 1 := by
      by_cases e : Even b.card <;> simp [BooleanMarginalAmbiguity.parityTable,e]
    simp [one]
  have eq := total_eq same
  rw [card,pow_succ] at sum
  refine ⟨T,U,same,by omega,by omega,?_⟩
  intro h
  have bad := congrFun h ∅
  simp [T,U,embed,BooleanMarginalAmbiguity.parityTable] at bad

end PrimeFactors.BooleanTradeVolume
