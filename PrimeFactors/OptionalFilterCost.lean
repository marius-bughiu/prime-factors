import PrimeFactors.IndependentFilterOrdering

/-! Charge one lookup for each optional filter and a fixed cost for the final
exact test. Complete-period pass fractions give a simple threshold for which
filters to use. -/
namespace PrimeFactors.OptionalFilterCost

open IndependentFilterOrdering

/-- Finish by checking every survivor at price c in units of a single lookup. -/
noncomputable def cost (c : ℚ) (rates : List ℚ) : ℚ :=
  expected rates + rates.prod * c

@[simp] theorem nil_cost (c : ℚ) : cost c [] = c := by simp [cost,expected]

@[simp] theorem cons_cost (c a : ℚ) (rates : List ℚ) :
    cost c (a::rates) = 1+a*cost c rates := by
  simp [cost,expected]
  ring

/-- Appending this optional test pays exactly when it saves enough final checks. -/
theorem extra_cost (rates : List ℚ) (a c : ℚ) :
    cost c (rates++[a])-cost c rates = rates.prod*(1-(1-a)*c) := by
  simp [cost,expected_append,expected]
  ring

noncomputable def choose (c : ℚ) (rates : List ℚ) : List ℚ :=
  rates.filter fun a => 1+a*c < c

private theorem barrier {a c : ℚ} (profitable : 1+a*c ≤ c) (rates : List ℚ)
    (above : ∀ b ∈ rates, a ≤ b) (positive : ∀ b ∈ rates, 0 ≤ b) :
    1+a*cost c rates ≤ cost c rates := by
  induction rates with
  | nil => simpa only [nil_cost] using profitable
  | cons b bs ih =>
    have tail := ih (fun p hp => above p (List.mem_cons_of_mem _ hp))
      (fun p hp => positive p (List.mem_cons_of_mem _ hp))
    have comparison := mul_le_mul_of_nonneg_left tail (positive b (by simp))
    rw [cons_cost]
    nlinarith only [comparison,above b (by simp)]

/-- For an already sorted sequence, this choice minimizes cost even against
competitors allowed to omit any subsequence of tests. -/
theorem optimal_sublist (c : ℚ) (price : 0 ≤ c) {rates other : List ℚ}
    (sorted : rates.Pairwise (· ≤ ·)) (positive : ∀ p ∈ rates, 0 ≤ p)
    (sub : other.Sublist rates) : cost c (choose c rates) ≤ cost c other := by
  induction sub with
  | slnil => simp [choose]
  | @cons xs ys b sub ih =>
    obtain ⟨above,sortedTail⟩ := List.pairwise_cons.mp sorted
    have posTail : ∀ p ∈ ys, 0 ≤ p := fun p hp => positive p (List.mem_cons_of_mem _ hp)
    have opt := ih sortedTail posTail
    by_cases good : 1+b*c<c
    · have keep := barrier good.le (choose c ys)
        (fun p hp => above p (List.mem_filter.mp hp).1)
        (fun p hp => posTail p (List.mem_filter.mp hp).1)
      simpa [choose,List.filter_cons,good] using keep.trans opt
    · simpa [choose,List.filter_cons,good] using opt
  | @cons₂ xs ys b sub ih =>
    obtain ⟨above,sortedTail⟩ := List.pairwise_cons.mp sorted
    have pos := positive b (by simp)
    have posTail : ∀ p ∈ ys, 0 ≤ p := fun p hp => positive p (List.mem_cons_of_mem _ hp)
    have opt := ih sortedTail posTail
    by_cases good : 1+b*c<c
    · simpa [choose,List.filter_cons,good] using
        add_le_add_left (mul_le_mul_of_nonneg_left opt pos) 1
    · have empty : choose c ys = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro p hp
        obtain ⟨inside,hp⟩ := List.mem_filter.mp hp
        have ple := mul_le_mul_of_nonneg_right (above p inside) price
        simp only [decide_eq_true_eq] at hp
        linarith
      rw [empty,nil_cost] at opt
      have compare := mul_le_mul_of_nonneg_left opt pos
      have eq : choose c (b::ys) = choose c ys := by simp [choose,List.filter_cons,good]
      rw [eq,empty,nil_cost,cons_cost]
      linarith

/-- The same schedule is optimal among all subsets in all orders. -/
theorem optimal (c : ℚ) (price : 0 ≤ c) {rates other : List ℚ}
    (sorted : rates.Pairwise (· ≤ ·)) (positive : ∀ p ∈ rates, 0 ≤ p)
    (sub : other.Subperm rates) : cost c (choose c rates) ≤ cost c other := by
  let ordered := other.insertionSort (· ≤ ·)
  have shape : ordered.Perm other := List.perm_insertionSort _ _
  obtain ⟨l, perm, nested⟩ := sub
  have subperm : ordered.Subperm rates := ⟨l,perm.trans shape.symm,nested⟩
  have sortedOther : ordered.Pairwise (· ≤ ·) := List.sorted_insertionSort _ _
  have first := optimal_sublist c price sorted positive
    (List.sublist_of_subperm_of_sorted subperm sortedOther sorted)
  have sign : ∀ p ∈ other, 0 ≤ p := fun p hp => positive p (nested.subset (perm.symm.subset hp))
  have second := IndependentFilterOrdering.optimal sortedOther shape sign
  apply first.trans
  unfold cost
  rw [shape.prod_eq]
  linarith

end PrimeFactors.OptionalFilterCost
