import PrimeFactors.FiniteFilterWork
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-! Expected cost of equal-cost independent tests in a conjunction. The
standard adjacent exchange puts the smallest pass probability first. For
background on sequential testing of series systems see Y. Ben-Dov (1981),
https://doi.org/10.1287/mnsc.27.12.1410. -/
namespace PrimeFactors.IndependentFilterOrdering

/-- Expected number of tests per starting row. Reaching the remaining tests
requires the first test to pass. -/
noncomputable def expected : List ℚ → ℚ
  | [] => 0
  | p::ps => 1+p*expected ps

/-- The work after a prefix is weighted by its joint pass fraction. -/
theorem expected_append (prior tail : List ℚ) :
    expected (prior++tail) = expected prior + prior.prod * expected tail := by
  induction prior with
  | nil => simp [expected]
  | cons p ps ih =>
    simp only [List.cons_append,expected,List.prod_cons,ih]
    ring

/-- The exact saving from exchanging adjacent tests is the difference of
their pass fractions times the probability of reaching the pair. -/
theorem adjacent (prior tail : List ℚ) (a b : ℚ) :
    expected (prior++a::b::tail) - expected (prior++b::a::tail) = prior.prod*(a-b) := by
  rw [expected_append,expected_append]
  simp only [expected]
  ring

private theorem insert_le (a : ℚ) (xs : List ℚ) (positive : ∀ p ∈ xs, 0 ≤ p) :
    expected (xs.orderedInsert (· ≤ ·) a) ≤ expected (a::xs) := by
  induction xs with
  | nil => simp [List.orderedInsert]
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp [List.orderedInsert,h]
    · have tail := ih (fun p hp => positive p (by simp [hp]))
      have bp := positive b (by simp)
      have comp := mul_le_mul_of_nonneg_left tail bp
      have swap := adjacent [] bs b a
      simp only [List.nil_append,List.prod_nil,one_mul] at swap
      rw [List.orderedInsert,if_neg h]
      calc
        expected (b::List.orderedInsert (· ≤ ·) a bs) ≤ expected (b::a::bs) :=
          add_le_add_left comp 1
        _ ≤ expected (a::b::bs) := by linarith

private theorem sort_le (xs : List ℚ) (positive : ∀ p ∈ xs, 0 ≤ p) :
    expected (xs.insertionSort (· ≤ ·)) ≤ expected xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    have rest : ∀ p ∈ as, 0 ≤ p := fun p hp => positive p (by simp [hp])
    have insert := insert_le a (as.insertionSort (· ≤ ·))
      (fun p hp => rest p ((List.mem_insertionSort _).mp hp))
    exact insert.trans (add_le_add_left
      (mul_le_mul_of_nonneg_left (ih rest) (positive a (by simp))) 1)

/-- A sorted permutation minimizes expected tests. The algebra requires
only nonnegative entries, which includes pass probabilities in [0,1]. -/
theorem optimal {sorted other : List ℚ} (order : sorted.Pairwise (· ≤ ·))
    (same : sorted.Perm other) (positive : ∀ p ∈ other, 0 ≤ p) :
    expected sorted ≤ expected other := by
  have eq : sorted = other.insertionSort (· ≤ ·) :=
    List.eq_of_perm_of_sorted (same.trans (List.perm_insertionSort _ other).symm) order
      (List.sorted_insertionSort _ other)
  rw [eq]
  exact sort_le other positive

variable {α : Type*}

/-- At every stage, the stated pass fraction agrees with the exact count
among the rows which reached that stage. -/
def ExactRates (xs : List α) : List ((α → Bool) × ℚ) → Prop
  | [] => True
  | (f,p)::fs => ((xs.filter f).length:ℚ) = xs.length*p ∧ ExactRates (xs.filter f) fs

/-- Under the stated conditional counts the expectation gives the exact
finite number of scalar tests, multiplied by the starting population. -/
theorem work_eq {xs : List α} {fs : List ((α → Bool) × ℚ)} (rates : ExactRates xs fs) :
    (FiniteFilterWork.work xs (fs.map Prod.fst):ℚ) = xs.length*expected (fs.map Prod.snd) := by
  induction fs generalizing xs with
  | nil => simp [FiniteFilterWork.work,expected]
  | cons f fs ih =>
    obtain ⟨pass,p⟩ := f
    obtain ⟨first,rest⟩ := rates
    simp only [List.map_cons,FiniteFilterWork.work,expected,Nat.cast_add,ih rest,first]
    ring

/-- Apply the exchange result to an actual finite population when the same
fractions hold in both tested orders, as happens on joint complete periods
for filters on pairwise coprime moduli. -/
theorem optimal_work {xs : List α} {fs gs : List ((α → Bool) × ℚ)}
    (same : fs.Perm gs) (order : (fs.map Prod.snd).Pairwise (· ≤ ·))
    (positive : ∀ p ∈ gs.map Prod.snd, 0 ≤ p)
    (left : ExactRates xs fs) (right : ExactRates xs gs) :
    FiniteFilterWork.work xs (fs.map Prod.fst) ≤ FiniteFilterWork.work xs (gs.map Prod.fst) := by
  have h := mul_le_mul_of_nonneg_left (optimal order (same.map _) positive)
    (show (0:ℚ) ≤ xs.length by positivity)
  rw [←work_eq left,←work_eq right] at h
  exact_mod_cast h

end PrimeFactors.IndependentFilterOrdering
