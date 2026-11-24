import PrimeFactors.CoupledImages
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace PrimeFactors

section Mass

variable {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- A point in one local set gives its sign two votes when unique and one vote
when it also belongs to the opposite local set. -/
private def signVotes {X : Type*} [DecidableEq X] (C : Bool → Finset X)
    (b : Bool) (x : X) : ℕ :=
  (if x ∈ C b then 1 else 0) + (if x ∈ C b \ C (!b) then 1 else 0)

private theorem sum_signVotes {X : Type*} [Fintype X] [DecidableEq X]
    (C : Bool → Finset X) (eqCard : (C false).card = (C true).card) (b : Bool) :
    ∑ x, signVotes C b x = (C false ∪ C true).card := by
  have h : (C b).card = (C (!b)).card := by cases b <;> simp [eqCard]
  simp only [signVotes, Finset.sum_add_distrib, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  change (C b).card + (C b \ C (!b)).card = _
  rw [add_comm, h, Finset.card_sdiff_add_card]
  cases b <;> simp [Finset.union_comm]

private theorem signVotes_per_point {X : Type*} [DecidableEq X] (C : Bool → Finset X) (x : X) :
    ∑ b, signVotes C b x ≤ 2 := by
  rw [Fintype.sum_bool]
  by_cases h : x ∈ C true <;> by_cases h' : x ∈ C false <;> simp [signVotes, h, h']

/-- A subset of sign vectors occupies at least its share of the full optimal
union. The count applies to arbitrary pattern-dependent translations whose
single-set and two-set minima are attained by the given canonical sets. -/
theorem groupedImage_sign_mass (patterns : Finset (I → Bool))
    (canonical : (i : I) → Bool → Finset (A i))
    (equal : ∀ i, (canonical i false).card = (canonical i true).card)
    (old : (I → Bool) → (i : I) → Finset (A i))
    (minimal : ∀ i, ∀ r ∈ patterns, ∀ t ∈ patterns,
      (canonical i (r i) ∪ canonical i (t i)).card ≤ (old r i ∪ old t i).card) :
    patterns.card * (∏ i, (canonical i false ∪ canonical i true).card) ≤
      2 ^ Fintype.card I * (coupledImageBoxes patterns old).card := by
  classical
  let C := coupledImageBoxes patterns (fun r i => canonical i (r i))
  let votes (r : I → Bool) (x : (i : I) → A i) := ∏ i, signVotes (canonical i) (r i) (x i)
  have row (r : I → Bool) : ∑ x, votes r x = ∏ i, (canonical i false ∪ canonical i true).card := by
    rw [show ∑ x, votes r x = ∏ i, ∑ v, signVotes (canonical i) (r i) v from (Fintype.prod_sum _).symm]
    simp_rw [sum_signVotes _ (equal _)]
  have column (x : (i : I) → A i) : ∑ r ∈ patterns, votes r x ≤
      if x ∈ C then 2 ^ Fintype.card I else 0 := by
    split_ifs with mem
    · calc
        _ ≤ ∑ r, votes r x := Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
        _ = ∏ i, ∑ b, signVotes (canonical i) b (x i) :=
          (Fintype.prod_sum (fun (i : I) (b : Bool) => signVotes (canonical i) b (x i))).symm
        _ ≤ ∏ _ : I, 2 := Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          (fun i _ => signVotes_per_point (canonical i) (x i))
        _ = _ := by simp
    · apply Nat.le_zero.mpr
      apply Finset.sum_eq_zero
      intro r hr
      have bad : ¬ ∀ i, x i ∈ canonical i (r i) := fun all =>
        mem (Finset.mem_biUnion.mpr ⟨r, hr, Fintype.mem_piFinset.mpr all⟩)
      push_neg at bad
      obtain ⟨i, hi⟩ := bad
      exact Finset.prod_eq_zero (f := fun j => signVotes (canonical j) (r j) (x j))
        (Finset.mem_univ i) (by simp [signVotes, hi])
  calc
    _ = ∑ r ∈ patterns, ∑ x, votes r x := by simp_rw [row]; simp
    _ = ∑ x, ∑ r ∈ patterns, votes r x := Finset.sum_comm
    _ ≤ ∑ x, if x ∈ C then 2 ^ Fintype.card I else 0 := Finset.sum_le_sum fun x _ => column x
    _ = 2 ^ Fintype.card I * C.card := by simp [Finset.sum_ite, Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (coupledImage_optimal patterns id old canonical minimal)

end Mass

end PrimeFactors
