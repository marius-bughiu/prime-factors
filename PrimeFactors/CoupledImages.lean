import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Prod

namespace PrimeFactors

/-- A union of coordinate boxes, with an arbitrary finite set of required rows. -/
noncomputable def coupledImageBoxes {R I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, DecidableEq (A i)] (rows : Finset R)
    (localSet : R → (i : I) → Finset (A i)) : Finset ((i : I) → A i) :=
  rows.biUnion fun r => Fintype.piFinset (localSet r)

private theorem two_choices_compress {R T : Type*} [DecidableEq T]
    (rows : Finset R) (sign : R → Bool) (canonical : Bool → Finset T) (old : R → Finset T)
    (minPair : ∀ r ∈ rows, ∀ t ∈ rows, (canonical (sign r) ∪ canonical (sign t)).card ≤
      (old r ∪ old t).card) :
    (rows.biUnion (fun r => canonical (sign r))).card ≤ (rows.biUnion old).card := by
  classical
  rcases rows.eq_empty_or_nonempty with rfl | ⟨r,hr⟩
  · simp
  have reps : ∃ t ∈ rows, ∀ j ∈ rows, sign j=sign r ∨ sign j=sign t := by
    by_cases other : ∃ t ∈ rows, sign t ≠ sign r
    · obtain ⟨t,ht,ne⟩ := other
      refine ⟨t,ht,fun j _ => ?_⟩
      cases h₁ : sign r <;> cases h₂ : sign t <;> cases h₃ : sign j <;> simp_all
    · push_neg at other
      exact ⟨r,hr,fun j hj => Or.inl (other j hj)⟩
  obtain ⟨t,ht,rep⟩ := reps
  calc
    _ ≤ (canonical (sign r) ∪ canonical (sign t)).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨j,hj,hx⟩ := Finset.mem_biUnion.mp hx
      rcases rep j hj with eq | eq
      · exact Finset.mem_union_left _ (eq ▸ hx)
      · exact Finset.mem_union_right _ (eq ▸ hx)
    _ ≤ (old r ∪ old t).card := minPair r hr t ht
    _ ≤ _ := Finset.card_le_card (Finset.union_subset
      (Finset.subset_biUnion_of_mem old hr) (Finset.subset_biUnion_of_mem old ht))

section Coordinates

variable {R I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

private theorem coupledImage_slices (i : I) (rows : Finset R) (L : R → (j : I) → Finset (A j)) :
    (coupledImageBoxes rows L).card = ∑ y : (j : {j // j ≠ i}) → A j,
      ((rows.filter (fun r => ∀ j : {j // j ≠ i}, y j ∈ L r j)).biUnion (fun r => L r i)).card := by
  classical
  let rest (x : (j : I) → A j) (j : {j // j ≠ i}) := x j
  rw [Finset.card_eq_sum_card_fiberwise (show Set.MapsTo rest (coupledImageBoxes rows L)
    (Finset.univ : Finset ((j : {j // j ≠ i}) → A j)) from fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.card_bij (fun x _ => x i)
  · intro x hx
    obtain ⟨mx,eq⟩ := Finset.mem_filter.mp hx
    obtain ⟨r,hr,mr⟩ := Finset.mem_biUnion.mp mx
    have all := Fintype.mem_piFinset.mp mr
    exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_filter.mpr ⟨hr,eq ▸ fun j => all j⟩,all i⟩
  · intro x hx z hz atI
    have common := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hz).2.symm
    funext j
    by_cases eq : j=i
    · subst j; exact atI
    · exact congrFun common ⟨j,eq⟩
  · intro z hz
    obtain ⟨r,hr,localMem⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨rr,others⟩ := Finset.mem_filter.mp hr
    let x := (Equiv.piSplitAt i A).symm (z,y)
    have atI : x i=z := congrArg Prod.fst ((Equiv.piSplitAt i A).apply_symm_apply (z,y))
    have off : rest x=y := congrArg Prod.snd ((Equiv.piSplitAt i A).apply_symm_apply (z,y))
    refine ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨r,rr,Fintype.mem_piFinset.mpr ?_⟩,
      off⟩,atI⟩
    intro j
    by_cases eq : j=i
    · subst j; simpa only [atI] using localMem
    · have same : x j=y ⟨j,eq⟩ := congrFun off ⟨j,eq⟩
      exact same ▸ others ⟨j,eq⟩

/-- Replacing the chosen coordinate by a common optimal representative for
each sign weakly decreases the cardinality of the union. Every other
coordinate and the set of requested sign patterns may be arbitrary. -/
theorem coupledImage_compress_coordinate (i : I) (rows : Finset R) (sign : R → Bool)
    (old newSet : R → (j : I) → Finset (A j)) (canonical : Bool → Finset (A i))
    (same : ∀ r j, j ≠ i → newSet r j=old r j)
    (atI : ∀ r, newSet r i=canonical (sign r))
    (minimal : ∀ r ∈ rows, ∀ t ∈ rows, (canonical (sign r) ∪ canonical (sign t)).card ≤
      (old r i ∪ old t i).card) :
    (coupledImageBoxes rows newSet).card ≤ (coupledImageBoxes rows old).card := by
  classical
  rw [coupledImage_slices i rows newSet,coupledImage_slices i rows old]
  apply Finset.sum_le_sum
  intro y _
  simp_rw [fun r (j : {j // j ≠ i}) => same r j j.2,atI]
  apply two_choices_compress
  intro r hr t ht
  exact minimal r (Finset.mem_filter.mp hr).1 t (Finset.mem_filter.mp ht).1

/-- Exact finite tensorization for any choice of required rows. The premise
for equal signs is single-set optimality, and the premise for different
signs is local two-set union optimality. -/
theorem coupledImage_optimal (rows : Finset R) (sign : R → I → Bool)
    (old : R → (j : I) → Finset (A j)) (canonical : (i : I) → Bool → Finset (A i))
    (minimal : ∀ i, ∀ r ∈ rows, ∀ t ∈ rows,
      (canonical i (sign r i) ∪ canonical i (sign t i)).card ≤ (old r i ∪ old t i).card) :
    (coupledImageBoxes rows (fun r i => canonical i (sign r i))).card ≤
      (coupledImageBoxes rows old).card := by
  classical
  let stage (s : Finset I) (r : R) (i : I) := if i∈s then canonical i (sign r i) else old r i
  have sweep (s : Finset I) : (coupledImageBoxes rows (stage s)).card ≤
      (coupledImageBoxes rows old).card := by
    induction s using Finset.induction_on with
    | empty => simp [stage]
    | @insert i s fresh ih =>
      apply le_trans _ ih
      apply coupledImage_compress_coordinate i rows (fun r => sign r i) _ _ (canonical i)
      · intro r j ji; simp [stage,ji]
      · intro r; simp [stage]
      · simpa [stage,fresh] using minimal i
  simpa [stage] using sweep Finset.univ

/-- If all sign vectors occur, the minimum retained set is a Cartesian
product, with exactly the product of the local union sizes. -/
theorem coupledImage_full_product (old : (I → Bool) → (j : I) → Finset (A j))
    (canonical : (i : I) → Bool → Finset (A i))
    (minimal : ∀ i, ∀ r t : I → Bool,
      (canonical i (r i) ∪ canonical i (t i)).card ≤ (old r i ∪ old t i).card) :
    (∏ i, (canonical i false ∪ canonical i true).card) ≤
      (coupledImageBoxes Finset.univ old).card := by
  classical
  have prod : coupledImageBoxes Finset.univ (fun (r : I → Bool) i => canonical i (r i)) =
      Fintype.piFinset (fun i => canonical i false ∪ canonical i true) := by
    ext x
    simp only [coupledImageBoxes,Finset.mem_biUnion,Finset.mem_univ,true_and,
      Fintype.mem_piFinset,Finset.mem_union]
    constructor
    · rintro ⟨r,hr⟩ i
      cases h : r i
      · exact Or.inl (h ▸ hr i)
      · exact Or.inr (h ▸ hr i)
    · intro hx
      refine ⟨fun i => if x i ∈ canonical i false then false else true,fun i => ?_⟩
      dsimp only
      split_ifs with h
      · exact h
      · exact (hx i).resolve_left h
  rw [← Fintype.card_piFinset, ← prod]
  exact coupledImage_optimal Finset.univ id old canonical (fun i r _ t _ => minimal i r t)

end Coordinates

end PrimeFactors
