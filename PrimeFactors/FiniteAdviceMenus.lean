import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod

/-! A finite choice of menus, each with a bound on its number of trials.
The upper bound permits a clue depending on the entire input. Attainment
allows the clue to identify the block containing the correct label. -/
namespace PrimeFactors.FiniteAdviceMenus

open Finset

variable {Ω α : Type*} [DecidableEq α] {K B : ℕ}

/-- Pool the menus. Every success of any input-dependent clue is retained. -/
theorem upper (label : Ω→α) (menus : Fin K→Finset α) (clue : Ω→Fin K)
    (budget : ∀ i,(menus i).card≤B) :
    ∃ S : Finset α, S.card≤K*B ∧ ∀ x,label x∈menus (clue x) → label x∈S := by
  refine ⟨univ.biUnion menus,?_,fun x hit => mem_biUnion.mpr ⟨clue x,mem_univ _,hit⟩⟩
  simpa using card_biUnion_le_card_mul (univ : Finset (Fin K)) menus B (fun i _ => budget i)

/-- Partition any eligible list into K menus of capacity B. The clue uses
the true label to choose its menu. Every hit and miss of the list is preserved. -/
theorem realize (pos : 0<K) (label : Ω→α) (S : Finset α) (budget : S.card≤K*B) :
    ∃ menus : Fin K→Finset α, ∃ clue : Ω→Fin K,
      (∀ i,(menus i).card≤B) ∧ ∀ x,label x∈menus (clue x) ↔ label x∈S := by
  classical
  obtain ⟨slot⟩ : Nonempty (↥S ↪ Fin K×Fin B) := Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using budget)
  let row (i : Fin K) := S.attach.filter (fun a => (slot a).1=i)
  let menus (i : Fin K) := (row i).image Subtype.val
  let clue (x : Ω) : Fin K := if h : label x∈S then (slot ⟨label x,h⟩).1 else ⟨0,pos⟩
  refine ⟨menus,clue,?_,?_⟩
  · intro i
    have capacity : (row i).card≤(univ : Finset (Fin B)).card := by
      apply card_le_card_of_injOn (fun a => (slot a).2) (fun _ _ => mem_univ _)
      intro a ha b hb eq
      exact slot.injective (Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm) eq)
    exact card_image_le.trans (by simpa only [card_univ,Fintype.card_fin] using capacity)
  · intro x
    constructor
    · intro hit
      obtain ⟨a,_,ha⟩ := mem_image.mp hit
      exact ha ▸ a.property
    · intro hit
      apply mem_image.mpr
      exact ⟨⟨label x,hit⟩,mem_filter.mpr ⟨mem_attach _ _,by simp [clue,hit]⟩,rfl⟩

/-- The attaining clue need only consult the true label. Composing this
selector with the input label works for any population. -/
theorem realize_by_label (pos : 0<K) (S : Finset α) (budget : S.card≤K*B) :
    ∃ menus : Fin K→Finset α, ∃ pick : α→Fin K,
      (∀ i,(menus i).card≤B) ∧ ∀ a,a∈menus (pick a) ↔ a∈S :=
  realize pos id S budget

/-- The best count on a finite population is attained equally by a
single larger list and by freely chosen clue-dependent menus. -/
theorem optimal (pos : 0<K) (pop : Finset Ω) (label : Ω→α) (h : ℕ)
    (best : IsGreatest {n : ℕ | ∃ S : Finset α,S.card≤K*B ∧
      n=(pop.filter (fun x => label x∈S)).card} h) :
    IsGreatest {n : ℕ | ∃ menus : Fin K→Finset α, ∃ clue : Ω→Fin K,
      (∀ i,(menus i).card≤B) ∧ n=(pop.filter (fun x => label x∈menus (clue x))).card} h := by
  constructor
  · obtain ⟨S,budget,hit⟩ := best.1
    obtain ⟨menus,clue,small,same⟩ := realize pos label S budget
    refine ⟨menus,clue,small,?_⟩
    simpa only [same] using hit
  · rintro _ ⟨menus,clue,small,rfl⟩
    obtain ⟨S,budget,cover⟩ := upper label menus clue small
    have sub : pop.filter (fun x => label x∈menus (clue x)) ⊆ pop.filter (fun x => label x∈S) := by
      intro x hit
      exact mem_filter.mpr ⟨(mem_filter.mp hit).1,cover x (mem_filter.mp hit).2⟩
    exact (card_le_card sub).trans (best.2 ⟨S,budget,rfl⟩)

end PrimeFactors.FiniteAdviceMenus
