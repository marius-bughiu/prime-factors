import PrimeFactors.RankWeightSeparation

/-! Exact list size for 99.9% coverage of the five-square product-one
modular population. -/
namespace PrimeFactors.FiveSquareCoverageTail

open Finset PrimeSquareSumWeights FiveSquareGuessRanks RankWeightSeparation
open scoped Classical
open private PrimeFactors.FiveSquareGuessRanks.labelFintype from PrimeFactors.FiveSquareGuessRanks
attribute [local instance 2000] PrimeFactors.FiveSquareGuessRanks.labelFintype

/-- A list covers at least 99.9% of the ordered pairs iff its omitted mass,
multiplied by a thousand, is at most the total mass. -/
noncomputable def covers (L : Finset GlobalLabels) : Prop :=
  1000*(∑ s∈Lᶜ,weight 1 s.val) ≤ ∑ s : GlobalLabels,weight 1 s.val

attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card PrimeFactors.FiveSquareGuessRanks.labelFintype

private theorem count_mass {α : Type*} [Fintype α] (w : α→ℕ) {c : ℕ}
    (h : (∑ s, if w s=32 then 1 else 0)=c) :
    (univ.filter (fun s => w s=32)).card=c := by
  simpa only [sum_boole,Nat.cast_id] using h

private theorem smallest_count :
    (univ.filter (fun s : GlobalLabels => weight 1 s.val=32)).card=23823800 := by
  have eq := global_histogram (fun w => if w=32 then 1 else 0)
  have checked : compressed [5,7,11,13,17] (fun w => if w=32 then 1 else 0)=23823800 := by decide +kernel
  exact count_mass (fun s : GlobalLabels => weight 1 s.val) (eq.trans checked)

private theorem exact_coverage {α : Type*} [Fintype α] [DecidableEq α] (w : α→ℕ)
    (count : Fintype.card α=41767264) (total : (∑ x,w x)=3920716800)
    (floor : ∀ x,32≤w x) (many : 122522 ≤ (univ.filter (fun x => w x=32)).card) :
    (∀ L : Finset α,1000*(∑ x∈Lᶜ,w x)≤∑ x,w x → 41644742≤L.card) ∧
    ∃ L : Finset α, L.card=41644742 ∧ 1000*(∑ x∈Lᶜ,w x)≤∑ x,w x := by
  constructor
  · intro L ok
    have lo := sum_le_sum (s:=Lᶜ) (fun x _ => floor x)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at lo
    have cards := card_compl_add_card L
    rw [count] at cards
    rw [total] at ok
    omega
  · obtain ⟨D,subset,size⟩ := exists_subset_card_eq many
    refine ⟨Dᶜ,?_,?_⟩
    · have cards := card_compl_add_card D
      omega
    · rw [compl_compl,total,sum_congr rfl (fun x hx => (mem_filter.mp (subset hx)).2)]
      simp only [sum_const,nsmul_eq_mul,size]
      decide

/-- 41,644,742 is the minimum number of labels that cover at least
999/1000 of the actual modular pair mass. -/
theorem optimal : (∀ L : Finset GlobalLabels, covers L → 41644742≤L.card) ∧
    ∃ L : Finset GlobalLabels, L.card=41644742 ∧ covers L :=
  exact_coverage _ label_count total_weight
    (fun s => (by decide +kernel : ∀ n∈fiveWeights,32≤n) _ (five_supported s))
    (smallest_count.ge.trans' (by decide : 122522≤23823800))

end PrimeFactors.FiveSquareCoverageTail
