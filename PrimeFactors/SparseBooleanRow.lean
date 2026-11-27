import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Isolate one signature in a finite Boolean histogram by conditioning on
at most the base-two logarithm of its support size. The tests determining a
signature and its multiplicity are those of Mazumdar and Pal, *Support
Recovery in Mixture Models With Sparse Parameters*, Algorithm 1. -/

namespace PrimeFactors.SparseBooleanRow

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- Signatures are the sets of coordinates on which the test returns one. -/
def Agrees (fixed x y : Finset ι) : Prop := ∀ i ∈ fixed, (i ∈ x ↔ i ∈ y)

/-- Only the restriction of the distinguished signature to the fixed coordinates is used. -/
def Isolates (rows : Finset (Finset ι)) (fixed x : Finset ι) : Prop :=
  x ∈ rows ∧ ∀ y ∈ rows, Agrees fixed y x → y = x

private def branch (rows : Finset (Finset ι)) (i : ι) (b : Bool) :=
  rows.filter (fun x => (i ∈ x ↔ b = true))

private theorem halve (rows : Finset (Finset ι)) (many : 1 < rows.card) :
    ∃ i b, (branch rows i b).Nonempty ∧ 2 * (branch rows i b).card ≤ rows.card := by
  obtain ⟨x,y,hx,hy,ne⟩ := one_lt_card_iff.mp many
  have diff : ∃ i, ¬(i ∈ x ↔ i ∈ y) := by
    by_contra! agree
    exact ne (Finset.ext agree)
  obtain ⟨i,hi⟩ := diff
  have ht : (branch rows i true).Nonempty := by
    by_cases h : i ∈ x
    · exact ⟨x, by simp [branch,hx,h]⟩
    · have hyi : i ∈ y := by tauto
      exact ⟨y, by simp [branch,hy,hyi]⟩
  have hf : (branch rows i false).Nonempty := by
    by_cases h : i ∈ x
    · have hyi : i ∉ y := by tauto
      exact ⟨y, by simp [branch,hy,hyi]⟩
    · exact ⟨x, by simp [branch,hx,h]⟩
  have partition : (branch rows i true).card + (branch rows i false).card = rows.card := by
    simpa [branch] using rows.filter_card_add_filter_neg_card_eq_card (fun x => i ∈ x)
  by_cases h : 2 * (branch rows i true).card ≤ rows.card
  · exact ⟨i,true,ht,h⟩
  · exact ⟨i,false,hf,by omega⟩

/-- Among any nonempty support of distinct signatures there is a signature isolated
by at most `floor(log₂(cardinality))` coordinates, regardless of its multiplicity. -/
theorem exists_isolating (rows : Finset (Finset ι)) (ne : rows.Nonempty) :
    ∃ fixed x, fixed.card ≤ rows.card.log2 ∧ Isolates rows fixed x := by
  induction rows using Finset.strongInductionOn with
  | _ rows ih =>
    by_cases small : rows.card ≤ 1
    · obtain ⟨x,hx⟩ := ne
      exact ⟨∅,x,by simp,hx,fun y hy _ => card_le_one.mp small _ hy _ hx⟩
    · obtain ⟨i,b,hn,half⟩ := halve rows (by omega)
      let sub := branch rows i b
      have subpos : 0 < sub.card := card_pos.mpr hn
      have lt : sub.card < rows.card := by change 2*sub.card ≤ rows.card at half; omega
      have proper : sub ⊂ rows := Finset.ssubset_iff_subset_ne.mpr
        ⟨filter_subset .., fun eq => lt.ne (congrArg card eq)⟩
      obtain ⟨fixed,x,size,hx,unique⟩ := ih sub proper hn
      have logle : sub.card.log2 + 1 ≤ rows.card.log2 := by
        apply (Nat.le_log2 (card_pos.mpr ne).ne').mpr
        rw [pow_succ, Nat.mul_comm]
        exact (Nat.mul_le_mul_left 2 (Nat.log2_self_le subpos.ne')).trans half
      obtain ⟨xm,xb⟩ := mem_filter.mp hx
      refine ⟨insert i fixed, x, (card_insert_le ..).trans (by omega), xm, ?_⟩
      intro y hy agrees
      have side := agrees i (mem_insert_self ..)
      exact unique y (mem_filter.mpr ⟨hy,side.trans xb⟩)
        (fun j hj => agrees j (mem_insert_of_mem hj))

/-- The weighted count of a mixed assignment. `ones` must occur and `zeros` must be absent. -/
noncomputable def count (rows : Finset (Finset ι)) (weight : Finset ι → ℕ) (ones zeros : Finset ι) : ℕ :=
  ∑ y ∈ rows.filter (fun y => ones ⊆ y ∧ Disjoint zeros y), weight y

private theorem matches_iff {fixed x y : Finset ι} :
    fixed ∩ x ⊆ y ∧ Disjoint (fixed \ x) y ↔ Agrees fixed y x := by
  rw [Finset.disjoint_left]
  simp only [Agrees, Finset.subset_iff, mem_inter, mem_sdiff]
  constructor
  · rintro ⟨yes,no⟩ i hi
    exact ⟨fun hy => by_contra (fun hx => no ⟨hi,hx⟩ hy), fun hx => yes ⟨hi,hx⟩⟩
  · intro agree
    exact ⟨fun _ h => (agree _ h.1).mpr h.2, fun _ h hy => h.2 ((agree _ h.1).mp hy)⟩

private theorem count_insert (rows : Finset (Finset ι)) (weight : Finset ι → ℕ)
    (ones zeros : Finset ι) (i : ι) :
    count rows weight (insert i ones) zeros =
      ∑ y ∈ (rows.filter fun y => ones ⊆ y ∧ Disjoint zeros y).filter (fun y => i ∈ y), weight y := by
  unfold count
  congr 1
  ext y
  simp [insert_subset_iff]
  tauto

/-- The unextended query gives the multiplicity. Requiring one more coordinate
to be one gives that same multiplicity exactly at the one bits and zero elsewhere. -/
theorem read_isolated {rows : Finset (Finset ι)} {fixed x : Finset ι}
    (iso : Isolates rows fixed x) (weight : Finset ι → ℕ) :
    count rows weight (fixed ∩ x) (fixed \ x) = weight x ∧
    ∀ i, count rows weight (insert i (fixed ∩ x)) (fixed \ x) =
      if i ∈ x then weight x else 0 := by
  have cell : rows.filter (fun y => fixed ∩ x ⊆ y ∧ Disjoint (fixed \ x) y) = {x} := by
    ext y
    simp only [mem_filter, mem_singleton, matches_iff]
    exact ⟨fun h => iso.2 y h.1 h.2, fun h => h.symm ▸ ⟨iso.1, fun _ _ => Iff.rfl⟩⟩
  constructor
  · simp [count, cell]
  · intro i
    rw [count_insert, cell]
    rw [Finset.filter_singleton]
    by_cases hi : i ∈ x <;> simp [hi]

/-- A positive mixed cell can be recognized as one signature using only its counts.
The bits are exactly the extensions with positive count. -/
theorem recognize {rows : Finset (Finset ι)} {weight : Finset ι → ℕ} {ones zeros : Finset ι}
    (positive : ∀ y ∈ rows, 0 < weight y) (hit : 0 < count rows weight ones zeros)
    (pure : ∀ i, count rows weight (insert i ones) zeros = 0 ∨
      count rows weight (insert i ones) zeros = count rows weight ones zeros) :
    ∃ x, rows.filter (fun y => ones ⊆ y ∧ Disjoint zeros y) = {x} ∧
      weight x = count rows weight ones zeros ∧
      ∀ i, (i ∈ x ↔ 0 < count rows weight (insert i ones) zeros) := by
  let cell := rows.filter (fun y => ones ⊆ y ∧ Disjoint zeros y)
  have live : cell.Nonempty := by
    by_contra hn
    have empty := not_nonempty_iff_eq_empty.mp hn
    change 0 < ∑ y ∈ cell, weight y at hit
    simp [empty] at hit
  have bits {y} (hy : y ∈ cell) (i : ι) :
      i ∈ y ↔ 0 < count rows weight (insert i ones) zeros := by
    have wy := positive y (mem_filter.mp hy).1
    have h := pure i
    rw [count_insert] at h ⊢
    change (∑ z ∈ cell.filter (fun z => i ∈ z), weight z) = 0 ∨
      (∑ z ∈ cell.filter (fun z => i ∈ z), weight z) = ∑ z ∈ cell, weight z at h
    have split := cell.sum_filter_add_sum_filter_not (fun z => i ∈ z) weight
    constructor
    · intro yes
      exact wy.trans_le (single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.mpr ⟨hy,yes⟩))
    · intro yes
      by_contra no
      have opp : 0 < ∑ z ∈ cell.filter (fun z => i ∉ z), weight z :=
        wy.trans_le (single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.mpr ⟨hy,no⟩))
      change 0 < ∑ z ∈ cell.filter (fun z => i ∈ z), weight z at yes
      omega
  obtain ⟨x,hx⟩ := live
  have singleton : cell = {x} := by
    ext y
    rw [mem_singleton]
    exact ⟨fun hy => Finset.ext (fun i => (bits hy i).trans (bits hx i).symm), fun h => h ▸ hx⟩
  refine ⟨x,singleton,?_,bits hx⟩
  change weight x = ∑ y ∈ cell, weight y
  simp [singleton]

end PrimeFactors.SparseBooleanRow
