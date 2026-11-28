import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-! Extending labels on a finite ordered layer to a monotone predictor.
Summing a uniform prediction bound then controls any finite union of layers. -/

namespace PrimeFactors.MonotoneSumExtension

open Finset

variable {α ι : Type*}

/-- Equal inputs in a layer must also have equal labels. -/
def OrderedOn (A : Finset α) (input value : α → ℕ) : Prop :=
  ∀ x∈A, ∀ y∈A, input x ≤ input y → value x ≤ value y

/-- Maximum label observed up to n, with zero before the first observation. -/
noncomputable def extend (A : Finset α) (input value : α → ℕ) (n : ℕ) : ℕ :=
  (A.filter fun x => input x≤n).sup value

theorem monotone_extend (A : Finset α) (input value : α → ℕ) :
    Monotone (extend A input value) := by
  intro m n mn
  apply sup_mono
  intro x hx
  exact mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.trans mn⟩

theorem agrees {A : Finset α} {input value : α → ℕ} (ordered : OrderedOn A input value)
    {x : α} (hx : x∈A) : extend A input value (input x)=value x := by
  apply le_antisymm (Finset.sup_le fun y hy =>
    ordered y (mem_filter.mp hy).1 x hx (mem_filter.mp hy).2)
  exact le_sup (mem_filter.mpr ⟨hx,le_rfl⟩)

/-- Being ordered is exactly the condition for the labels to admit a total extension. -/
theorem ordered_iff_exists (A : Finset α) (input value : α → ℕ) :
    OrderedOn A input value ↔ ∃ g : ℕ → ℕ, Monotone g ∧ ∀ x∈A, g (input x)=value x := by
  constructor
  · exact fun h => ⟨extend A input value,monotone_extend ..,fun _ hx => agrees h hx⟩
  · rintro ⟨g,mono,match'⟩ x hx y hy xy
    rw [←match' x hx,←match' y hy]
    exact mono xy

/-- Members of the ambient population on which the predictor is exact. -/
noncomputable def exactHits (P : Finset α) (input value : α → ℕ) (g : ℕ → ℕ) : Finset α :=
  P.filter fun x => g (input x)=value x

theorem subset_hits {A P : Finset α} {input value : α → ℕ} (sub : A⊆P)
    (ordered : OrderedOn A input value) : A⊆exactHits P input value (extend A input value) :=
  fun _ hx => mem_filter.mpr ⟨sub hx,agrees ordered hx⟩

variable [DecidableEq α] {P : Finset α} {input value : α → ℕ}

private theorem scaled_sum (I : Finset ι) (layer : ι → Finset α) (D : ℕ) :
    D*(I.biUnion layer).card≤∑ i∈I,D*(layer i).card := by
  rw [←mul_sum]
  exact Nat.mul_le_mul_left _ card_biUnion_le

theorem scaled_union_le (I : Finset ι) (layer : ι → Finset α) {D M : ℕ}
    (inside : ∀ i∈I, layer i⊆P) (ordered : ∀ i∈I, OrderedOn (layer i) input value)
    (cap : ∀ g : ℕ → ℕ, Monotone g → D*(exactHits P input value g).card≤M) :
    D*(I.biUnion layer).card≤I.card*M := by
  calc
    _ ≤ ∑ i∈I,D*(layer i).card := scaled_sum I layer D
    _ ≤ ∑ _i∈I,M := sum_le_sum fun i hi =>
      (Nat.mul_le_mul_left D (card_le_card (subset_hits (inside i hi) (ordered i hi)))).trans
        (cap _ (monotone_extend ..))
    _ = _ := by simp

theorem union_le (I : Finset ι) (layer : ι → Finset α) {M : ℕ}
    (inside : ∀ i∈I, layer i⊆P) (ordered : ∀ i∈I, OrderedOn (layer i) input value)
    (cap : ∀ g : ℕ → ℕ, Monotone g → (exactHits P input value g).card≤M) :
    (I.biUnion layer).card≤I.card*M := by
  simpa only [one_mul] using scaled_union_le I layer (D:=1) inside ordered
    (fun g hg => by simpa only [one_mul] using cap g hg)

/-- A strict fractional bound per predictor remains strict for a nonempty menu. -/
theorem scaled_union_lt (I : Finset ι) (nonempty : I.Nonempty) (layer : ι → Finset α) {D M : ℕ}
    (inside : ∀ i∈I, layer i⊆P) (ordered : ∀ i∈I, OrderedOn (layer i) input value)
    (cap : ∀ g : ℕ → ℕ, Monotone g → D*(exactHits P input value g).card<M) :
    D*(I.biUnion layer).card<I.card*M := by
  calc
    _ ≤ ∑ i∈I,D*(layer i).card := scaled_sum I layer D
    _ < ∑ _i∈I,M := sum_lt_sum_of_nonempty nonempty fun i hi =>
      (Nat.mul_le_mul_left D (card_le_card (subset_hits (inside i hi) (ordered i hi)))).trans_lt
        (cap _ (monotone_extend ..))
    _ = _ := by simp

end PrimeFactors.MonotoneSumExtension
