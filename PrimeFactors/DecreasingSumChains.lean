import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

/-! The finite chain–antichain partition by longest chain length, specialized
to increasing products and decreasing sums. -/

namespace PrimeFactors.DecreasingSumChains

open Finset
open scoped Classical

variable {α : Type*}

/-- Earlier in the chain means a smaller product and a strictly larger sum. -/
def Before (n s : α → ℕ) (a b : α) : Prop := n a < n b ∧ s b < s a

/-- All entries come from the given set, and every earlier entry precedes
every later entry. -/
def ChainIn (A : Finset α) (n s : α → ℕ) (xs : List α) : Prop :=
  xs.Pairwise (Before n s) ∧ ∀ a ∈ xs, a ∈ A

/-- A strict product increase rules out repeated entries in a chain. -/
theorem nodup {A : Finset α} {n s : α → ℕ} {xs : List α} (h : ChainIn A n s xs) :
    xs.Nodup := h.1.imp (fun {a b} h eq => by subst b; exact (lt_irrefl _ h.1))

/-- Either there is a chain of more than L points, or the points admit L
colors with weakly increasing sums inside each color at distinct products.
The color of a point counts the longest possible tail following that point. -/
theorem chain_or_coloring (A : Finset α) (n s : α → ℕ) (L : ℕ) :
    (∃ xs, L<xs.length ∧ ChainIn A n s xs) ∨
      ∃ color : α → ℕ, (∀ a ∈ A, color a < L) ∧
        ∀ a ∈ A, ∀ b ∈ A, color a=color b → n a<n b → s a≤s b := by
  classical
  by_cases long : ∃ xs, L<xs.length ∧ ChainIn A n s xs
  · exact Or.inl long
  right
  have bounded {xs : List α} (h : ChainIn A n s xs) : xs.length ≤ L := by
    by_contra! lt
    exact long ⟨xs, lt, h⟩
  let tail (a : α) (k : ℕ) := ∃ xs : List α, xs.length=k ∧ ChainIn A n s (a::xs)
  let color (a : α) := Nat.findGreatest (tail a) L
  have attains (a : α) (ha : a∈A) : tail a (color a) := by
    apply Nat.findGreatest_spec (m:=0) (Nat.zero_le _)
    exact ⟨[], rfl, by simp [ChainIn,ha]⟩
  have small (a : α) (ha : a∈A) : color a<L := by
    obtain ⟨xs, size, chain⟩ := attains a ha
    have bound := bounded chain
    simp only [List.length_cons,size] at bound
    omega
  refine ⟨color, small, ?_⟩
  intro a ha b hb same inc
  by_contra! dec
  have step : Before n s a b := ⟨inc, dec⟩
  obtain ⟨xs, size, chain⟩ := attains b hb
  have longer : tail a (color b+1) := by
    refine ⟨b::xs, by simp [size], List.pairwise_cons.mpr ⟨?_, chain.1⟩, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact step
      · have prev := (List.pairwise_cons.mp chain.1).1 x hx
        exact ⟨step.1.trans prev.1, prev.2.trans step.2⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact chain.2 _ hx
  have more : color b+1 ≤ color a := Nat.le_findGreatest (small b hb) longer
  omega

/-- The color fibers cover A and are monotone for
strictly ordered products. An empty A also admits the cover with L=0. -/
theorem chain_or_layers (A : Finset α) (n s : α → ℕ) (L : ℕ) :
    (∃ xs, L<xs.length ∧ ChainIn A n s xs) ∨
      ∃ layer : Fin L → Finset α, A=univ.biUnion layer ∧
        ∀ i, ∀ a ∈ layer i, ∀ b ∈ layer i, n a<n b → s a≤s b := by
  classical
  rcases chain_or_coloring A n s L with long | ⟨c, small, ordered⟩
  · exact Or.inl long
  right
  let layer (i : Fin L) := A.filter (fun a => c a=i.val)
  refine ⟨layer, ?_, ?_⟩
  · ext a
    constructor
    · intro ha
      exact mem_biUnion.mpr ⟨(⟨c a, small a ha⟩ : Fin L), mem_univ _, mem_filter.mpr ⟨ha,rfl⟩⟩
    · intro h
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp h
      exact (mem_filter.mp hi).1
  · intro i a ha b hb
    obtain ⟨ai, ac⟩ := mem_filter.mp ha
    obtain ⟨bi, bc⟩ := mem_filter.mp hb
    exact ordered a ai b bi (ac.trans bc.symm)

/-- When products uniquely label the points of A, each layer is
weakly monotone even when non-strict product comparisons are requested. -/
theorem chain_or_ordered_layers (A : Finset α) (n s : α → ℕ) (L : ℕ)
    (unique : (A : Set α).InjOn n) :
    (∃ xs, L<xs.length ∧ ChainIn A n s xs) ∨
      ∃ layer : Fin L → Finset α, A=univ.biUnion layer ∧
        ∀ i, ∀ a ∈ layer i, ∀ b ∈ layer i, n a≤n b → s a≤s b := by
  classical
  rcases chain_or_layers A n s L with long | ⟨layer, cover, ordered⟩
  · exact Or.inl long
  right
  refine ⟨layer, cover, ?_⟩
  intro i a ha b hb h
  rcases h.lt_or_eq with lt | eq
  · exact ordered i a ha b hb lt
  · have inside {x : α} (mem : x ∈ layer i) : x ∈ A :=
      cover ▸ mem_biUnion.mpr ⟨i, mem_univ _, mem⟩
    exact le_of_eq (congrArg s (unique (inside ha) (inside hb) eq))

end PrimeFactors.DecreasingSumChains
