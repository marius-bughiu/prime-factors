import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! A deterministic point-query lower bound for ordered Boolean masks. The
public information fixes the row strata and two possible count profiles.
Every assignment of bits realizing its profile is allowed. -/
namespace PrimeFactors.StratifiedPointQueryLower
open Finset

variable {C : Type*}

/-- Positions within a stratum are publicly indexed from zero. -/
def Fits (cap count : C → ℕ) (o : C → Finset ℕ) : Prop :=
  ∀ i, o i ⊆ range (cap i) ∧ (o i).card = count i

/-- A decision tree may revisit a position and can select its next query
using all answers already received. -/
inductive Tree (cap : C → ℕ) where
  | leaf (b : Bool)
  | ask (i : C) (j : Fin (cap i)) (yes no : Tree cap)

def Tree.run {cap : C → ℕ} (t : Tree cap) (o : C → Finset ℕ) : Bool × ℕ :=
  match t with
  | .leaf b => (b,0)
  | .ask i j yes no =>
    let a := if j.val ∈ o i then yes.run o else no.run o
    (a.1,a.2+1)

private structure Partial where
  yes : Finset ℕ
  no : Finset ℕ

private def Extends (s : Partial) (o : Finset ℕ) := s.yes ⊆ o ∧ Disjoint s.no o

/-- So far the answered ones fit the smaller count, and the answered zeros
leave enough room for the larger count. -/
private structure Good (s : Partial) (cap low spent : ℕ) : Prop where
  consistent : Disjoint s.yes s.no
  yesInside : s.yes ⊆ range cap
  noInside : s.no ⊆ range cap
  fewOnes : s.yes.card ≤ low
  fewZeros : s.no.card + low < cap
  readBound : s.yes.card + s.no.card ≤ spent

private theorem completion {s : Partial} {cap low spent target : ℕ}
    (h : Good s cap low spent) (bounds : low ≤ target ∧ target ≤ low+1) :
    ∃ o : Finset ℕ, o ⊆ range cap ∧ o.card = target ∧ Extends s o := by
  have sub : s.yes ⊆ range cap \ s.no := fun a ha => mem_sdiff.mpr
    ⟨h.yesInside ha,fun hno => disjoint_left.mp h.consistent ha hno⟩
  have room : target ≤ (range cap \ s.no).card := by
    rw [card_sdiff h.noInside,card_range]
    have := h.fewZeros
    omega
  obtain ⟨o,y,inside,card⟩ := exists_subsuperset_card_eq sub (h.fewOnes.trans bounds.1) room
  exact ⟨o,inside.trans sdiff_subset,card,y,disjoint_left.mpr
    (fun a hn ho => (mem_sdiff.mp (inside ho)).2 hn)⟩

private theorem record {s : Partial} {cap low spent j : ℕ} (h : Good s cap low spent)
    (inside : j < cap) (room : spent+1 < cap) :
    ∃ (b : Bool) (s' : Partial), Good s' cap low (spent+1) ∧
      ∀ o, Extends s' o → Extends s o ∧ decide (j ∈ o) = b := by
  obtain ⟨disj,ys,ns,ones,zeros,count⟩ := h
  by_cases positive : j ∉ s.no ∧ (j ∈ s.yes ∨ s.yes.card < low)
  · refine ⟨true,⟨insert j s.yes,s.no⟩,⟨disjoint_insert_left.mpr ⟨positive.1,disj⟩,
      insert_subset (mem_range.mpr inside) ys,ns,?_,zeros,?_⟩,?_⟩
    · change (insert j s.yes).card ≤ low
      rcases positive.2 with seen|space
      · rwa [card_insert_of_mem seen]
      · exact (card_insert_le ..).trans space
    · change (insert j s.yes).card + s.no.card ≤ spent+1
      have := card_insert_le j s.yes
      omega
    · intro o ext
      exact ⟨⟨(subset_insert ..).trans ext.1,ext.2⟩,
        decide_eq_true (ext.1 (mem_insert_self ..))⟩
  · have off : j ∉ s.yes := fun y => positive ⟨fun n => disjoint_left.mp disj y n,Or.inl y⟩
    refine ⟨false,⟨s.yes,insert j s.no⟩,⟨disjoint_insert_right.mpr ⟨off,disj⟩,
      ys,insert_subset (mem_range.mpr inside) ns,ones,?_,?_⟩,?_⟩
    · change (insert j s.no).card + low < cap
      by_cases seen : j ∈ s.no
      · rwa [card_insert_of_mem seen]
      · have full : s.yes.card = low := by
          by_contra! ne
          exact positive ⟨seen,Or.inr (by omega)⟩
        have := card_insert_le j s.no
        omega
    · change s.yes.card + (insert j s.no).card ≤ spent+1
      have := card_insert_le j s.no
      omega
    · intro o ext
      have neg : j ∉ o := fun h => disjoint_left.mp ext.2 (mem_insert_self ..) h
      exact ⟨⟨ext.1,ext.2.mono_left (subset_insert ..)⟩,by simp [neg]⟩

private theorem complete_all {cap low : C → ℕ} {s : C → Partial} {spent : ℕ}
    (good : ∀ i, Good (s i) (cap i) (low i) spent) {target : C → ℕ}
    (bounds : ∀ i, low i ≤ target i ∧ target i ≤ low i+1) :
    ∃ o, Fits cap target o ∧ ∀ i, Extends (s i) (o i) := by
  choose o inside card ext using (fun i => completion (good i) (bounds i))
  exact ⟨o,fun i => ⟨inside i,card i⟩,ext⟩

private theorem strategy {cap low : C → ℕ} {target : Bool → C → ℕ}
    (profiles : ∀ b i, low i ≤ target b i ∧ target b i ≤ low i + 1) (want : Bool)
    (steps : ℕ) {spent : ℕ} (tree : Tree cap) (s : C → Partial)
    (room : ∀ i, spent+steps ≤ cap i) (good : ∀ i, Good (s i) (cap i) (low i) spent)
    (correct : ∀ b o, Fits cap (target b) o → (∀ i, Extends (s i) (o i)) →
      (tree.run o).1 = b) :
    ∃ o, Fits cap (target want) o ∧ (∀ i, Extends (s i) (o i)) ∧ steps ≤ (tree.run o).2 := by
  classical
  induction steps generalizing tree s spent with
  | zero =>
    obtain ⟨o,fits,ext⟩ := complete_all good (profiles want)
    exact ⟨o,fits,ext,Nat.zero_le _⟩
  | succ n ih =>
    cases tree with
    | leaf label =>
      obtain ⟨o,fits,ext⟩ := complete_all good (profiles (!label))
      have impossible := correct (!label) o fits ext
      cases label <;> simp [Tree.run] at impossible
    | ask i j yes no =>
      by_cases last : n = 0
      · obtain ⟨o,fits,ext⟩ := complete_all good (profiles want)
        exact ⟨o,fits,ext,by simp [last,Tree.run]⟩
      have enough := room i
      obtain ⟨b,cell,next,back⟩ := record (good i) j.isLt (by omega)
      let nextState := Function.update s i cell
      have valid (u : C) : Good (nextState u) (cap u) (low u) (spent+1) := by
        by_cases eq : u=i
        · simpa [nextState,eq] using next
        · obtain ⟨d,y,z,o,f,prev⟩ := good u
          simpa [nextState,eq] using
            (show Good (s u) (cap u) (low u) (spent+1) from
              ⟨d,y,z,o,f,prev.trans (Nat.le_succ _)⟩)
      have compatible (o : C → Finset ℕ) (ext : ∀ u, Extends (nextState u) (o u)) :
          (∀ u, Extends (s u) (o u)) ∧ decide (j.val ∈ o i) = b := by
        have ⟨old,answer⟩ := back (o i) (by simpa [nextState] using ext i)
        refine ⟨fun u => ?_,answer⟩
        by_cases eq : u=i
        · simpa [eq] using old
        · simpa [nextState,eq] using ext u
      let child := if b then yes else no
      have route (o : C → Finset ℕ) (answer : decide (j.val ∈ o i) = b) :
          (Tree.ask i j yes no).run o = ((child.run o).1,(child.run o).2+1) := by
        by_cases h : j.val ∈ o i
        · have eq : b = true := by simpa [h] using answer.symm
          simp [child,Tree.run,h,eq]
        · have eq : b = false := by simpa [h] using answer.symm
          simp [child,Tree.run,h,eq]
      have childCorrect (label : Bool) (o : C → Finset ℕ) (fits : Fits cap (target label) o)
          (ext : ∀ u, Extends (nextState u) (o u)) : (child.run o).1 = label := by
        obtain ⟨old,answer⟩ := compatible o ext
        simpa only [route o answer] using correct label o fits old
      obtain ⟨o,fits,ext,cost⟩ := ih child nextState (spent:=spent+1)
        (fun u => by have := room u; omega) valid childCorrect
      obtain ⟨old,answer⟩ := compatible o ext
      exact ⟨o,fits,old,by rw [route o answer]; exact Nat.succ_le_succ cost⟩

/-- When a correct deterministic tree distinguishes the two given profiles,
each promised label admits some placement requiring at least m individual
bit queries, for any m no larger than the smallest stratum. -/
theorem worst_case {cap low : C → ℕ} {target : Bool → C → ℕ}
    (space : ∀ i, low i < cap i)
    (profiles : ∀ b i, low i ≤ target b i ∧ target b i ≤ low i+1)
    (tree : Tree cap) (correct : ∀ b o, Fits cap (target b) o → (tree.run o).1 = b)
    {m : ℕ} (bound : ∀ i, m ≤ cap i) (want : Bool) :
    ∃ o, Fits cap (target want) o ∧ m ≤ (tree.run o).2 := by
  let blank : C → Partial := fun _ => ⟨∅,∅⟩
  have good (i : C) : Good (blank i) (cap i) (low i) 0 := by
    refine ⟨by simp [blank],by simp [blank],by simp [blank],by simp [blank],?_,by simp [blank]⟩
    simpa [blank] using space i
  obtain ⟨o,fits,_,cost⟩ := strategy profiles want m tree blank (spent:=0)
    (fun i => by simpa using bound i) good (fun b a h _ => correct b a h)
  exact ⟨o,fits,cost⟩

/-- The same lower bound applies to deciding nonemptiness in a distinguished
stratum when the two promised counts there are zero and one. -/
theorem nonempty_worst_case {cap low : C → ℕ} {target : Bool → C → ℕ}
    (space : ∀ i, low i < cap i)
    (profiles : ∀ b i, low i ≤ target b i ∧ target b i ≤ low i+1)
    (i : C) (absent : target false i = 0) (present : target true i = 1)
    (tree : Tree cap) (correct : ∀ b o, Fits cap (target b) o →
      (tree.run o).1 = decide ((o i).Nonempty))
    {m : ℕ} (bound : ∀ c, m ≤ cap c) (want : Bool) :
    ∃ o, Fits cap (target want) o ∧ m ≤ (tree.run o).2 := by
  apply worst_case space profiles tree _ bound want
  intro b o fits
  rw [correct b o fits]
  have count := (fits i).2
  cases b <;> simp_all [←Finset.card_pos]

end PrimeFactors.StratifiedPointQueryLower
