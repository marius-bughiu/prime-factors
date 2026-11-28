import PrimeFactors.FactorOrbitAdviceConstruction
import PrimeFactors.FactorOrbitAdviceFloor
import Mathlib.Logic.Equiv.Fintype

/-! Complete orders for bounded advice. An adviser selects one of B full
lists before guessing starts. A list can put every position congruent to
its message first, in the base order. Unused messages can repeat a list. -/
namespace PrimeFactors.FactorOrbitAdviceMenu

open FactorOrbitGuessRanks FactorOrbitAdviceFloor
open FactorOrbitAdviceConstruction (code advised)
open scoped Classical

private theorem reorder {B k : ℕ} (positive : 0<B) (b : Fin B) :
    ∃ perm : Equiv.Perm (Fin k), ∀ i : Fin k, code positive i=b → (perm i).val=i.val/B := by
  let belongs (i : Fin k) := code positive i=b
  let shorten (i : {i : Fin k // belongs i}) : Fin k :=
    ⟨i.val.val/B,(Nat.div_le_self _ _).trans_lt i.val.isLt⟩
  have inj : Function.Injective shorten := by
    intro x y eq
    have quotient : x.val.val/B=y.val.val/B := congrArg Fin.val eq
    have remainder : x.val.val%B=y.val.val%B := congrArg Fin.val (x.property.trans y.property.symm)
    apply Subtype.ext
    apply Fin.ext
    calc
      _ = x.val.val%B+B*(x.val.val/B) := (Nat.mod_add_div ..).symm
      _ = y.val.val%B+B*(y.val.val/B) := by rw [quotient,remainder]
      _ = _ := Nat.mod_add_div ..
  let e := Equiv.ofInjective shorten inj
  refine ⟨e.extendSubtype,fun i hi => ?_⟩
  rw [e.extendSubtype_apply_of_mem i hi]
  rfl

variable {G : Type*} [CommGroup G] [Fintype G]

/-- The strided hint can be used with precisely the complete-menu model
of the rank lower bound. Ranks agree for every base policy and hidden pair. -/
theorem realizes {B : ℕ} (positive : 0<B) (P : FiveSquareFactorGuessing.PolicyFor G) :
    ∃ menu : ∀ n : G, Menu n B, ∀ a b : G,
      rank (menu (a*b)) (code positive ((P (a*b)) (label (a*b) a)).val) a = advised B P a b := by
  choose perm good using fun (n : G) (c : Fin B) => reorder (k:=Fintype.card (Label n)) positive c
  refine ⟨fun n c => (P n).trans (perm n c),fun a b => ?_⟩
  let i := (P (a*b)) (label (a*b) a)
  change (perm (a*b) (code positive i.val) i).val+1=(i.val+1-1)/B+1
  rw [good _ _ _ rfl,Nat.add_sub_cancel]

/-- Padding a smaller, nonempty alphabet preserves every selected rank. -/
theorem pad {B C : ℕ} (positive : 0<B) (le : B≤C) {n : G} (P : Menu n B) :
    ∃ Q : Menu n C, ∀ b a, rank Q (Fin.castLE le b) a=rank P b a := by
  let select (i : Fin C) : Fin B := if h : i.val<B then ⟨i.val,h⟩ else ⟨0,positive⟩
  refine ⟨fun i => P (select i),fun b a => ?_⟩
  have eq : select (Fin.castLE le b)=b := by simp [select,b.isLt]
  change ((P (select (Fin.castLE le b))) (label n a)).val+1=_
  rw [eq]
  rfl

end PrimeFactors.FactorOrbitAdviceMenu
