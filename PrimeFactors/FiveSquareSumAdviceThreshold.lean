import PrimeFactors.FiveSquareSumCodeWidth
import PrimeFactors.CompressedSumClue

/-! If an external message can only encode the sum, its fixed width
preserves the complete sum's optimal modular rank exactly when it can
distinguish every attained sum. The encoder may use the public product. -/
namespace PrimeFactors.FiveSquareSumAdviceThreshold

open FiveSquareSignPopulation (m)
private noncomputable abbrev U := (ZMod m)ˣ
open FiveSquareSumCodeWidth (Fits)
open CompressedSumClue (cost)
open PrimeSquareSumWeights (weight)
open scoped Classical
attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card
set_option maxRecDepth 4096

/-- The compressed reporter costs exactly as many guesses as disclosing
the whole sum, averaging uniformly over the first unit at this product. -/
def Preserves (u : U) (bits : ℕ) : Prop :=
  ∃ f : ZMod m→Fin (2^bits), cost u f=cost u id

theorem preserves_iff (u : U) (bits : ℕ) : Preserves u bits ↔ Fits u.val.val bits := by
  constructor
  · rintro ⟨f,eq⟩
    have inj := (CompressedSumClue.cost_eq_iff u f).mp eq
    let encode (s : CoprimeGuessTables.Labels m u.val.val) := f s.val
    have faithful : Function.Injective encode := by
      intro a b same
      exact Subtype.ext (inj ((CoprimeGuessTables.positive_iff _).mpr a.property) ((CoprimeGuessTables.positive_iff _).mpr b.property) same)
    exact ⟨encode,Function.invFun encode,Function.leftInverse_invFun faithful⟩
  · rintro ⟨encode,decode,inv⟩
    let f (s : ZMod m) : Fin (2^bits) :=
      if h : AdmissibleSum (u.val.val:ZMod m) s then encode ⟨s,h⟩ else ⟨0,by positivity⟩
    refine ⟨f,(CompressedSumClue.cost_eq_iff u f).mpr ?_⟩
    intro s hs t ht eq
    have a := (CoprimeGuessTables.positive_iff _).mp hs
    have b := (CoprimeGuessTables.positive_iff _).mp ht
    simp only [f,dif_pos a,dif_pos b] at eq
    exact congrArg Subtype.val (inv.injective eq)

/-- 27 bits is the condition for all unit products; the code may change
with the public product. -/
theorem all_products (bits : ℕ) : (∀ u,Preserves u bits) ↔ 27≤bits := by
  simp only [preserves_iff,FiveSquareSumCodeWidth.all_units_iff]

theorem width_26 :
    ((Finset.univ : Finset U).filter (fun u => Preserves u 26)).card=1715313600 ∧
    ((Finset.univ : Finset U).filter (fun u => ¬Preserves u 26)).card=2205403200 := by
  simpa only [preserves_iff] using FiveSquareSumCodeWidth.twenty_six_counts

end PrimeFactors.FiveSquareSumAdviceThreshold
