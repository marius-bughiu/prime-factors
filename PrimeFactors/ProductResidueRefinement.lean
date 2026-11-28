import PrimeFactors.PooledFactorOrbitRanks
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.ZMod.Units

/-! A finer public product in a finite group gives no improvement in the
optimal rank of either factor residue in a quotient group, when the original
pair is drawn uniformly from the finer group. -/
namespace PrimeFactors.ProductResidueRefinement

open Finset FactorOrbitGuessRanks
open scoped Classical

variable {H G : Type*} [CommGroup H] [CommGroup G] [Fintype H] [Fintype G]
variable (π : H →* G) (onto : Function.Surjective π)

omit [Fintype G] in
include onto in
/-- For each public product h and projected first factor g, exactly this
many choices of a∈H produce the pair (a,h/a) with first projection g. -/
theorem fiber_count (g : G) : (univ.filter (fun a : H => π a=g)).card=Fintype.card π.ker := by
  have e := MonoidHom.fiberEquivKerOfSurjective onto g
  exact (Fintype.card_subtype (fun a : H => π a=g)).symm.trans (Fintype.card_congr e)

omit [Fintype H] [Fintype G] in
/-- The public product also determines which coarse residue partners g. -/
theorem partner (h a : H) : π (h/a)=π h/π a := map_div π h a

include onto in
/-- Every statistic on coarse residues is repeated once per kernel element. -/
theorem sum_pullback {A : Type*} [AddCommMonoid A] (f : G→A) :
    (∑ a : H,f (π a))=Fintype.card π.ker • (∑ g : G,f g) := by
  have eq := sum_fiberwise_of_maps_to' (s:=(univ : Finset H)) (t:=(univ : Finset G))
    (g:=fun a => π a) (fun _ _ => mem_univ _) f
  simpa only [sum_const,fiber_count π onto,←Finset.smul_sum] using eq.symm

include onto in
private theorem population : Fintype.card H=Fintype.card π.ker*Fintype.card G := by
  simpa only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_one] using sum_pullback π onto (fun _ => (1:ℕ))

include onto in
/-- The normalized distribution of π(a) is precisely uniform on G. -/
theorem mean_pullback (f : G→ℚ) : (∑ a : H,f (π a))/(Fintype.card H:ℚ)=
    (∑ g : G,f g)/(Fintype.card G:ℚ) := by
  have pos : (0:ℚ)<Fintype.card π.ker := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card π.ker)
  rw [sum_pullback π onto,population π onto,Nat.cast_mul,nsmul_eq_mul,mul_div_mul_left _ _ pos.ne']

/-- If the full product h is fixed and a is uniform, this is the inclusive
guess rank of either projected factor under one complete order. -/
noncomputable def conditional (h : H) (order : Order (π h)) : ℚ :=
  ((∑ a : H, ((order (label (π h) (π a))).val+1) : ℕ):ℚ)/Fintype.card H

include onto in
theorem conditional_mean (h : H) (order : Order (π h)) :
    conditional π h order=mean (π h) order := by
  simpa only [conditional,mean,Nat.cast_sum,Nat.cast_add,Nat.cast_one] using
    mean_pullback π onto (fun a : G => ((order (label (π h) a)).val:ℚ)+1)

include onto in
/-- Already at each individual refined product, the minimum equals the
original optimum for its projection. -/
theorem conditional_optimum (h : H) : IsLeast (Set.range (conditional π h)) (optimum (π h)) := by
  rw [show conditional π h=mean (π h) from funext (conditional_mean π onto h)]
  exact optimal _

abbrev Policy := ∀ h : H, Order (π h)
noncomputable def pooled (P : Policy π) : ℚ := (∑ h,conditional π h (P h))/Fintype.card H

include onto in
/-- A policy that can choose its entire order from the finer product has
exactly the same optimal average as a policy using only the coarse product.
An optimal coarse policy attains equality by composition with π. -/
theorem pooled_optimum : IsLeast (Set.range (pooled π)) ((∑ g : G,optimum g)/Fintype.card G) := by
  choose e best using fun g : G => (optimal g).1
  rw [←mean_pullback π onto optimum]
  constructor
  · refine ⟨fun h => e (π h),?_⟩
    simp only [pooled,conditional_mean π onto,best]
  · rintro _ ⟨P,rfl⟩
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact sum_le_sum (fun h _ => ((conditional_optimum π onto h).2 ⟨P h,rfl⟩))

/-- Reduction of unit residues from any positive multiple d of the coarse
modulus m gives the explicit original mean, including all fine products. -/
theorem units_reduction {m d : ℕ} [NeZero m] [NeZero d] (div : m∣d) :
    IsLeast (Set.range (pooled (ZMod.unitsMap div)))
      ((Fintype.card (ZMod m)ˣ:ℚ)/4+1/2+fixed (1:(ZMod m)ˣ)/(4*Fintype.card (ZMod m)ˣ)) := by
  rw [←PooledFactorOrbitRanks.optimal_mean (ZMod m)ˣ]
  exact pooled_optimum _ (ZMod.unitsMap_surjective div)

end PrimeFactors.ProductResidueRefinement
