import PrimeFactors.FiveSquarePolicy
import PrimeFactors.SquareFiberMoments

/-! The kernel of squaring on units modulo the product of the five prime
squares. Every local square root of one contributes one independent sign. -/
namespace PrimeFactors.FiveSquareOrbitKernel

open Finset PrimeSquareSumWeights FiveSquareGuessRanks
open FiveSquarePrimeSupply (m)
open FiveSquarePolicy (U)
open scoped Classical
set_option maxRecDepth 4096
open private PrimeFactors.CoprimeGuessTables.coprime from PrimeFactors.CoprimeGuessTables

private def sqrtOneEquiv (R : Type*) [CommMonoid R] :
    {u : Rˣ // u^2=1} ≃ {x : R // x^2=1} where
  toFun u := ⟨u.val.val,by simpa using congrArg Units.val u.property⟩
  invFun x := by
    have self : x.val*x.val=1 := by simpa only [sq] using x.property
    refine ⟨⟨x.val,x.val,self,self⟩,Units.ext ?_⟩
    simpa only [Units.val_pow_eq_pow_val,Units.val_one] using x.property
  left_inv u := Subtype.ext (Units.ext rfl)
  right_inv x := Subtype.ext rfl

private theorem local_one (i : Fin 5) : weight 0 (1:ZMod ((primes i)^2))=2 := by
  have odd : primes i≠2 := (by decide +kernel : ∀ j,primes j≠2) i
  haveI : Fact (1<(primes i)^2) := ⟨(by decide +kernel : ∀ j,1<(primes j)^2) i⟩
  apply regular_weight odd
  · simp
  · exact ⟨0,1,by simp,by simp⟩

private theorem count_roots {G : Type*} [CommGroup G] [Fintype G] (g : G) :
    SquareFiberMoments.roots g=Nat.card {u : G // u^2=g} := by
  classical
  simp only [SquareFiberMoments.roots,Nat.card_eq_fintype_card,Fintype.card_subtype]

private theorem factor_ones {ι : Type*} [Fintype ι] (d : ι→ℕ)
    (cop : Pairwise (fun i j => (d i).Coprime (d j))) :
    weight 0 (1:ZMod (∏ i,d i)) = ∏ i,weight 0 (1:ZMod (d i)) := by
  have one (i : ι) : (ZMod.prodEquivPi d cop 1) i=1 := congrFun (map_one (ZMod.prodEquivPi d cop)) i
  simpa only [one] using CoprimeGuessTables.weight_pi d cop 0 (1:ZMod (∏ i,d i))

theorem count : SquareFiberMoments.roots (1:U)=32 := by
  have fibre := count_roots (1:U)
  have two : IsUnit (2:ZMod m) := (ZMod.isUnit_iff_coprime 2 m).mpr
    (by rw [show m=7239457225 from modulus_value]; decide +kernel)
  have kernel := weight_roots two 0 (1:ZMod m)
  simp only [Nat.cast_zero,mul_zero,sub_zero,one_pow] at kernel
  have inj : Function.Injective primes := by decide +kernel
  have crt := factor_ones (fun i => (primes i)^2) (PrimeFactors.CoprimeGuessTables.coprime primes inj)
  have value : (∏ i,weight 0 (1:ZMod ((primes i)^2)))=32 := by
    simp only [local_one,prod_const,card_univ,Fintype.card_fin]
    decide
  exact fibre.trans ((Nat.card_congr (sqrtOneEquiv (ZMod m))).trans (kernel.symm.trans (crt.trans value)))

end PrimeFactors.FiveSquareOrbitKernel
