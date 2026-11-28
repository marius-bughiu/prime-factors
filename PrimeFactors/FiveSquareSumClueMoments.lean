import PrimeFactors.FiveSquareSignPopulation
import PrimeFactors.FiveSquareOrbitKernel
import PrimeFactors.SumClueOrbitRanks

/-! Second moments of complementary factor-pair multiplicities when the
product and its true sum residue are supplied at five prime squares. -/
namespace PrimeFactors.FiveSquareSumClueMoments

open Finset PrimeSquareSumWeights FiveSquareSignRanks
open FiveSquareGuessRanks (primes)
open FiveSquarePrimeSupply (m)
open FiveSquarePolicy (U)
open scoped Classical
set_option maxRecDepth 4096
attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card

/-- Unnormalized second moment, with one summand per possible sum. -/
noncomputable def squareMass (b : Pattern) := rows b (fun w => w^2)

private def allSquare : Pattern := fun _ => true
private noncomputable def diagonal (b : Pattern) := if b=allSquare then 32 else 0

private theorem full_support {d n : ℕ} [NeZero d] :
    (∑ s : ZMod d,weight n s^2)=∑ s : CoprimeGuessTables.Labels d n,weight n s.val^2 := by
  have zero (s : {s : ZMod d // ¬AdmissibleSum (n:ZMod d) s}) : weight n s.val=0 :=
    Nat.eq_zero_of_not_pos (fun h => s.property ((CoprimeGuessTables.positive_iff s.val).mp h))
  have split := Fintype.sum_subtype_add_sum_subtype (AdmissibleSum (n:ZMod d)) (fun s => weight n s^2)
  simpa only [zero,zero_pow (by decide : 2≠0),sum_const_zero,add_zero] using split.symm

/-- The complete global sum of squared weights is determined by five
quadratic signs. -/
theorem second (u : U) :
    (∑ s : ZMod m,weight u.val.val s^2)=squareMass (sign u.val.val) := by
  rw [full_support]
  have unit : IsUnit (u.val.val:ZMod m) := by rw [ZMod.natCast_zmod_val]; exact u.isUnit
  exact histogram _ (local_units unit) (fun w => w^2)

private theorem sign_of_square (x u : U) (eq : x^2=u) : sign u.val.val=allSquare := by
  funext i
  apply decide_eq_true
  have dv : primes i∣m := (by decide +kernel : ∀ j, primes j∣m) i
  let f := ZMod.castHom dv (ZMod (primes i))
  have rep : f u.val=(u.val.val:ZMod (primes i)) := by
    nth_rw 1 [←ZMod.natCast_zmod_val u.val]
    exact map_natCast f _
  have square : x.val^2=u.val := by simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val eq
  exact (isSquare_iff_exists_sq _).mpr ⟨f x.val,by rw [←rep,←square,map_pow]⟩

private theorem has_root {G : Type*} [CommGroup G] [Fintype G] (u : G)
    (pos : 0<SquareFiberMoments.roots u) : ∃ x : G,x^2=u := by
  classical
  unfold SquareFiberMoments.roots at pos
  obtain ⟨x,hx⟩ := card_pos.mp pos
  exact ⟨x,(mem_filter.mp hx).2⟩

private theorem roots_le (u : U) : SquareFiberMoments.roots u≤diagonal (sign u.val.val) := by
  rcases SquareFiberMoments.share_kernel u with zero|same
  · rw [zero]; exact Nat.zero_le _
  have full := same.trans FiveSquareOrbitKernel.count
  have pos : 0<SquareFiberMoments.roots u := by omega
  obtain ⟨x,square⟩ := has_root u pos
  rw [sign_of_square x u square,diagonal,if_pos rfl,full]

private theorem diagonal_total : (∑ u : U,diagonal (sign u.val.val))=3920716800 := by
  rw [FiveSquareSignPopulation.sum_by_pattern diagonal,show (∑ b : Pattern,diagonal b)=32 by decide +kernel]
  decide

/-- A unit product has 32 diagonal ordered pairs exactly in the all-square
pattern; every other product has none. -/
theorem root_count (u : U) : SquareFiberMoments.roots u=if sign u.val.val=(fun _ => true) then 32 else 0 := by
  have same := (SquareFiberMoments.first (G:=U)).trans (FiveSquarePolicy.unit_count.1.trans diagonal_total.symm)
  exact (sum_eq_sum_iff_of_le (fun v (_ : v∈(univ:Finset U)) => roots_le v)).mp same u (mem_univ _)

/-- The exact algebraic cost for free access to the true sum residue at a
fixed observed product. The numerator uses its actual full residue table. -/
noncomputable def expected (u : U) : ℚ :=
  1/2+(((∑ s : ZMod m,weight u.val.val s^2 : ℕ):ℚ)+SquareFiberMoments.roots u)/(4*3920716800)

/-- The same cost computed from the 32-pattern table. -/
noncomputable def patternMean (b : Pattern) : ℚ := 1/2+((squareMass b:ℚ)+diagonal b)/(4*3920716800)

theorem expected_eq (u : U) : expected u=patternMean (sign u.val.val) := by
  rw [expected,second u,root_count]
  rfl

private theorem receipt :
    (∑ b : Pattern,(squareMass b:ℚ))/32=759029245975 ∧
    (∑ b : Pattern,patternMean b)/32=95858834947/1960358400 ∧
    patternMean (fun _ => true)=2472189581/13613600 ∧
    patternMean (fun _ => false)=17/2 := by decide +kernel

/-- The unnormalized sum of squared weights, averaged over unit products. -/
theorem pooled_second :
    (∑ u : U,((∑ s : ZMod m,weight u.val.val s^2 : ℕ):ℚ))/(Fintype.card U:ℚ)=759029245975 := by
  simp_rw [second]
  exact (FiveSquareSignPopulation.mean_by_pattern (fun b => (squareMass b:ℚ))).trans receipt.1

/-- Exact mean cost over all unit products if the true sum residue is
given free of charge. Each product has the same number of ordered preimages. -/
theorem pooled :
    (∑ u : U,expected u)/(Fintype.card U:ℚ)=95858834947/1960358400 := by
  simp_rw [expected_eq]
  exact (FiveSquareSignPopulation.mean_by_pattern patternMean).trans receipt.2.1

theorem all_square (u : U) (h : sign u.val.val=(fun _ => true)) :
    expected u=2472189581/13613600 := by rw [expected_eq,h,receipt.2.2.1]

theorem all_nonsquare (u : U) (h : sign u.val.val=(fun _ => false)) :
    expected u=17/2 := by rw [expected_eq,h,receipt.2.2.2]

theorem one : expected (1:U)=2472189581/13613600 :=
  all_square 1 (sign_of_square 1 1 (one_pow 2))

/-- For the given unit product, choosing a separate orbit order at each
supplied sum attains the stated mean. It is the least mean over all such
families, counting the successful guess. -/
theorem optimal (u : U) :
    IsLeast (Set.range (SumClueOrbitRanks.mean (u:=u))) (expected u) := by
  have two : IsUnit (2:ZMod m) := (ZMod.isUnit_iff_coprime 2 m).mpr
    (by rw [show m=7239457225 from FiveSquareGuessRanks.modulus_value]; decide +kernel)
  have h := SumClueOrbitRanks.mean_optimum u two
  rw [FiveSquarePolicy.unit_count.1] at h
  exact h

end PrimeFactors.FiveSquareSumClueMoments
