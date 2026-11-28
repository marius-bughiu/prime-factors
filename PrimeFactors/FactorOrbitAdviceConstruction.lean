import PrimeFactors.FiveSquareFactorGuessing
import PrimeFactors.GeometricWheelBlocks

/-! Truthful side information specifies one remainder of the hidden orbit's
position in a known ordering. One tests the labels in that residue class
in their original order. The information is supplied by hypothesis. -/
namespace PrimeFactors.FactorOrbitAdviceConstruction

open Finset FactorOrbitGuessRanks
open FiveSquareFactorGuessing (PolicyFor)
open FiveSquarePolicy (U)
open FiveSquareAllPrimeRanks (uniform actual UnitPair)
open scoped Classical
open private PrimeFactors.FiveSquareFactorGuessing.lift PrimeFactors.FiveSquareFactorGuessing.lift_units
  PrimeFactors.FiveSquareFactorGuessing.rank_sym PrimeFactors.FiveSquareFactorGuessing.rank_bound
  PrimeFactors.FiveSquareFactorGuessing.uniform_attains PrimeFactors.FiveSquareFactorGuessing.error
  from PrimeFactors.FiveSquareFactorGuessing

/-- The truthful advice has exactly B available codewords, including
when the underlying list is longer. -/
noncomputable def code {B : ℕ} (positive : 0<B) (i : ℕ) : Fin B := ⟨i%B,Nat.mod_lt i positive⟩

/-- Exactly floor(i/B) positions of the same code precede position i. -/
theorem prior_card {B : ℕ} (positive : 0<B) (i : ℕ) :
    ((range i).filter (fun j => code positive j=code positive i)).card=i/B := by
  have h := GeometricWheelBlocks.retained_count ({i%B}:Finset ℕ) (m:=B)
    (by intro a ha; obtain rfl := mem_singleton.mp ha; exact Nat.mod_lt i positive) i
  simpa only [mem_singleton,Fin.ext_iff,code,GeometricWheelBlocks.laneLength,sum_singleton,
    lt_self_iff_false,if_false,Nat.add_zero] using h

/-- Any probability distribution on a finite set of hidden targets
obeys the inclusive mean-rank bound under this supplied code. -/
theorem weighted_mean {α : Type*} [Fintype α] (μ : α→ℝ) (nonnegative : ∀ a,0≤μ a)
    (normalized : ∑ a,μ a=1) (i : α→ℕ) {B : ℕ} (positive : 0<B) :
    (∑ a,μ a*((i a/B+1:ℕ):ℝ))≤((∑ a,μ a*((i a+1:ℕ):ℝ))-1)/(B:ℝ)+1 := by
  have bpos : (0:ℝ)<B := by exact_mod_cast positive
  have each (a : α) : ((i a/B:ℕ):ℝ)≤(i a:ℝ)/B :=
    (le_div_iff₀ bpos).mpr (by exact_mod_cast Nat.div_mul_le_self (i a) B)
  calc
    _ ≤ ∑ a, μ a*((i a:ℝ)/B+1) := sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (by rw [Nat.cast_add,Nat.cast_one]; linarith only [each a]) (nonnegative a)
    _ = _ := by simp only [Nat.cast_add,Nat.cast_one,mul_add,mul_one,←mul_div_assoc,←sum_div,
                          sum_add_distrib,normalized,add_sub_cancel_right]

variable {G : Type*} [CommGroup G] [Fintype G]

/-- Actual inclusive rank after receiving the target's code. -/
noncomputable def advised (B : ℕ) (P : PolicyFor G) (a b : G) :=
  (FiveSquareFactorGuessing.rank P a b-1)/B+1

theorem advised_eq {B : ℕ} (positive : 0<B) (P : PolicyFor G) (a b : G) :
    advised B P a b=
      ((range ((P (a*b)) (label (a*b) a)).val).filter
        (fun j => code positive j=code positive ((P (a*b)) (label (a*b) a)).val)).card+1 := by
  rw [prior_card positive]
  rfl

private theorem positive_rank (P : PolicyFor G) (a b : G) : 0<FiveSquareFactorGuessing.rank P a b :=
  Nat.succ_pos _

private theorem avg_as_weight {α : Type*} [Fintype α] (f : α→ℕ) :
    (∑ a,(1/(Fintype.card α:ℝ))*(f a:ℝ))=((∑ a,f a:ℕ):ℝ)/(Fintype.card α:ℝ) := by
  rw [←mul_sum,←Nat.cast_sum]
  ring

private theorem uniform_comparison {B : ℕ} (positive : 0<B) (P : FiveSquareFactorGuessing.Policy) :
    uniform (PrimeFactors.FiveSquareFactorGuessing.lift (advised B P)) ≤
      (uniform (PrimeFactors.FiveSquareFactorGuessing.lift (FiveSquareFactorGuessing.rank P))-1)/(B:ℝ)+1 := by
  have size : (0:ℝ)<Fintype.card UnitPair := by
    exact_mod_cast (Fintype.card_pos : 0<Fintype.card UnitPair)
  have prob : (∑ _ : UnitPair, (1:ℝ)/(Fintype.card UnitPair))=1 := by
    simp only [sum_const,card_univ,nsmul_eq_mul]
    rw [←mul_div_assoc,mul_one,div_self size.ne']
  let old (v : UnitPair) := FiveSquareFactorGuessing.rank P v.1 v.2
  have restore (v : UnitPair) : old v-1+1=old v := Nat.sub_add_cancel (positive_rank P v.1 v.2)
  have cmp := weighted_mean (fun _ : UnitPair => (1:ℝ)/(Fintype.card UnitPair))
    (fun _ => (div_pos zero_lt_one size).le) prob (fun v => old v-1) positive
  simp only [restore,avg_as_weight] at cmp
  simpa only [uniform,PrimeFactors.FiveSquareFactorGuessing.lift_units,advised,old] using cmp

/-- Modular mean after the truthful rank residue is revealed. -/
noncomputable def modularMean (B : ℕ) (P : FiveSquareFactorGuessing.Policy) :=
  uniform (PrimeFactors.FiveSquareFactorGuessing.lift (advised B P))

/-- Mean for the actual prime population after the same information is supplied. -/
noncomputable def primeMean (B : ℕ) (P : FiveSquareFactorGuessing.Policy) :=
  actual (PrimeFactors.FiveSquareFactorGuessing.lift (advised B P))

set_option maxRecDepth 4096
attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card

/-- With 25 truthful bits, no hidden modular pair needs over 59 orbit
guesses, regardless of the underlying ordering. -/
theorem five_worst (P : FiveSquareFactorGuessing.Policy) (a b : U) : advised (2^25) P a b≤59 := by
  let n := a*b
  have cap : fixed n≤32 := by
    rcases SquareFiberMoments.share_kernel n with zero|same
    · exact zero.le.trans (by decide : 0≤32)
    · exact (same.trans FiveSquareOrbitKernel.count).le
  have card := count n
  rw [FiveSquarePolicy.unit_count.1] at card
  have index := ((P n) (label n a)).isLt
  change (((P n) (label n a)).val+1-1)/2^25+1≤59
  change (((P n) (label n a)).val/33554432)+1≤59
  omega

private theorem center_bound :
    (FiveSquareFactorGuessing.optimalCenter-1)/(2^25:ℕ)+1+(1:ℝ)/2^347<31 := by
  norm_num [FiveSquareFactorGuessing.optimalCenter,FiveSquareFactorGuessing.T]

/-- Some product-dependent order averages under 31 guesses when its
truthful 25-bit code is supplied, in the finite modular population. -/
theorem five_uniform :
    ∃ P : FiveSquareFactorGuessing.Policy, modularMean (2^25) P+1/(2:ℝ)^347<31 := by
  obtain ⟨P,_,hit⟩ := PrimeFactors.FiveSquareFactorGuessing.uniform_attains
  have cmp := uniform_comparison (B:=2^25) (by decide) P
  rw [hit] at cmp
  exact ⟨P,(add_le_add_right cmp _).trans_lt center_bound⟩

/-- Under the explicit prime-counting endpoints, the same order also
averages under 31 orbit guesses on the eligible full-width prime pairs. -/
theorem five_actual {li : ℕ→ℝ} (h : FiveSquarePrimeSupply.Endpoints li) :
    ∃ P : FiveSquareFactorGuessing.Policy, modularMean (2^25) P<31 ∧ primeMean (2^25) P<31 := by
  obtain ⟨P,low⟩ := five_uniform
  have sym (a b : U) : advised (2^25) P a b=advised (2^25) P b a := by
    rw [advised,PrimeFactors.FiveSquareFactorGuessing.rank_sym,←advised]
  have bound (a b : U) : advised (2^25) P a b≤2^33 :=
    (five_worst P a b).trans (by decide)
  have close := (abs_le.mp (PrimeFactors.FiveSquareFactorGuessing.error h (advised (2^25) P) sym bound)).2
  change primeMean (2^25) P-modularMean (2^25) P≤_ at close
  have positive : (0:ℝ)<1/2^347 := by positivity
  have upper := (sub_le_iff_le_add.mp close).trans_eq (add_comm _ _)
  exact ⟨P,(lt_add_of_pos_right _ positive).trans low,upper.trans_lt low⟩

end PrimeFactors.FactorOrbitAdviceConstruction
