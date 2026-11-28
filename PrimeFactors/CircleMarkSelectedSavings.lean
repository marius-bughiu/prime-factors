import PrimeFactors.CircleMarkFirstTargetPopulation
import PrimeFactors.CircleMarkParityLanes

/-! A single population for the first target actually selected from each product
and the fraction of its gcd tests eliminated by the two parity progressions. -/
namespace PrimeFactors.CircleMarkSelectedSavings

open Finset MixedPrefixSample CircleMarkFirstTarget CircleMarkFirstTargetPopulation
open CircleMarkBandSavings CircleMarkParityLanes
open private PrimeFactors.CircleMarkFirstTargetPopulation.first_exists from PrimeFactors.CircleMarkFirstTargetPopulation
open private PrimeFactors.FullPopulationFavoredSums.mem_eligible from PrimeFactors.FullPopulationFavoredSums

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible primes population

/-- Remove first targets beyond 13 and the products for which the geometric
bound or the bound on early marks may fail. The two sets may overlap. -/
noncomputable def regular := eligible \ (population ∪ exceptional (2^968))

theorem first_regular {p q : ℕ} (mem : (p,q)∈regular) :
    ∃ a, First (p*q) a ∧ a≤13 ∧ allowed a := by
  obtain ⟨pair,out⟩ := mem_sdiff.mp mem
  obtain ⟨a,first⟩ := PrimeFactors.CircleMarkFirstTargetPopulation.first_exists pair
  have early : a≤13 := le_of_not_gt fun late => out
    (mem_union_left _ (mem_late.mpr ⟨pair,a,first,late⟩))
  obtain ⟨_,_,_,pp,qp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp pair
  have pr := prime (pp.one_lt.trans_le (Nat.le_mul_of_pos_right _ qp.pos)) first
  refine ⟨a,first,early,?_⟩
  unfold allowed
  interval_cases a <;> norm_num at pr ⊢

/-- One target is obtained from the product; the search gain bound is
simultaneous over all marked stops for this particular choice. -/
theorem first_savings {p q : ℕ} (mem : (p,q)∈regular) :
    ∃ a, First (p*q) a ∧ a≤13 ∧ allowed a ∧ ∀ stop : ℕ, 0<stop →
      ¬(p*q).Coprime (CircleMarkSmallTargetPopulation.magnitude a stop 1) →
      2^359*(CircleMarkTwoAdicSavings.stripped (p*q) a stop).card<stop := by
  obtain ⟨a,first,early,ok⟩ := first_regular mem
  obtain ⟨pair,out⟩ := mem_sdiff.mp mem
  have positive : 0<a := by
    by_contra! bad
    have zero : a=0 := by omega
    obtain ⟨_,_,_,pp,qp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp pair
    have neg := first.1
    rw [zero,Nat.cast_zero,jacobiSym.zero_left (pp.one_lt.trans_le (Nat.le_mul_of_pos_right _ qp.pos))] at neg
    contradiction
  have bound : a∈Icc 1 CircleMarkSmallTargetPopulation.A :=
    mem_Icc.mpr ⟨positive,early.trans (by decide)⟩
  exact ⟨a,first,early,ok,fun _ start hit => CircleMarkParityLanes.broad_fraction pair
    (fun m => out (mem_union_right _ m)) ok bound first.1 start hit⟩

private theorem fraction_bound {all kept late exc : ℕ} (den : 0<all)
    (sum : all≤kept+(late+exc)) (sparse : 2^85*exc<all)
    (approx : |(late:ℝ)/all-1/64|≤1/(2:ℝ)^146) :
    63/64-1/(2:ℝ)^84<(kept:ℝ)/all := by
  have pos : 0<(all:ℝ) := Nat.cast_pos.mpr den
  have rare : (exc:ℝ)/all<1/(2:ℝ)^85 := by
    rw [div_lt_div_iff₀ pos (by positivity),one_mul,mul_comm]
    exact_mod_cast sparse
  have total : (all:ℝ)≤kept+(late:ℝ)+exc := by
    exact_mod_cast (show all≤kept+late+exc by omega)
  have ratio := div_le_div_of_nonneg_right total pos.le
  rw [div_self pos.ne',add_div,add_div] at ratio
  have remainder := (abs_le.mp approx).2
  linarith

/-- The analytic input is used only for the share of early chosen targets.
The exceptional set and the pointwise search bound above are unconditional. -/
theorem share {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints modulus li) :
    63/64-1/(2:ℝ)^84 < (regular.card:ℝ)/eligible.card := by
  have den : 0<eligible.card := by have := ChebyshevPrimeSample.eligible_count; omega
  have cover : eligible ⊆ regular ∪ (population ∪ exceptional (2^968)) := by
    intro v mem
    by_cases out : v∈population ∪ exceptional (2^968)
    · exact mem_union_right _ out
    · exact mem_union_left _ (mem_sdiff.mpr ⟨mem,out⟩)
  have total := (card_le_card cover).trans ((card_union_le ..).trans
    (Nat.add_le_add_left (card_union_le ..) _))
  exact fraction_bound den total broad_exceptions (close_ehp h)


end PrimeFactors.CircleMarkSelectedSavings
