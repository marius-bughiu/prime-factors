import PrimeFactors.QuarticPublicResidueGate
import PrimeFactors.QuarticLocalPopulation

/-! Relating the local criterion and the length of the last-bit screened
executable list to the uniform eligible prime-pair population. -/
namespace PrimeFactors.QuarticLocalSearchWork

open Finset
open MixedPrefixSample (eligible)
open QuarticLocalClassification (Tests)
open QuarticPublicResidueGate (Allowed denominators)
open QuarticLocalPopulation (lastBits locus)
open scoped Classical
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible

noncomputable def locallyPossible := eligible.filter (fun v => Tests (v.1*v.2))

theorem possible_eq : locallyPossible=locus := by
  ext ⟨p,q⟩
  rw [locallyPossible,mem_filter,QuarticLocalPopulation.mem_locus]
  apply and_congr_right
  intro mem
  obtain ⟨pl,ord,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp mem
  have two : 2<p := (by decide +kernel : 2<FullRangeResidueEstimates.X).trans_le pl
  exact QuarticLocalClassification.semiprime pp qp (pp.odd_of_ne_two two.ne') (qp.odd_of_ne_two (two.trans ord).ne')

private theorem pos : (0:ℝ)<eligible.card := by
  have h := MixedPrefixSample.denominator ChebyshevPrimeSample.prime_count
  exact_mod_cast (show 0<eligible.card by omega)

private theorem length_le (n : ℕ) : (denominators n).length ≤ if Allowed n then 3 else 0 := by
  unfold denominators ProductSelectedQuarticDenominators.denominators
  split_ifs <;> decide

private theorem scheduled (s : Finset (ℕ×ℕ)) : (∑ v∈s,(denominators (v.1*v.2)).length)≤
    (s.filter (fun v => Allowed (v.1*v.2))).card*3 := by
  have bounds := sum_le_sum (s:=s) (fun v _ => length_le (v.1*v.2))
  apply bounds.trans_eq
  rw [←sum_filter,sum_const,smul_eq_mul]

theorem workload : (∑ v∈eligible,(denominators (v.1*v.2)).length)≤lastBits.card*3 := by
  have classes : (eligible.filter (fun v => Allowed (v.1*v.2)))=lastBits := by
    ext ⟨p,q⟩
    simp only [mem_filter,QuarticLocalPopulation.mem_lastBits,Allowed]
  exact (scheduled eligible).trans_eq (congrArg (fun s : Finset (ℕ×ℕ) => s.card*3) classes)

private theorem from_share (cap : (lastBits.card:ℝ)/eligible.card<751/3000) :
    1000*(∑ v∈eligible,(denominators (v.1*v.2)).length)<751*eligible.card := by
  have scaled := (div_lt_iff₀ pos).mp cap
  have cost : ((∑ v∈eligible,(denominators (v.1*v.2)).length : ℕ):ℝ)≤lastBits.card*3 := by
    exact_mod_cast workload
  exact_mod_cast (show (1000:ℝ)*((∑ v∈eligible,(denominators (v.1*v.2)).length : ℕ):ℝ)<
    751*eligible.card by linarith)

/-- Upper bound on scheduled checks before an early return, charging all
three permitted trials to every product whose public last four bits pass. -/
theorem average {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints 16 li) :
    1000*(∑ v∈eligible,(denominators (v.1*v.2)).length)<751*eligible.card := by
  apply from_share
  have upper := (abs_le.mp (QuarticLocalPopulation.last_close_ehp h)).2
  have margin : (1:ℝ)/4+1/2^146<751/3000 := by norm_num
  linarith

/-- The same work bound already follows from the unconditional BMOR
endpoint estimate at modulus sixteen. -/
theorem average_bmor {li : ℕ→ℝ} (h : QuarticLocalPopulation.BmorEndpoints li) :
    1000*(∑ v∈eligible,(denominators (v.1*v.2)).length)<751*eligible.card := by
  apply from_share
  have upper := (abs_le.mp (QuarticLocalPopulation.last_close_bmor h)).2
  have margin : (1:ℝ)/4+1/4160<751/3000 := by norm_num
  linarith

end PrimeFactors.QuarticLocalSearchWork
