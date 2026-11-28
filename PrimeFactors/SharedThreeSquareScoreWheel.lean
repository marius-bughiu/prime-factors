import PrimeFactors.ScoreWheelMemory
import PrimeFactors.ShiftedScoreSieveCycle
import PrimeFactors.ThreeSquareWheelWork

/-! The ascending packed phase table is the one traversed by every
stream. Its output is exactly the subset counted in the population bounds. -/
namespace PrimeFactors.SharedThreeSquareScoreWheel

open Finset
open SixSquareLookupStages (A period coprime)
open ScoreWheelMemory (wheel phases)
open ShiftedScoreSieveCycle (table phase output)
open ThreeSquareWheelWork (generated remaining)
open WithinResidueSearchFloor (low scoreVisits)
open MixedPrefixSample (eligible)
open StreamSumScores (seed term)
open scoped Classical
attribute [local irreducible] eligible

theorem table_eq (n : ℕ) : (table (A n 3)).sort (·≤·)=phases n := by
  apply List.Sorted.eq_of_mem_iff (sort_sorted_lt _) (ScoreWheelMemory.increasing n)
  intro j
  simp only [mem_sort,table,mem_filter,mem_range,ShiftedScoreSieveCycle.normalized,mem_univ,
    true_and,ScoreWheelMemory.mem_phases,ScoreWheelMemory.stride_apply]

private theorem present (n : ℕ) : (A n 3).Nonempty := by
  refine ⟨((1+n:ℕ):ZMod wheel),(SixSquareLookupStages.mem_A n 3 (1+n)).mpr ?_⟩
  exact admissibleSum_of_factor_pair (period 3) (one_mul n)

/-- The stream offset emitted by reading the appropriate slot of the
periodic shared table. Each modulo-100 stream has its own starting slot. -/
noncomputable def index (n start k : ℕ) := output wheel (NeZero.pos _) (table (A n 3))
  (ShiftedScoreSieveCycle.table_nonempty (coprime 3) (present n)) (phase (start:ZMod wheel)) k

/-- An emitted term belongs to the inclusive old score prefix exactly
when it belongs to the counted three-screen subsearch. -/
theorem candidate (v : ℕ×ℕ) (r : Fin 100) (j : ℕ) :
    term (low v) r j∈generated v ↔ term (low v) r j∈scoreVisits v ∧
      ∃ k,index (v.1*v.2) (seed (low v) r) k=j := by
  change term (low v) r j∈(scoreVisits v).filter _ ↔ _
  rw [mem_filter]
  apply and_congr_right
  intro _
  unfold index
  rw [ShiftedScoreSieveCycle.stream_exact (coprime 3) (present (v.1*v.2))]
  simp only [term,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]

/-- Each stream advances in strictly increasing original position, so the
existing merge-by-score order remains available on surviving terms. -/
theorem ordered (n start : ℕ) : StrictMono (index n start) := by
  apply ShiftedScoreSieveCycle.ordered
  intro x hx
  exact mem_range.mp (mem_filter.mp hx).1

private theorem total {S : Finset (ℕ×ℕ)} (V : ℕ×ℕ→Finset ℕ) (W : ℕ×ℕ→ℕ)
    (previous : 100000*(∑ v∈S,(ThreeSquareWheelWork.setup+W v))<10901*(∑ v∈S,(V v).card)) :
    100000*(∑ v∈S,(ScoreWheelMemory.setupChecks (v.1*v.2)+W v))<10901*(∑ v∈S,(V v).card) := by
  have charge := sum_le_sum (s:=S) (fun v _ =>
    Nat.add_le_add_right (ScoreWheelMemory.setup_unconditional (v.1*v.2)) (W v))
  exact (Nat.mul_le_mul_left 100000 charge).trans_lt previous

/-- Use the actual short-circuit setup count for the phase table in the
whole-population bound. The tail count includes its failing lookup. -/
theorem lookup_population :
    100000*(∑ v∈eligible,(ScoreWheelMemory.setupChecks (v.1*v.2)+remaining v)) <
      10901*(∑ v∈eligible,(scoreVisits v).card) :=
  total (S:=eligible) scoreVisits remaining ThreeSquareWheelWork.lookup_population

end PrimeFactors.SharedThreeSquareScoreWheel
