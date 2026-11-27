import PrimeFactors.PublicStableWheelCounts

/-! Compare two additional odd primes with arbitrary extra precision at the
seven old primes. All cardinalities use the same public interval for each
fixture and the same starting wheel. -/
namespace PrimeFactors.PublicFreshPrimeComparison

open ChebyshevQuarticScale (fresh crossed)
open PublicWheelWidthControls (width tests period_bounds)
open LocalSumMenu (count)
open PublicStableWheelCounts (survivors)
open private PrimeFactors.IntervalWheelControls.prime_count from PrimeFactors.IntervalWheelControls

abbrev base := PublicPrimeSquareCounts.modulus
def modulus := base*23*29

/-- The product modulus enforces exactly the starting wheel and the two new predicates. -/
theorem passes_iff (n s : ℕ) :
    AdmissibleSum (n : ZMod modulus) (s : ZMod modulus) ↔
      (AdmissibleSum (n : ZMod base) (s : ZMod base) ∧
       AdmissibleSum (n : ZMod 23) (s : ZMod 23)) ∧
       AdmissibleSum (n : ZMod 29) (s : ZMod 29) := by
  rw [modulus, PublicWheelLookupCosts.extend_prefix (by decide : (base*23).Coprime 29),
    PublicWheelLookupCosts.extend_prefix (by decide : base.Coprime 23)]

/-- Each additional table uses one membership bit per residue. -/
theorem table_sizes : [23,29].length = 2 ∧ [23,29].sum = 52 ∧
    (([23,29] : List ℕ).map (fun p => (p+7)/8)).sum = 7 := by decide

theorem fresh_local :
    fresh%23 = 15 ∧ fresh%29 = 25 ∧ count fresh 23 = 11 ∧ count fresh 29 = 15 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  all_goals
    rw [PrimeFactors.IntervalWheelControls.prime_count (by decide) (by decide) (by decide +kernel)]
    decide +kernel

theorem crossed_local :
    crossed%23 = 11 ∧ crossed%29 = 27 ∧ count crossed 23 = 11 ∧ count crossed 29 = 14 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  all_goals
    rw [PrimeFactors.IntervalWheelControls.prime_count (by decide) (by decide) (by decide +kernel)]
    decide +kernel

private theorem extend_count (n : ℕ) : count n modulus = count n base * count n 23 * count n 29 := by
  exact (card_admissibleSum_crt (by decide : (base*23).Coprime 29) n).trans
    (congrArg (· * count n 29) (card_admissibleSum_crt (by decide : base.Coprime 23) n))

theorem period_counts : count fresh modulus = 4839757322400 ∧ count crossed modulus = 3099457320960 := by
  simp only [extend_count, PublicPrimeSquareCounts.fresh_period, PublicPrimeSquareCounts.crossed_period,
    fresh_local.2.2.1, fresh_local.2.2.2, crossed_local.2.2.1, crossed_local.2.2.2]
  decide

/-- Parts per million of starting-wheel survivors retained on the actual interval. -/
def Relative (n lo hi : ℕ) : Prop :=
  lo*tests n base ≤ 1000000*tests n modulus ∧ 1000000*tests n modulus ≤ hi*tests n base

private theorem retain {n wlo whi old new l h : ℕ} (size : wlo ≤ width n ∧ width n ≤ whi)
    (old_eq : count n base = old) (new_eq : count n modulus = new)
    (lower : l*((whi/base+1)*old) ≤ 1000000*(wlo/modulus*new))
    (upper : 1000000*((whi/modulus+1)*new) ≤ h*(wlo/base*old)) : Relative n l h := by
  have bound (m c : ℕ) (pos : 0<m) (card : count n m = c) :
      wlo/m*c ≤ tests n m ∧ tests n m ≤ (whi/m+1)*c := by
    obtain ⟨lo,hi⟩ := period_bounds n m pos
    rw [card] at lo hi
    exact ⟨(Nat.mul_le_mul_right _ (Nat.div_le_div_right size.1)).trans lo,
      hi.trans (Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.div_le_div_right size.2)))⟩
  obtain ⟨ol,oh⟩ := bound base old (by decide) old_eq
  obtain ⟨nl,nh⟩ := bound modulus new (by decide) new_eq
  exact ⟨(Nat.mul_le_mul_left _ oh).trans (lower.trans (Nat.mul_le_mul_left _ nl)),
    (Nat.mul_le_mul_left _ nh).trans (upper.trans (Nat.mul_le_mul_left _ ol))⟩

theorem fresh_bounds : Relative fresh 247376 247377 := by
  apply retain (wlo:=2557561*10^300) (whi:=2557562*10^300) _
    PublicPrimeSquareCounts.fresh_period period_counts.1
  · decide +kernel
  · decide +kernel
  · exact PublicWheelLookupCosts.width_between (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem crossed_bounds : Relative crossed 230884 230885 := by
  apply retain (wlo:=11130366*10^300) (whi:=11130367*10^300) _
    PublicPrimeSquareCounts.crossed_period period_counts.2
  · decide +kernel
  · decide +kernel
  · exact PublicWheelLookupCosts.width_between (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Compare counts of eliminated sums. The last inequality expresses the
extra eliminations per million initial survivors. No set inclusion between
the two strengthened tests is needed. -/
def Advantage (n gap : ℕ) : Prop :=
  tests n modulus < survivors n ∧
  tests n base - survivors n < tests n base - tests n modulus ∧
  gap*tests n base ≤ 1000000*(survivors n - tests n modulus)

theorem fresh_advantage : Advantage fresh 65023 := by
  have ⟨_,a⟩ := fresh_bounds
  have ⟨b,c⟩ := PublicStableWheelCounts.fresh_bounds
  have pos := PublicPrimeSquareCounts.fresh_summary.1
  unfold Advantage base at *
  omega

theorem crossed_advantage : Advantage crossed 57615 := by
  have ⟨_,a⟩ := crossed_bounds
  have ⟨b,c⟩ := PublicStableWheelCounts.crossed_bounds
  have pos := PublicPrimeSquareCounts.crossed_summary.1
  unfold Advantage base at *
  omega

end PrimeFactors.PublicFreshPrimeComparison
