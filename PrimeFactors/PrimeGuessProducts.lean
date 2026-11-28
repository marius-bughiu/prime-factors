import PrimeFactors.PrimeSquareGuessAffinity
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Products of factors bounded away from one by a multiple of the
reciprocal prime can be made arbitrarily small using distinct primes. -/

namespace PrimeFactors.PrimeGuessProducts

open Finset Real

/-- Distinct primes at or above a fixed threshold still have unbounded
finite sums of reciprocals. -/
theorem large_tail (cut : ℕ) (target : ℝ) :
    ∃ n : ℕ, target < ∑ p∈n.primesBelow \ cut.primesBelow, (1:ℝ)/p := by
  classical
  by_contra! limited
  apply not_summable_one_div_on_primes
  apply summable_of_sum_range_le (c:=target+∑ p∈cut.primesBelow,(1:ℝ)/p)
  · intro n
    apply Set.indicator_nonneg
    intros
    positivity
  · intro n
    rw [sum_indicator_eq_sum_filter]
    change (∑ p∈n.primesBelow, (1:ℝ)/p)≤_
    have sub : n.primesBelow∩cut.primesBelow ⊆ cut.primesBelow := inter_subset_right
    have first : ∑ p∈n.primesBelow∩cut.primesBelow,(1:ℝ)/p ≤
        ∑ p∈cut.primesBelow,(1:ℝ)/p :=
      sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
    have split := sum_sdiff (f:=fun p : ℕ => (1:ℝ)/p)
      (show n.primesBelow∩cut.primesBelow ⊆ n.primesBelow from inter_subset_left)
    have tail : n.primesBelow \ (n.primesBelow∩cut.primesBelow)=n.primesBelow \ cut.primesBelow := by
      ext p
      simp only [mem_sdiff,mem_inter]
      tauto
    rw [tail] at split
    linarith only [limited n,first,split]

/-- One finite product already suffices once the reciprocal sum is large. -/
theorem finite_small (S : Finset ℕ) (f : ℕ → ℝ) (nn : ∀ p∈S, 0≤f p)
    (gap : ∀ p∈S, f p≤1-1/(2*(p:ℝ))) {ε : ℝ} (pos : 0<ε)
    (big : -2*Real.log ε < ∑ p∈S,(1:ℝ)/p) : ∏ p∈S,f p < ε := by
  have bound := prod_le_prod (s:=S) (f:=f) (g:=fun p : ℕ => exp (-(1/(2*(p:ℝ)))))
    (fun p hp => nn p hp) (fun p hp => (gap p hp).trans
      (by linarith only [Real.add_one_le_exp (-(1/(2*(p:ℝ))))]))
  apply bound.trans_lt
  rw [←Real.exp_sum,←Real.exp_log pos,Real.exp_lt_exp]
  have each (p : ℕ) : -(1/(2*(p:ℝ))) = -(1/2:ℝ)*(1/(p:ℝ)) := by ring
  simp_rw [each]
  rw [←mul_sum]
  linarith only [big]

/-- For any nonnegative local factors with the stated reciprocal deficit,
finite products along the prime squares fall below every positive target. -/
theorem arbitrarily_small (cut : ℕ) (f : ℕ → ℝ) (nn : ∀ p, p.Prime → cut≤p → 0≤f p)
    (gap : ∀ p, p.Prime → cut≤p → f p≤1-1/(2*(p:ℝ)))
    {ε : ℝ} (pos : 0<ε) :
    ∃ n : ℕ, ∏ p∈n.primesBelow \ cut.primesBelow, f p < ε := by
  obtain ⟨n,big⟩ := large_tail cut (-2*Real.log ε)
  refine ⟨n,?_⟩
  let S := n.primesBelow \ cut.primesBelow
  have good {p : ℕ} (h : p∈S) : p.Prime ∧ cut≤p := by
    obtain ⟨a,b⟩ := mem_sdiff.mp h
    have hp := (Nat.mem_primesBelow.mp a).2
    exact ⟨hp,le_of_not_gt (fun lt => b (Nat.mem_primesBelow.mpr ⟨lt,hp⟩))⟩
  exact finite_small S f (fun p hp => nn p (good hp).1 (good hp).2)
    (fun p hp => gap p (good hp).1 (good hp).2) pos big

/-- The prime-square residue models meet the reciprocal-deficit hypothesis
even when each prime occurs just once. -/
theorem small_joint_affinity {ε : ℝ} (pos : 0<ε) :
    ∃ n : ℕ, ∏ p∈n.primesBelow \ Nat.primesBelow 11, PrimeSquareGuessAffinity.affinity p < ε := by
  apply arbitrarily_small 11 PrimeSquareGuessAffinity.affinity
  · intro p _ _
    exact PrimeSquareGuessAffinity.affinity_nonneg p
  · intro p prime large
    letI : Fact p.Prime := ⟨prime⟩
    linarith only [PrimeSquareGuessAffinity.deficit_lower large]
  · exact pos

/-- Every label has inclusive rank at least one. This also accounts for
the additive one in the classical square-root bound on expected rank. -/
theorem mean_ge_one {α : Type*} [Fintype α] (w : α → ℝ) (nn : ∀ a,0≤w a)
    (mass : 0<IndependentGuessRanks.total w) (e : Fin (Fintype.card α) ≃ α) :
    1≤IndependentGuessRanks.meanRank w e := by
  unfold IndependentGuessRanks.meanRank
  rw [le_div_iff₀ mass,one_mul]
  rw [IndependentGuessRanks.total,←e.sum_comp w]
  exact sum_le_sum fun i _ => le_mul_of_one_le_left (nn _) (by have := Nat.cast_nonneg (α:=ℝ) i.val; linarith)

/-- A bound by the joint affinity translates to the fraction of the
uniform-random-order mean, whose inclusive rank is (A+1)/2. -/
theorem fraction_of_uniform {a f μ ε : ℝ} (a0 : 0≤a) (mu : 1≤μ)
    (bound : 2*μ≤1+a*f) (small : f<ε/2) (pos : 0<ε) : μ<ε*((a+1)/2) := by
  have dom : a*f≤a*(ε/2) := mul_le_mul_of_nonneg_left small.le a0
  linarith only [mu,bound,dom,pos]

end PrimeFactors.PrimeGuessProducts
