import PrimeFactors.DyadicClusterMenu
import PrimeFactors.DyadicMenuPopulationOptimum
import PrimeFactors.SumMenuWeightThreshold

/-! For a fixed square unit product modulo a power of two, count how many
ordered pairs the best list of B distinct guesses of their sum can cover. -/
namespace PrimeFactors.ExactDyadicSumMenu

open Finset PrimeSquareSumWeights
open scoped Classical

/-- Maximum over all distinct sum lists within the given budget. -/
def attainable (e N B : ℕ) : Set ℕ :=
  {n | ∃ S : Finset (ZMod (2^e)), S.card≤B ∧ n=∑ s∈S, weight N s}

private theorem profile {e t j N : ℕ} (depth : 2*t+j=e) (ht : 2≤t) (hj : 4≤j)
    (good : N%8=1) :
    ∃ A : Finset (ZMod (2^e)), A.card=2*DyadicSquareValueCount.count j ∧
      (∑ s∈A, weight N s)=2^(t+j+1) ∧
      (∀ s∈A, 2^(t+2)≤weight N s) ∧ (∀ s∉A, weight N s≤2^(t+1)) := by
  subst e
  let A := DyadicClusterMenu.menu t j N
  refine ⟨A,DyadicClusterMenu.card ht good,?_,fun _ => DyadicClusterMenu.weight_floor hj,?_⟩
  · rw [←LocalSumGuessCoverage.covered_eq_sum]
    exact DyadicClusterMenu.mass ht good
  · intro s outside
    by_cases pos : 0<weight N s
    · obtain ⟨a,b,prod,rfl⟩ := (CoprimeGuessTables.positive_iff s).mp pos
      have odd : Odd N := Nat.odd_iff.mpr (by omega)
      exact DyadicPairSumWeight.weight_le_of_gap (by omega) odd prod
        (fun divides => outside ((DyadicClusterMenu.pair_mem_iff ht odd prod).mpr divides))
    · exact (Nat.eq_zero_of_not_pos pos) ▸ Nat.zero_le _

/-- Between two consecutive cluster sizes, every extra guess buys exactly
the same number of pairs. The bound is attained for every budget in the interval. -/
theorem optimal_between {t j N B : ℕ} (ht : 2≤t) (hj : 4≤j) (good : N%8=1)
    (lower : 2*DyadicSquareValueCount.count j≤B)
    (upper : B≤2*DyadicSquareValueCount.count (j+2)) :
    IsGreatest (attainable (2*(t+1)+j) N B)
      (2^(t+j+2)+(B-2*DyadicSquareValueCount.count j)*2^(t+2)) := by
  obtain ⟨I,ic,im,heavy,icap⟩ := profile (N:=N) (t:=t+1) (j:=j) rfl (by omega) hj good
  obtain ⟨O,oc,_,ties,ocap⟩ := profile (e:=2*(t+1)+j) (N:=N) (t:=t) (j:=j+2)
    (by omega) ht (by omega) good
  have strict : (2:ℕ)^(t+1)<2^(t+2) := Nat.pow_lt_pow_right (by decide) (by omega)
  have le : (2:ℕ)^(t+2)≤2^(t+1+2) := Nat.pow_le_pow_right (by decide) (by omega)
  have incl : I⊆O := by
    intro s si
    by_contra so
    exact (not_lt_of_ge (ocap s so)) (strict.trans_le (le.trans (heavy s si)))
  have marginal : t+1+1=t+2 := by omega
  rw [marginal] at icap
  have opt := SumMenuWeightThreshold.optimal (weight N) I O B (2^(t+2)) incl
    (ic ▸ lower) (oc ▸ upper) (fun s si => le.trans (heavy s si)) icap
    (fun s so => le_antisymm (icap s (mem_sdiff.mp so).2) (ties s (mem_sdiff.mp so).1))
  rwa [ic,im,show t+1+j+1=t+j+2 by omega] at opt

/-- With 161 observed product bits and at most 2^32 guesses for the sum
ending, this is the exact largest number of compatible ordered pairs. -/
theorem at_161 {N : ℕ} (good : N%8=1) :
    IsGreatest (attainable 161 N (2^32)) (5010795177*2^66) := by
  have c33 : 2*DyadicSquareValueCount.count 33=2863311534 := by
    rw [DyadicSquareValueCount.closed (by decide)]; decide
  have c35 : 2*DyadicSquareValueCount.count (33+2)=11453246126 := by
    rw [DyadicSquareValueCount.closed (by decide)]; decide
  have h := optimal_between (t:=63) (j:=33) (B:=2^32) (by decide) (by decide) good
    (c33 ▸ (by decide)) (c35 ▸ (by decide))
  rw [c33] at h
  exact h

/-- Best fraction of actual eligible prime pairs at the same budget,
conditional on the specified product suffix and prime-count estimates. -/
theorem prime_pairs_161 (r : DyadicSumMenuBudget.U 161) (good : r.val.val%8=1)
    {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints (2^161) li) :
    let C := (5010795177:ℝ)/2^94
    |DyadicMenuPopulationOptimum.bestActual r (2^32)-C|≤C/2^146 := by
  have result := DyadicMenuPopulationOptimum.optimum_161 r _ _ (at_161 good) h
  norm_num at result ⊢
  exact result

end PrimeFactors.ExactDyadicSumMenu
