import PrimeFactors.CoprimeGuessTables
import PrimeFactors.PrimeGuessProducts

/-! For a uniform ordered factor-residue pair with product one, the optimum
inclusive sum-residue rank can be an arbitrarily small fraction of the
uniform-order mean. The modulus varies with the requested fraction. -/

namespace PrimeFactors.ArbitrarilyBiasedSumGuesses

open Finset PrimeSquareSumWeights CoprimeGuessTables IndependentGuessRanks
open scoped Classical

noncomputable def primes (bound : ℕ) := bound.primesBelow \ Nat.primesBelow 11

private theorem member {bound p : ℕ} (h : p∈primes bound) : p.Prime ∧ 11≤p := by
  obtain ⟨a,b⟩ := mem_sdiff.mp h
  have prime := (Nat.mem_primesBelow.mp a).2
  exact ⟨prime,le_of_not_gt (fun lt => b (Nat.mem_primesBelow.mpr ⟨lt,prime⟩))⟩

instance (bound : ℕ) (i : primes bound) : Fact i.val.Prime := ⟨(member i.property).1⟩

/-- The product of p² over distinct primes 11 ≤ p < bound. -/
noncomputable abbrev period (bound : ℕ) := modulus (fun i : primes bound => i.val)

abbrev Sums (bound : ℕ) := Labels (period bound) 1

noncomputable def mass {bound : ℕ} (s : Sums bound) : ℝ := weight 1 s.val

/-- This is a comparison of inclusive remainder guesses. No search for an
exact integer sum, or oracle for checking a remainder guess, is assumed. -/
theorem arbitrarily_small_mean {ε : ℝ} (pos : 0<ε) :
    ∃ b : ℕ, ∃ e : Fin (Fintype.card (Sums b)) ≃ Sums b,
      Antitone (mass ∘ e) ∧ meanRank mass e<ε*((Fintype.card (Sums b):ℝ)+1)/2 := by
  classical
  obtain ⟨b,small⟩ := PrimeGuessProducts.small_joint_affinity (half_pos pos)
  let p (i : primes b) := i.val
  have odd (i : primes b) : p i≠2 := by have := (member i.property).2; dsimp [p]; omega
  have unit (i : primes b) : ¬p i∣1 := (member i.property).1.not_dvd_one
  have square (i : primes b) : IsSquare (1:ZMod (p i)) := ⟨1,by simp⟩
  obtain ⟨e,order,upper⟩ := global_rank_bound p Subtype.val_injective 1 odd unit
    (by simpa only [Nat.cast_one] using square)
  refine ⟨b,e,order,?_⟩
  have fsmall : (∏ i : primes b, PrimeSquareGuessAffinity.affinity (p i))<ε/2 := by
    simpa only [p,Finset.prod_coe_sort,primes] using small
  have posMass : 0<total (mass (bound:=b)) :=
    sum_pos (fun s _ => by unfold mass; exact_mod_cast (positive_iff s.val).mpr s.property) univ_nonempty
  have lower := PrimeGuessProducts.mean_ge_one (mass (bound:=b)) (fun _ => by unfold mass; positivity) posMass e
  have bound := PrimeGuessProducts.fraction_of_uniform (Nat.cast_nonneg (Fintype.card (Sums b))) lower upper fsmall pos
  linarith only [bound]

end PrimeFactors.ArbitrarilyBiasedSumGuesses
