import PrimeFactors.ArbitrarilyBiasedSumGuesses
import PrimeFactors.SplittingGuessPrimes

/-! The asymptotic relative remainder-guessing gain is available at every
fixed positive integer product value. The finite residue population and
the modulus both vary; this gives no oracle for the actual integer sum. -/

namespace PrimeFactors.FixedProductSumGuesses

open Finset CoprimeGuessTables IndependentGuessRanks PrimeSquareSumWeights
open scoped Classical

noncomputable def weightAt {n : ℕ} {m : ℕ+} (s : Labels (m:ℕ) n) : ℝ := weight n s.val

/-- For any fixed positive product, one can choose distinct prime squares
with an arbitrarily small optimal-to-random mean-rank ratio for the truly
attainable sum labels. Every chosen prime can exceed a requested cutoff. -/
theorem every_positive (n cut : ℕ) (hn : 0<n) {ε : ℝ} (ep : 0<ε) :
    ∃ S : Finset ℕ, (∀ p∈S, p.Prime ∧ cut≤p ∧ ¬p∣n ∧ IsSquare (n:ZMod p)) ∧
      ∃ m : ℕ+, (m:ℕ)=∏ p∈S,p^2 ∧
        ∃ e : Fin (Fintype.card (Labels (m:ℕ) n)) ≃ Labels (m:ℕ) n,
          Antitone (weightAt ∘ e) ∧
          meanRank weightAt e<ε*((Fintype.card (Labels (m:ℕ) n):ℝ)+1)/2 := by
  classical
  obtain ⟨S,good,big⟩ := SplittingGuessPrimes.large_tail hn (max 11 cut) (-2*Real.log (ε/2))
  let p (i : S) := i.val
  letI (i : S) : Fact (p i).Prime := ⟨(good i.val i.property).1⟩
  have large (i : S) : 11≤p i := (le_max_left ..).trans (good i.val i.property).2.1
  have fa : ∏ i : S, PrimeSquareGuessAffinity.affinity (p i)<ε/2 := by
    rw [Finset.prod_coe_sort]
    apply PrimeGuessProducts.finite_small S _ (fun a _ => PrimeSquareGuessAffinity.affinity_nonneg a)
    · intro a ha
      haveI : Fact a.Prime := ⟨(good a ha).1⟩
      linarith only [PrimeSquareGuessAffinity.deficit_lower (large ⟨a,ha⟩)]
    · exact half_pos ep
    · exact big
  have mp : 0<modulus p := Nat.pos_of_ne_zero (NeZero.ne _)
  let m : ℕ+ := ⟨modulus p,mp⟩
  refine ⟨S,fun a ha => ⟨(good a ha).1,(le_max_right ..).trans (good a ha).2.1,(good a ha).2.2⟩,m,?_,?_⟩
  · change (∏ i : S, i.val^2) = ∏ a∈S,a^2
    exact Finset.prod_coe_sort S (fun a : ℕ => a^2)
  have odd (i : S) : p i≠2 := by have := large i; omega
  obtain ⟨e,ord,upper⟩ := global_rank_bound p Subtype.val_injective n odd
    (fun i => (good i.val i.property).2.2.1) (fun i => (good i.val i.property).2.2.2)
  refine ⟨e,ord,?_⟩
  have mass : 0<total (weightAt (n:=n) (m:=m)) := by
    apply sum_pos
    · intro s _
      unfold weightAt
      exact_mod_cast (positive_iff s.val).mpr s.property
    · exact univ_nonempty
  have lower := PrimeGuessProducts.mean_ge_one (weightAt (n:=n) (m:=m))
    (fun _ => by unfold weightAt; positivity) mass e
  have bound := PrimeGuessProducts.fraction_of_uniform (Nat.cast_nonneg (Fintype.card (Labels (m:ℕ) n)))
    lower upper fa ep
  linarith only [bound]

end PrimeFactors.FixedProductSumGuesses
