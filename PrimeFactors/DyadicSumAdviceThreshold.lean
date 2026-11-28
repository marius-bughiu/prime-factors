import PrimeFactors.ExactDyadicSumMenu
import PrimeFactors.FiniteAdviceMenus

/-! How much additional information could make a list of 2^32 guesses hit
half the sum endings? At a fixed product suffix, 121 and 122 additional
bits lie on opposite sides of the threshold for unrestricted advice. -/
namespace PrimeFactors.DyadicSumAdviceThreshold

open ExactDyadicSumMenu DyadicSumMenuBudget DyadicMenuPopulationOptimum
open Finset
open DyadicSumGuessPopulation (population)
open scoped Classical
attribute [local irreducible] DyadicSumGuessPopulation.population bestActual

/-- On each input a clue selects one list. The clue may depend on the
input pair in any way, including through information expensive to obtain. -/
noncomputable def advisedShare {e K : ℕ} (r : U e)
    (rows : Fin K→Finset (ZMod (2^e))) (clue : ℕ×ℕ→Fin K) : ℝ :=
  (((population r).filter (fun v => ((v.1+v.2:ℕ):ZMod (2^e))∈rows (clue v))).card:ℝ) /
    (population r).card

/-- Even a perfectly chosen clue can cover only labels from the union. -/
theorem advised_upper {e K B : ℕ} (r : U e) (rows : Fin K→Finset (ZMod (2^e)))
    (clue : ℕ×ℕ→Fin K) (size : ∀ i, (rows i).card≤B) :
    advisedShare r rows clue ≤ bestActual r (K*B) := by
  let label := fun v : ℕ×ℕ => ((v.1+v.2:ℕ):ZMod (2^e))
  obtain ⟨S,ok,cover⟩ := FiniteAdviceMenus.upper label rows clue size
  apply le_trans (b:=actualShare r S) _ ((bestActual_spec r (K*B)).2 ⟨S,ok,rfl⟩)
  unfold actualShare advisedShare
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Nat.cast_le.mpr (card_le_card (fun v hv => mem_filter.mpr
    ⟨(mem_filter.mp hv).1,cover v (mem_filter.mp hv).2⟩))

/-- Unrestricted advice can encode the index of a correct block of
guesses. This existence claim supplies no product-only way to choose the block. -/
theorem advised_attains {e K B : ℕ} (r : U e) (pos : 0<K) :
    ∃ rows : Fin K→Finset (ZMod (2^e)), ∃ clue : ℕ×ℕ→Fin K,
      (∀ i, (rows i).card≤B) ∧ advisedShare r rows clue=bestActual r (K*B) := by
  obtain ⟨S,ok,rate⟩ := (bestActual_spec r (K*B)).1
  let label := fun v : ℕ×ℕ => ((v.1+v.2:ℕ):ZMod (2^e))
  obtain ⟨rows,clue,size,same⟩ := FiniteAdviceMenus.realize pos label S ok
  refine ⟨rows,clue,size,?_⟩
  rw [rate,advisedShare,actualShare]
  have equal := filter_congr (s:=population r) (fun v _ => same v)
  change (((population r).filter (fun v => label v∈rows (clue v))).card:ℝ)/_ = _
  rw [equal]

private theorem central {t j b : ℕ} (r : U 161) (good : r.val.val%8=1)
    (depth : 2*(t+1)+j=161) (ht : 2≤t) (hj : 4≤j)
    (lower : 2*DyadicSquareValueCount.count j≤2^b)
    (upper : 2^b≤2*DyadicSquareValueCount.count (j+2))
    {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints (2^161) li) :
    let W := 2^(t+j+2)+(2^b-2*DyadicSquareValueCount.count j)*2^(t+2)
    let C := (W:ℝ)/2^160
    |bestActual r (2^b)-C|≤C/2^146 := by
  have top := optimal_between ht hj good lower upper
  rw [depth] at top
  exact optimum_161 r _ _ top h

/-- The best lists at the two budgets cover approximately 5/12 and
7/12 of the prime population, under the explicit endpoint estimates. -/
theorem neighboring_budgets (r : U 161) (good : r.val.val%8=1)
    {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints (2^161) li) :
    |bestActual r (2^153)-5/12| < 1/2^146 ∧
    |bestActual r (2^154)-7/12| < 1/2^146 := by
  have count (j : ℕ) (pos : 0<j) := DyadicSquareValueCount.closed pos
  have low := central (t:=3) (j:=153) (b:=153) r good (by decide) (by decide) (by decide)
    (by rw [count _ (by decide)]; decide) (by rw [count _ (by decide)]; decide) h
  have high := central (t:=2) (j:=155) (b:=154) r good (by decide) (by decide) (by decide)
    (by rw [count _ (by decide)]; decide) (by rw [count _ (by decide)]; decide) h
  dsimp only at low high
  rw [count _ (by decide)] at low high
  rw [abs_le] at low high
  norm_num at low high
  constructor <;> rw [abs_lt] <;> constructor <;> linarith

/-- At a fixed square product suffix, even 121 further bits cannot make a
list of 2^32 guesses cover 41.7%. With perfect advice 122 bits can cover 58.3%. -/
theorem threshold (r : U 161) (good : r.val.val%8=1)
    {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints (2^161) li) :
    (∀ (rows : Fin (2^121)→Finset (ZMod (2^161))) (clue : ℕ×ℕ→Fin (2^121)),
      (∀ i, (rows i).card≤2^32) → advisedShare r rows clue<417/1000) ∧
    (∃ (rows : Fin (2^122)→Finset (ZMod (2^161))) (clue : ℕ×ℕ→Fin (2^122)),
      (∀ i, (rows i).card≤2^32) ∧ 583/1000<advisedShare r rows clue) := by
  obtain ⟨lo,hi⟩ := neighboring_budgets r good h
  rw [abs_lt] at lo hi
  constructor
  · intro rows clue size
    have bound := advised_upper r rows clue size
    rw [←pow_add] at bound
    exact bound.trans_lt (by linarith only [lo.2])
  · obtain ⟨rows,clue,size,hit⟩ := advised_attains (K:=2^122) (B:=2^32) r (by decide)
    rw [←pow_add] at hit
    exact ⟨rows,clue,size,hit ▸ (by linarith only [hi.1])⟩

end PrimeFactors.DyadicSumAdviceThreshold
