import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! One-based expected guessing rank for finite probability tables.
For the normalized first-moment bound see Sason and Verdú, Theorem 5(a),
equation (73) with ρ=1 (https://arxiv.org/abs/1801.01265), and earlier
guesswork bounds of Arıkan (https://doi.org/10.1109/18.481781). -/

namespace PrimeFactors.IndependentGuessRanks

open Finset Real

noncomputable def total {α : Type*} [Fintype α] (w : α → ℝ) := ∑ i, w i

noncomputable def rootTotal {α : Type*} [Fintype α] (w : α → ℝ) := ∑ i, sqrt (w i)

/-- Squared Hellinger affinity to the uniform distribution, for a nonzero
unnormalized nonnegative weight table. -/
noncomputable def affinity {α : Type*} [Fintype α] (w : α → ℝ) :=
  (rootTotal w)^2 / ((Fintype.card α : ℝ) * total w)

/-- Unnormalized weights are counted once for each inclusive guess. -/
theorem rank_bound {k : ℕ} (w : Fin k → ℝ) (nn : ∀ i, 0 ≤ w i) (sorted : Antitone w) :
    2 * (∑ i, ((i.val:ℝ)+1) * w i) ≤ (∑ i, w i) + (∑ i, sqrt (w i))^2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    let v := fun i : Fin k => w i.castSucc
    let z := w (Fin.last k)
    have prev := ih v (fun i => nn i.castSucc)
      (fun _ _ h => sorted (Fin.castSucc_le_castSucc_iff.mpr h))
    have hz : 0 ≤ z := nn _
    have each (i : Fin k) : z ≤ sqrt (v i) * sqrt z := by
      have h : z ≤ v i := sorted (Fin.le_last _)
      calc
        z = sqrt z * sqrt z := (mul_self_sqrt hz).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (sqrt_le_sqrt h) (sqrt_nonneg _)
    have cross := Finset.sum_le_sum (s:=univ) (fun i _ => each i)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ←sum_mul] at cross
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc (f:=w),
      Fin.sum_univ_castSucc (f:=fun i => sqrt (w i))]
    change 2*((∑ i, ((i.val:ℝ)+1)*v i)+((k:ℝ)+1)*z) ≤
      (∑ i, v i)+z+((∑ i, sqrt (v i))+sqrt z)^2
    nlinarith only [prev,cross,sq_sqrt hz]

noncomputable def meanRank {α : Type*} [Fintype α] (w : α → ℝ)
    (e : Fin (Fintype.card α) ≃ α) := (∑ i, ((i.val:ℝ)+1)*w (e i)) / total w

/-- A decreasing probability order exists on every positive-mass finite
table and satisfies the normalized first-moment bound. Ties may be arbitrary. -/
theorem exists_rank_bound {α : Type*} [Fintype α] [Nonempty α] (w : α → ℝ)
    (nn : ∀ i, 0 ≤ w i) (mass : 0 < total w) :
    ∃ e : Fin (Fintype.card α) ≃ α, Antitone (w ∘ e) ∧
      2*meanRank w e ≤ 1 + (Fintype.card α : ℝ)*affinity w := by
  classical
  let e₀ := (Fintype.equivFin α).symm
  let f := fun i => -w (e₀ i)
  let e := (Tuple.sort f).trans e₀
  have sorted : Antitone (w ∘ e) := by
    intro i j h
    exact neg_le_neg_iff.mp (Tuple.monotone_sort f h)
  refine ⟨e,sorted,?_⟩
  have bound := rank_bound (w ∘ e) (fun i => nn (e i)) sorted
  have m : (∑ i, (w ∘ e) i) = total w := e.sum_comp w
  have a : (∑ i, sqrt ((w ∘ e) i)) = rootTotal w := e.sum_comp (fun x => sqrt (w x))
  rw [m,a] at bound
  have k : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have cancel : (Fintype.card α : ℝ) * affinity w = (rootTotal w)^2 / total w := by
    unfold affinity
    field_simp
    ring
  rw [cancel, meanRank, ←mul_div_assoc]
  calc
    _ ≤ (total w + (rootTotal w)^2) / total w := div_le_div_of_nonneg_right bound mass.le
    _ = _ := by rw [add_div, div_self mass.ne']

private theorem sqrt_product {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (nn : ∀ i, 0 ≤ g i) : sqrt (∏ i∈s, g i) = ∏ i∈s, sqrt (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [prod_insert hi, prod_insert hi, sqrt_mul (nn i), ih]

/-- For independent finite coordinates the squared affinity is the product
of the local squared affinities, even for different label alphabets. -/
theorem affinity_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (w : ∀ i, α i → ℝ) (nn : ∀ i x, 0 ≤ w i x) :
    affinity (fun x : ∀ i, α i => ∏ i, w i (x i)) = ∏ i, affinity (w i) := by
  unfold affinity rootTotal total
  simp_rw [sqrt_product univ _ (fun i => nn i _)]
  rw [←Fintype.prod_sum (fun i x => sqrt (w i x)), ←Fintype.prod_sum w,
    Fintype.card_pi, Nat.cast_prod, ←prod_pow, ←prod_mul_distrib, ←prod_div_distrib]

/-- A sorted independent-product table has an achievable mean-rank bound
computed from the coordinate tables alone. -/
theorem product_rank_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] (w : ∀ i, α i → ℝ)
    (nn : ∀ i x, 0 ≤ w i x) (mass : ∀ i, 0 < total (w i)) :
    let p := fun x : ∀ i, α i => ∏ i, w i (x i)
    ∃ e : Fin (Fintype.card (∀ i, α i)) ≃ (∀ i, α i), Antitone (p ∘ e) ∧
      2*meanRank p e ≤ 1 + ∏ i, ((Fintype.card (α i) : ℝ) * affinity (w i)) := by
  classical
  dsimp only
  have m : 0 < total (fun x : ∀ i, α i => ∏ i, w i (x i)) := by
    unfold total
    rw [←Fintype.prod_sum]
    exact prod_pos (fun i _ => mass i)
  obtain ⟨e,sorted,bound⟩ := exists_rank_bound _ (fun x => prod_nonneg (fun i _ => nn i (x i))) m
  refine ⟨e,sorted,?_⟩
  rwa [affinity_product w nn, Fintype.card_pi, Nat.cast_prod, ←prod_mul_distrib] at bound

end PrimeFactors.IndependentGuessRanks
