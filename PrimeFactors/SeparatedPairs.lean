import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

namespace PrimeFactors

/-- In each class, bound the number of near neighbors of any one member.
The remaining pairs have a lower bound from Cauchy–Schwarz after all class
capacities are subtracted. Pairs are ordered. -/
theorem separated_pairs_lower {ι α : Type*} (bins : Finset ι) (points : ι → Finset α)
    (far : α → α → Prop) [DecidableRel far] (cap : ι → ℕ)
    (near : ∀ d ∈ bins, ∀ x ∈ points d,
      ((points d).filter fun y => ¬ far x y).card ≤ cap d) :
    ((∑ d ∈ bins, (points d).card) - ∑ d ∈ bins, cap d)^2 ≤
      bins.card * ∑ d ∈ bins, ∑ x ∈ points d, ((points d).filter (far x)).card := by
  classical
  let excess := fun d => (points d).card - cap d
  have total : (∑ d ∈ bins, (points d).card) - ∑ d ∈ bins, cap d ≤ ∑ d ∈ bins, excess d := by
    apply Nat.sub_le_iff_le_add.mpr
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro d _
    dsimp [excess]
    omega
  have localBound (d : ι) (hd : d ∈ bins) :
      excess d ^ 2 ≤ ∑ x ∈ points d, ((points d).filter (far x)).card := by
    calc
      _ ≤ (points d).card * excess d := by
        rw [pow_two]
        exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = ∑ _x ∈ points d, excess d := by simp
      _ ≤ _ := Finset.sum_le_sum fun x hx => by
        have split := Finset.filter_card_add_filter_neg_card_eq_card (s := points d) (far x)
        have h := near d hd x hx
        dsimp [excess]
        omega
  calc
    _ ≤ (∑ d ∈ bins, excess d)^2 := Nat.pow_le_pow_left total 2
    _ ≤ bins.card * ∑ d ∈ bins, excess d^2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) bins (fun _ => 1) excess
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.sum_le_sum localBound)

end PrimeFactors
