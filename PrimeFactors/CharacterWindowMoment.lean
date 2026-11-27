import PrimeFactors.CharacterProductBound

/-! A second-moment count for simultaneous positive character tests on a finite
window. All correlations are actual signed sums on the same window. Index pairs
in the off-diagonal term are ordered, so no extra factor of two is needed. -/

namespace PrimeFactors.CharacterWindowMoment

open Finset

/-- The positions where every test takes the value +1. -/
noncomputable def survivors {α : Type*} {k : ℕ} (W : Finset α) (χ : Fin k → α → ℤ) :
    Finset α := by
  classical
  exact W.filter fun x => ∀ i, χ i x = 1

/-- The sum over ordered, unequal indices, separated from the diagonal. -/
theorem square_sum (k : ℕ) (f : Fin k → ℤ) :
    (∑ i, f i)^2 = (∑ i, (f i)^2) + ∑ i, ∑ j ∈ univ.erase i, f i * f j := by
  classical
  rw [sq, sum_mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_erase_add _ _ (mem_univ i), add_comm, sq]

/-- No independence assumption. An upper bound on each signed sum and each
signed cross-correlation gives an upper bound for the number of joint passes. -/
theorem finite {α : Type*} {k : ℕ} (W : Finset α) (χ : Fin k → α → ℤ) (t : ℕ)
    (U : Fin k → ℤ) (V : Fin k → Fin k → ℤ)
    (sq_le : ∀ i x, x ∈ W → (χ i x)^2 ≤ 1)
    (single : ∀ i, ∑ x ∈ W, χ i x ≤ U i)
    (pair : ∀ i j, i ≠ j → ∑ x ∈ W, χ i x * χ j x ≤ V i j) :
    ((survivors W χ).card : ℤ) * ((t : ℤ) + k)^2 ≤
      ((t : ℤ)^2 + k) * W.card + 2*t*(∑ i, U i) +
        ∑ i, ∑ j ∈ univ.erase i, V i j := by
  classical
  let off (x : α) := ∑ i, ∑ j ∈ univ.erase i, χ i x * χ j x
  have individual (x : α) (hx : x ∈ W) :
      ((t : ℤ) + ∑ i, χ i x)^2 ≤ ((t : ℤ)^2 + k) + 2*t*(∑ i, χ i x) + off x := by
    have diag : ∑ i, (χ i x)^2 ≤ (k : ℤ) := by
      simpa using sum_le_sum (s := univ) fun i _ => sq_le i x hx
    have identity := square_sum k (fun i => χ i x)
    change (∑ i, χ i x)^2 = _ + off x at identity
    nlinarith only [diag, identity]
  have linear : (∑ x ∈ W, 2*(t : ℤ)*(∑ i, χ i x)) ≤ 2*t*(∑ i, U i) := by
    rw [← mul_sum, sum_comm]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => single i) (by positivity)
  have cross : ∑ x ∈ W, off x ≤ ∑ i, ∑ j ∈ univ.erase i, V i j := by
    dsimp only [off]
    rw [sum_comm]
    apply sum_le_sum
    intro i _
    rw [sum_comm]
    exact sum_le_sum fun j hj => pair i j (ne_of_mem_erase hj).symm
  calc
    _ = ∑ x ∈ W, if ∀ i, χ i x = 1 then ((t : ℤ)+k)^2 else 0 := by
      simp only [survivors, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero, sum_mul, ite_mul, one_mul, zero_mul]
    _ ≤ ∑ x ∈ W, ((t : ℤ) + ∑ i, χ i x)^2 := by
      apply sum_le_sum
      intro x _
      split_ifs with h
      · simp [h]
      · exact sq_nonneg _
    _ ≤ ∑ x ∈ W, (((t : ℤ)^2 + k) + 2*t*(∑ i, χ i x) + off x) :=
      sum_le_sum fun x hx => individual x hx
    _ ≤ _ := by
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul]
      convert add_le_add (add_le_add_left linear (((t:ℤ)^2+k)*W.card)) cross using 1
      ring

/-- The positions in a progression passing every Jacobi test. -/
noncomputable def hits {k : ℕ} (D : Fin k → ℕ) (first step len : ℕ) : Finset ℕ :=
  survivors (range len) fun i j => TwoCharacterWindow.char (D i) (first+step*j)

/-- The single and product-character budgets can be supplied directly by
`TwoCharacterWindow.progression_bound`, with its stated character hypotheses. -/
theorem jacobi_window {k : ℕ} (D : Fin k → ℕ) (first step len t : ℕ)
    (E : Fin k → ℕ) (F : Fin k → Fin k → ℕ) (nz : ∀ i, D i ≠ 0)
    (single : ∀ i, TwoCharacterWindow.total (D i) first step len ≤ (E i : ℤ))
    (pair : ∀ i j, i ≠ j → TwoCharacterWindow.total (D i * D j) first step len ≤ (F i j : ℤ)) :
    ((hits D first step len).card : ℤ) * ((t : ℤ) + k)^2 ≤
      ((t : ℤ)^2 + k)*len + 2*t*(∑ i, (E i : ℤ)) +
        ∑ i, ∑ j ∈ univ.erase i, (F i j : ℤ) := by
  classical
  let χ (i : Fin k) (j : ℕ) := TwoCharacterWindow.char (D i) (first+step*j)
  have sq_le (i : Fin k) (j : ℕ) (_ : j ∈ range len) : (χ i j)^2 ≤ 1 := by
    dsimp only [χ, TwoCharacterWindow.char]
    rcases jacobiSym.trichotomy ((first + step*j : ℕ) : ℤ) (D i) with h | h | h <;>
      rw [h] <;> decide
  have products (i j : Fin k) (ne : i ≠ j) :
      ∑ x ∈ range len, χ i x * χ j x ≤ (F i j : ℤ) := by
    simpa only [χ, TwoCharacterWindow.total, TwoCharacterWindow.char,
      jacobiSym.mul_right' _ (nz i) (nz j)] using pair i j ne
  simpa only [card_range, hits, χ] using finite (range len) χ t
    (fun i => (E i : ℤ)) (fun i j => (F i j : ℤ)) sq_le single products

/-- A public root at each discriminant puts every actual odd divisor in the
row's simultaneous hit set whenever the divisor lies at that position. -/
theorem divisor_mem {k : ℕ} (D : Fin k → ℕ) {N f first step len j : ℕ}
    (three : ∀ i, D i % 4 = 3) (cop : ∀ i, N.Coprime (D i))
    (root : ∀ i, IsSquare (-(D i : ZMod N))) (odd : Odd f) (dv : f ∣ N)
    (point : first+step*j = f) (inside : j < len) :
    j ∈ hits D first step len := by
  apply mem_filter.mpr
  refine ⟨mem_range.mpr inside,fun i => ?_⟩
  change jacobiSym ((first+step*j : ℕ) : ℤ) (D i) = 1
  rw [point]
  exact ReciprocalDivisorClasses.divisor (three i) odd dv ((cop i).of_dvd_left dv).symm (root i)

/-- Conditional on the published PV estimate, a whole progression can be
priced with only the sum and sum of squares of the supplied integer upper
bounds on the square roots of the discriminants. -/
theorem jacobi_row_budget {k : ℕ} (D r : Fin k → ℕ) (first step len t H C₁ C₂ : ℕ)
    (pv : TwoCharacterWindow.PublishedPV) (large : ∀ i, 100 ≤ D i)
    (three : ∀ i, D i % 4 = 3) (cop : Pairwise fun i j => (D i).Coprime (D j))
    (stride : ∀ i, step.Coprime (D i)) (rad : ∀ i, D i ≤ (r i)^2)
    (bits : ∀ i, D i ≤ 2^H) (one : 5220+347*H ≤ 2220*C₁) (two : 5220+694*H ≤ 2220*C₂) :
    ((hits D first step len).card : ℤ) * ((t : ℤ) + k)^2 ≤
      ((t : ℤ)^2 + k)*len + 2*t*C₁*(∑ i, (r i : ℤ)) +
        C₂*((∑ i, (r i : ℤ))^2 - ∑ i, (r i : ℤ)^2) := by
  classical
  have base := jacobi_window D first step len t (fun i => C₁*r i) (fun i j => C₂*r i*r j)
    (fun i => by have := large i; omega)
    (fun i => CharacterProductBound.single pv (large i) (three i) (stride i)
      (rad i) (bits i) one first len)
    (fun i j h => CharacterProductBound.pair pv (large i) (large j) (three i) (three j)
      (cop h) (stride i) (stride j) (rad i) (rad j) (bits i) (bits j) two first len)
  rw [square_sum k (fun i => (r i : ℤ)), add_sub_cancel_left]
  simpa only [Nat.cast_mul, mul_assoc, mul_sum] using base

end PrimeFactors.CharacterWindowMoment
