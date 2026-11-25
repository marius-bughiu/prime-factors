import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PrimeFactors.UnitQuarticBox

open Finset

/-- The absolute bounds for 1, D, x, D² − 2s² and xD, in that order. -/
def weight (s B : ℕ) : Fin 5 → ℕ := ![1, 2*s, B, 2*s^2, 2*B*s]

/-- Independent coordinate moduli at the five degree-four unit Newton nodes. -/
def moduli (R : ℕ) : Fin 5 → ℕ := ![360*R^4, 360*R^3, 60*R^2, 60*R, 1]

abbrev Labels (R : ℕ) := (i : Fin 5) → Fin (moduli R i)

theorem weight_product (s B : ℕ) : ∏ i, weight s B i = 8*B^2*s^4 := by
  rw [Fin.prod_univ_five]
  change 1*(2*s)*B*(2*s^2)*(2*B*s) = _
  ring

theorem labels_card (R : ℕ) :
    Fintype.card (Labels R) = 466560000*R^10 := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin, Fin.prod_univ_five]
  change (360*R^4)*(360*R^3)*(60*R^2)*(60*R)*1 = _
  ring

theorem labels_index (R : ℕ) :
    Fintype.card (Labels R)*(R^10*12960) = (360*R^4)^5 := by
  rw [labels_card]
  ring

/-- Every integer box of this side length has coordinate differences bounded
by floor((M−1)/(5w)). For positive M and w the side length is ceil(M/(5w)). -/
private def side (M w : ℕ) := (M-1)/(5*w)+1

/-- A volume comparison suffices for any finite labeling of integer vectors.
The two vectors collide and the weighted sum of their absolute differences is
strictly below M. -/
theorem collision {L : Type*} [Fintype L] {M : ℕ} (w : Fin 5 → ℕ)
    (hM : 0 < M) (hw : ∀ i, 0 < w i)
    (room : Fintype.card L * (5^5 * ∏ i, w i) < M^5)
    (label : (Fin 5 → ℤ) → L) :
    ∃ p q : Fin 5 → ℤ, p ≠ q ∧ label p = label q ∧
      (∑ i, |p i-q i| *(w i : ℤ)) < (M : ℤ) := by
  classical
  let Box := (i : Fin 5) → Fin (side M (w i))
  let lift (a : Box) : Fin 5 → ℤ := fun i => ((a i).val : ℤ)
  have cover (i : Fin 5) : M ≤ (5*w i)*side M (w i) := by
    have h := Nat.lt_mul_div_succ (M-1) (Nat.mul_pos (by decide : 0<5) (hw i))
    unfold side
    omega
  have total : M^5 ≤ (5^5 * ∏ i, w i) * ∏ i, side M (w i) := by
    have h := Finset.prod_le_prod' (s := (univ : Finset (Fin 5))) (fun i _ => cover i)
    simpa only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin] using h
  have more : Fintype.card L < Fintype.card Box := by
    apply Nat.lt_of_mul_lt_mul_right (a := 5^5 * ∏ i, w i)
    simpa only [Box, Fintype.card_pi, Fintype.card_fin, Nat.mul_comm] using room.trans_le total
  obtain ⟨a,b,diff,same⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun a => label (lift a)) more
  refine ⟨lift a, lift b, ?_, same, ?_⟩
  · intro eq
    apply diff
    funext i
    apply Fin.ext
    have liftEq : ((a i).val : ℤ) = ((b i).val : ℤ) := congrFun eq i
    exact_mod_cast liftEq
  · have terms (i : Fin 5) : 5*(|(lift a) i-(lift b) i| *(w i : ℤ)) ≤ (M-1 : ℕ) := by
      have ha := (a i).isLt
      have hb := (b i).isLt
      change (a i).val < (M-1)/(5*w i)+1 at ha
      change (b i).val < (M-1)/(5*w i)+1 at hb
      have hab : |(lift a) i-(lift b) i| ≤ ((M-1)/(5*w i) : ℕ) := by
        apply abs_le.mpr
        dsimp [lift]
        omega
      have hmul := mul_le_mul_of_nonneg_right hab (show 0 ≤ (5:ℤ)*w i by positivity)
      have bound := Nat.mul_div_le (M-1) (5*w i)
      have cast : ((5*w i : ℕ) : ℤ)*(((M-1)/(5*w i) : ℕ) : ℤ) ≤ ((M-1 : ℕ):ℤ) := by
        exact_mod_cast bound
      simp only [Nat.cast_mul, Nat.cast_ofNat] at cast
      linarith only [hmul, cast]
    rw [Fin.sum_univ_five]
    have hsub : ((M-1 : ℕ):ℤ) < (M:ℤ) := by omega
    linarith only [terms 0,terms 1,terms 2,terms 3,terms 4,hsub]

/-- The five-coordinate bound for any positive radix whose margin pays for the widths. -/
theorem quartic_collision {L : Type*} [Fintype L] {R s B : ℕ}
    (hr : 0<R) (hs : 0<s) (hB : 0<B)
    (size : Fintype.card L ≤ 466560000*R^10)
    (scale : 5^5 * (∏ i, weight s B i) < R^10*12960)
    (label : (Fin 5 → ℤ) → L) :
    ∃ p q : Fin 5 → ℤ, p ≠ q ∧ label p = label q ∧
      (∑ i, |p i-q i| * (weight s B i : ℤ)) < 360*(R:ℤ)^4 := by
  have positive (i : Fin 5) : 0 < weight s B i := by
    fin_cases i <;> simp [weight, hs, hB]
  have room : Fintype.card L * (5^5 * ∏ i, weight s B i) < (360*R^4)^5 := calc
    _ ≤ (466560000*R^10) * (5^5 * ∏ i, weight s B i) := Nat.mul_le_mul_right _ size
    _ < (466560000*R^10) * (R^10*12960) := Nat.mul_lt_mul_of_pos_left scale (by positivity)
    _ = _ := by ring
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    (collision (weight s B) (by positivity) positive room label)

set_option exponentiation.threshold 16384 in
theorem uniform_scale {s B : ℕ} (hs2 : s^2 ≤ 2^2045) (hB2 : B^2 ≤ 2^2049) :
    5^5 * (∏ i, weight s B i) < ((2:ℕ)^614)^10*12960 := by
  have weightBound : (∏ i, weight s B i) ≤ 2^6142 := calc
    _ = 8*B^2*(s^2)^2 := by rw [weight_product]; ring
    _ ≤ 8*2^2049*(2^2045)^2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 8 hB2) (Nat.pow_le_pow_left hs2 2)
    _ = _ := by decide +kernel
  exact (Nat.mul_le_mul_left _ weightBound).trans_lt (by decide +kernel)

/-- The unit-node margin covers all allowed 2048-bit column weights at stride 2^614. -/
theorem collision_2048_of_card {L : Type*} [Fintype L] {s B : ℕ} (hs : 0<s) (hB : 0<B)
    (hs2 : s^2 ≤ 2^2045) (hB2 : B^2 ≤ 2^2049)
    (size : Fintype.card L ≤ 466560000*((2:ℕ)^614)^10)
    (label : (Fin 5 → ℤ) → L) :
    ∃ p q : Fin 5 → ℤ, p ≠ q ∧ label p = label q ∧
      (∑ i, |p i-q i| * (weight s B i : ℤ)) < 360*((2:ℤ)^614)^4 := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (quartic_collision (R := 2^614) (by positivity) hs hB size (uniform_scale hs2 hB2) label)

theorem collision_2048 {s B : ℕ} (hs : 0<s) (hB : 0<B)
    (hs2 : s^2 ≤ 2^2045) (hB2 : B^2 ≤ 2^2049)
    (label : (Fin 5 → ℤ) → Labels (2^614)) :
    ∃ p q : Fin 5 → ℤ, p ≠ q ∧ label p = label q ∧
      (∑ i, |p i-q i| * (weight s B i : ℤ)) < 360*((2:ℤ)^614)^4 :=
  collision_2048_of_card hs hB hs2 hB2 (labels_card _).le label

end PrimeFactors.UnitQuarticBox
