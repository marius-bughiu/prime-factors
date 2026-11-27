import PrimeFactors.DiscriminantStride
import Mathlib.Data.Real.Sqrt

/-! The two balanced intervals for (p−1)(q−1) and (p+1)(q+1) cannot
contain numbers with the same squarefree part, even at different candidate
sums. This lets one scale test consider both signs. -/

namespace PrimeFactors.OppositeSquareScaleBands

/-- The strict lower bound reflects distinct factors. -/
def InSumWindow (n s : ℕ) : Prop := 4*n < s^2 ∧ 2*s^2 ≤ 9*n

theorem balanced_sum {p q : ℕ} (ordered : p < q) (balanced : q < 2*p) :
    InSumWindow (p*q) (p+q) := by
  constructor
  · have pos : (0:ℤ) < (q:ℤ)-p := by omega
    zify
    nlinarith only [mul_pos pos pos]
  · have a : (0:ℤ) ≤ 2*(p:ℤ)-q := by omega
    have b : (0:ℤ) ≤ 2*(q:ℤ)-p := by omega
    zify
    nlinarith only [mul_nonneg a b]

private theorem lower_sum {l s : ℝ} (hl : 3 ≤ l) (hs : 0 ≤ s)
    (lo : 4*l^2 < s^2) : 2*l < s := by
  by_contra! h
  nlinarith only [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 2*l+s by linarith),lo]

private theorem upper_sum {l s : ℝ} (hl : 3 ≤ l)
    (hi : 2*s^2 ≤ 9*l^2) : s ≤ 17/8*l := by
  by_contra! h
  nlinarith only [mul_pos (sub_pos.mpr h) (show 0 < s+17/8*l by linarith),hi,sq_nonneg l]

private theorem gap_small {l v w s u : ℝ} (hl : 3 ≤ l) (hv : 0 ≤ v)
    (us : s ≤ 17/8*l) (uu : u ≤ 17/8*l)
    (minus : v^2+s = l^2+1) (plus : w^2 = l^2+1+u) : w-v ≤ 11/5 := by
  have vlow : l-11/10 ≤ v := by
    by_contra! h
    nlinarith only [mul_pos (sub_pos.mpr h) (show 0 < l-11/10+v by linarith),minus,us,hl]
  have whigh : w ≤ l+11/10 := by
    by_contra! h
    nlinarith only [mul_pos (sub_pos.mpr h) (show 0 < w+(l+11/10) by linarith),plus,uu,hl]
  linarith

private theorem gap_large {l v w s u : ℝ} (hl : 3 ≤ l) (hw : 0 ≤ w)
    (ls : 2*l < s) (lu : 2*l < u)
    (minus : v^2+s = l^2+1) (plus : w^2 = l^2+1+u) : 2 < w-v := by
  have vhigh : v < l-1 := by
    by_contra! h
    nlinarith only [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ v+(l-1) by linarith),minus,ls]
  have wlow : l+1 < w := by
    by_contra! h
    nlinarith only [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ l+1+w by linarith),plus,lu]
  linarith

/-- If both candidate sums exceed the lower bound, the squared difference
of the scaled roots exceeds four. If both are within the upper bound,
that integer is at most four. -/
theorem gap_threshold {n t y z s u : ℕ} (large : 9 ≤ n) (ordered : y ≤ z)
    (minus : t*y^2+s = n+1) (plus : t*z^2 = n+1+u) :
    (4*n < s^2 → 4*n < u^2 → 4 < t*(z-y)^2) ∧
    (2*s^2 ≤ 9*n → 2*u^2 ≤ 9*n → t*(z-y)^2 ≤ 4) := by
  let l := Real.sqrt n
  let c := Real.sqrt t
  have lsq : l^2=(n:ℝ) := Real.sq_sqrt (by positivity)
  have csq : c^2=(t:ℝ) := Real.sq_sqrt (by positivity)
  have hl : 3 ≤ l := calc
    (3:ℝ) = Real.sqrt 9 := by rw [show (9:ℝ)=3^2 by norm_num,Real.sqrt_sq (by norm_num)]
    _ ≤ l := Real.sqrt_le_sqrt (by exact_mod_cast large)
  have lower (a : ℕ) (al : 4*n < a^2) := lower_sum (s:=(a:ℝ)) hl (by positivity)
    (by rw [lsq]; exact_mod_cast al)
  have upper (a : ℕ) (au : 2*a^2 ≤ 9*n) := upper_sum (s:=(a:ℝ)) hl
    (by rw [lsq]; exact_mod_cast au)
  have cn : 0 ≤ c := Real.sqrt_nonneg _
  have m : (c*(y:ℝ))^2+s=l^2+1 := by rw [mul_pow,csq,lsq]; exact_mod_cast minus
  have p : (c*(z:ℝ))^2=l^2+1+u := by rw [mul_pow,csq,lsq]; exact_mod_cast plus
  have hv := mul_nonneg cn (show 0 ≤ (y:ℝ) by positivity)
  have hw := mul_nonneg cn (show 0 ≤ (z:ℝ) by positivity)
  have diff : 0 ≤ c*z-c*y := sub_nonneg.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast ordered) cn)
  have eqn : ((t*(z-y)^2:ℕ):ℝ) = (c*z-c*y)^2 := by
    push_cast [Nat.cast_sub ordered]
    rw [←csq]
    ring
  constructor
  · intro sl ul
    have blo := gap_large hl hw (lower s sl) (lower u ul) m p
    have limit : (4:ℝ) < ((t*(z-y)^2:ℕ):ℝ) := by
      rw [eqn]
      nlinarith only [mul_pos (sub_pos.mpr blo) (show 0 < c*z-c*y+2 by linarith)]
    exact_mod_cast limit
  · intro su uu
    have bhi := gap_small hl hv (upper s su) (upper u uu) m p
    have limit : ((t*(z-y)^2:ℕ):ℝ) < 5 := by
      rw [eqn]
      nlinarith only [mul_nonneg (sub_nonneg.mpr bhi) (show 0 ≤ 11/5+(c*z-c*y) by linarith)]
    have final : t*(z-y)^2 < 5 := by exact_mod_cast limit
    omega

/-- The predecessor and successor bands never share a square scale. -/
theorem disjoint {n t y z s u : ℕ} (large : 9 ≤ n) (ordered : y ≤ z)
    (minus : t*y^2+s = n+1) (plus : t*z^2 = n+1+u)
    (hs : InSumWindow n s) (hu : InSumWindow n u) : False := by
  obtain ⟨lo,hi⟩ := gap_threshold large ordered minus plus
  exact Nat.not_lt_of_ge (hi hs.2 hu.2) (lo hs.1 hu.1)

/-- A small gap between the scaled roots calls for the larger sum, and a
large gap calls for the smaller. The selected sum covers both signs. -/
theorem select_sum {n t y z s u : ℕ} (large : 9 ≤ n) (ordered : y ≤ z)
    (minus : t*y^2+s = n+1) (plus : t*z^2 = n+1+u) :
    InSumWindow n (if t*(z-y)^2 ≤ 4 then max s u else min s u) ↔
      InSumWindow n s ∨ InSumWindow n u := by
  obtain ⟨lo,hi⟩ := gap_threshold large ordered minus plus
  by_cases order : s ≤ u
  · rw [max_eq_right order,min_eq_left order]
    have squares := Nat.pow_le_pow_left order 2
    split_ifs with gap
    · exact ⟨Or.inr,fun h => h.elim (fun hs => False.elim (Nat.not_lt_of_ge gap (lo hs.1 (hs.1.trans_le squares)))) id⟩
    · exact ⟨Or.inl,fun h => h.elim id (fun hu => False.elim (gap (hi ((Nat.mul_le_mul_left 2 squares).trans hu.2) hu.2)))⟩
  · have rev := Nat.le_of_not_ge order
    rw [max_eq_left rev,min_eq_right rev]
    have squares := Nat.pow_le_pow_left rev 2
    split_ifs with gap
    · exact ⟨Or.inl,fun h => h.elim id (fun hu => False.elim (Nat.not_lt_of_ge gap (lo (hu.1.trans_le squares) hu.1)))⟩
    · exact ⟨Or.inr,fun h => h.elim (fun hs => False.elim (gap (hi hs.2 ((Nat.mul_le_mul_left 2 squares).trans hs.2)))) id⟩

end PrimeFactors.OppositeSquareScaleBands
