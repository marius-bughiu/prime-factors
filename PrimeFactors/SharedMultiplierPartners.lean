import PrimeFactors.MultiplierDivisorReach
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! A single pair of weights can reach only a short interval of partners
when its weighted trace lies close to its geometric minimum. -/
namespace PrimeFactors.SharedMultiplierPartners

open Real

set_option maxRecDepth 4096
set_option exponentiation.threshold 2048

/-- Square-root coordinates turn a bound on the excess into a linear strip.
The ratio of the two weight coordinates is controlled by just one hit. -/
private theorem root_scale {A B P Q s r : ℝ} (B1 : 1 ≤ B) (P0 : 0 < P)
    (sP : s ≤ P) (QP : Q ≤ 2*P) (near : A*P-B*Q ≤ s)
    (r2 : r^2 = A*B) : r ≤ 2*B := by
  have b0 : 0 ≤ B := by linarith
  have bp : P ≤ B*P := le_mul_of_one_le_left P0.le B1
  have ap : A*P ≤ (3*B)*P := by
    nlinarith only [near, sP, bp, mul_le_mul_of_nonneg_left QP b0]
  have aB := le_of_mul_le_mul_right ap P0
  have h : r^2 ≤ (2*B)^2 := by
    nlinarith only [r2, mul_le_mul_of_nonneg_right aB b0, sq_nonneg B]
  exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq h (by linarith))

/-- Diameter in the original integer coordinates after bounding the two
square roots from above. -/
private theorem diameter {A B P x y s C r : ℝ}
    (x0 : 0 ≤ x) (xy : x ≤ y) (yC : y ≤ C) (s0 : 0 ≤ s)
    (scale : r ≤ 2*B) (left : A*P-B*x ≤ s) (right : -(s) ≤ A*P-B*y) :
    r*(y^2-x^2) ≤ 8*C*s := by
  have y0 := x0.trans xy
  have gap : B*(y-x) ≤ 2*s := by linarith
  calc r*(y^2-x^2) ≤ (2*B)*(y^2-x^2) :=
        mul_le_mul_of_nonneg_right scale (by nlinarith only [sq_le_sq₀ x0 (x0.trans xy) |>.2 xy])
       _ = 2*(B*(y-x))*(y+x) := by ring
       _ ≤ 2*(2*s)*(y+x) := by gcongr
       _ ≤ 2*(2*s)*(2*C) := by gcongr; linarith
       _ = 8*C*s := by ring

/-- For a fixed smaller factor and a fixed *ordered* pair of weights, bound
the number of integer partners whose true trace is within 2^32+1 of minimum.
No primality or upper bound on the multiplier is required for this step. -/
theorem count {p a b k : ℕ} (ap : 0<a) (bp : 0<b) (prod : a*b=k)
    (lower : 2^1023≤p) (_upper : p<2^1024) (Q : Finset ℕ)
    (witness : ∀ q∈Q, p≤q ∧ q<2^1024 ∧
      (sqrt ((a*p:ℕ):ℝ)-sqrt ((b*q:ℕ):ℝ))^2 < (2:ℝ)^32+1) :
    (Q.card:ℝ) ≤ 1+8*(2:ℝ)^512*65537/sqrt (sqrt k) := by
  have kpos : 0<k := prod ▸ Nat.mul_pos ap bp
  have rpos : 0 < sqrt (sqrt k) := sqrt_pos.mpr (sqrt_pos.mpr (by exact_mod_cast kpos))
  rcases Q.eq_empty_or_nonempty with rfl | ne
  · simp only [Finset.card_empty, Nat.cast_zero]; positivity
  let x := Q.min' ne
  let y := Q.max' ne
  have hx := witness x (Q.min'_mem ne)
  have hy := witness y (Q.max'_mem ne)
  have xy : x ≤ y := Q.le_max' _ (Q.min'_mem ne)
  have linear {q : ℕ} (h : (sqrt ((a*p:ℕ):ℝ)-sqrt ((b*q:ℕ):ℝ))^2 < (2:ℝ)^32+1) :
      -(65537:ℝ) < sqrt a*sqrt p-sqrt b*sqrt q ∧
        sqrt a*sqrt p-sqrt b*sqrt q < 65537 := by
    push_cast at h
    rw [sqrt_mul (Nat.cast_nonneg _), sqrt_mul (Nat.cast_nonneg _)] at h
    exact abs_lt_of_sq_lt_sq' (h.trans (by norm_num)) (by norm_num)
  have plarge : 65537 ≤ sqrt p := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    exact_mod_cast (show 65537^2 ≤ p by exact le_trans (by decide +kernel : 65537^2 ≤ 2^1023) lower)
  have ppos : 0 < sqrt p := by linarith
  have b1 : (1:ℝ) ≤ sqrt b := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by exact_mod_cast (show 1^2 ≤ b by omega))
  have yp : sqrt y ≤ 2*sqrt p := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have yn : y≤2*p := by have h := hy.2.1; omega
    calc (y:ℝ) ≤ 2*p := by exact_mod_cast yn
         _ ≤ (2*sqrt p)^2 := by rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg p)]; linarith only [(Nat.cast_nonneg p : (0:ℝ) ≤ p)]
  have rk : (sqrt (sqrt k))^2 = sqrt a * sqrt b := by
    rw [sq_sqrt (sqrt_nonneg _), ←prod, Nat.cast_mul, sqrt_mul (Nat.cast_nonneg _)]
  have scale := root_scale b1 ppos plarge yp (linear hy.2.2).2.le rk
  have large : sqrt y ≤ (2:ℝ)^512 := by
    apply sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [← pow_mul]
    exact_mod_cast hy.2.1.le
  have rxy : sqrt (x:ℝ) ≤ sqrt y := sqrt_le_sqrt (by exact_mod_cast xy)
  have diam := diameter (sqrt_nonneg _) rxy large (by norm_num : (0:ℝ)≤65537)
    scale (linear hx.2.2).2.le (linear hy.2.2).1.le
  rw [sq_sqrt (Nat.cast_nonneg y),sq_sqrt (Nat.cast_nonneg x), mul_comm] at diam
  have card := Finset.card_le_card (show Q⊆Finset.Icc x y from
      fun z hz => Finset.mem_Icc.mpr ⟨Q.min'_le z hz,Q.le_max' z hz⟩)
  rw [Nat.card_Icc] at card
  have small : Q.card ≤ (y-x)+1 := by omega
  have realSmall : (Q.card:ℝ) ≤ (y:ℝ)-x+1 := by
    simpa only [Nat.cast_add,Nat.cast_sub xy,Nat.cast_one] using (show (Q.card:ℝ)≤((y-x+1:ℕ):ℝ) by exact_mod_cast small)
  linarith only [realSmall, (le_div_iff₀ rpos).mpr diam]

end PrimeFactors.SharedMultiplierPartners
