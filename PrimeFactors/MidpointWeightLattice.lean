import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors

namespace MidpointWeightLattice

/-- Split a pair into half-sum and half-difference, retaining a parity bit. -/
private def split (x y : ℤ) : ℤ × ℤ :=
  ((x+y)/2, x-(x+y)/2)

private theorem split_first (x y : ℤ) :
    x = (split x y).1 + (split x y).2 := by dsimp [split]; omega

private theorem split_second (x y : ℤ) :
    y = (split x y).1 - (split x y).2 + (x+y)%2 := by dsimp [split]; omega

private def residue (x : ℤ) (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨(x % n).toNat, by
    have pos : 0 < (n : ℤ) := by exact_mod_cast hn
    have ub := Int.emod_lt_of_pos x pos
    omega⟩

private theorem residue_val (x : ℤ) (n : ℕ) (hn : 0 < n) :
    ((residue x n hn).val : ℤ) = x % n := by
  have pos : 0 < (n : ℤ) := by exact_mod_cast hn
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

private abbrev Labels (H G R : ℕ) := Fin 2 × Fin H × Fin G × Fin 2 × Fin R

private def errorX {H G R : ℕ} (e : Labels H G R) : ℤ :=
  e.2.1.val + (e.2.2.1.val : ℤ) + (G : ℤ)*e.2.2.2.1.val

private def errorY {H G R : ℕ} (e : Labels H G R) : ℤ :=
  e.2.1.val - (e.2.2.1.val : ℤ) - (G : ℤ)*e.2.2.2.1.val + e.1.val

private def record (H G R : ℕ) (hH : 0 < H) (hG : 0 < G) (hR : 0 < R)
    (s X Y : ℤ) : (ℤ × ℤ) × Labels H G R :=
  let u := (split X Y).1
  let v := (split X Y).2
  let a := u / H
  let b := v / G
  let w := split a b
  (w, residue (X+Y) 2 (by decide), residue u H hH, residue v G hG,
    residue (a+b) 2 (by decide), residue (w.2-s*w.1) R hR)

private theorem rebuild (H G R : ℕ) (hH : 0 < H) (hG : 0 < G) (hR : 0 < R)
    (s X Y : ℤ) :
    let (w, e) := record H G R hH hG hR s X Y
    X = H*(w.1+w.2) + G*(w.1-w.2) + errorX e ∧
    Y = H*(w.1+w.2) - G*(w.1-w.2) + errorY e := by
  let u := (split X Y).1
  let v := (split X Y).2
  let a := u / H
  let b := v / G
  let w := split a b
  have x : X = u+v := split_first _ _
  have y : Y = u-v+(X+Y)%2 := split_second _ _
  have a' : a = w.1+w.2 := split_first _ _
  have b' : b = w.1-w.2+(a+b)%2 := split_second _ _
  have hu : u % H + H*a = u := Int.emod_add_ediv _ _
  have hv : v % G + G*b = v := Int.emod_add_ediv _ _
  dsimp only [record, errorX, errorY, Prod.fst, Prod.snd]
  simp only [residue_val]
  change X = H*(w.1+w.2) + G*(w.1-w.2) + (u%H + v%G + G*((a+b)%2)) ∧
    Y = H*(w.1+w.2) - G*(w.1-w.2) + (u%H - v%G - G*((a+b)%2) + (X+Y)%2)
  constructor
  · linear_combination x - hu - hv + H*a' + G*b'
  · linear_combination y - hu + hv + H*a' - G*b'

private theorem slope_residue (H G R : ℕ) (hH : 0 < H) (hG : 0 < G) (hR : 0 < R)
    (s X Y : ℤ) :
    let (w,e) := record H G R hH hG hR s X Y
    (e.2.2.2.2.val : ℤ) = (w.2-s*w.1) % R := residue_val _ _ hR

private theorem norm_lt {x y r : ℤ} (plus : |x+y| < r) (minus : |x-y| < r) :
    |x| + |y| < r := by
  rw [abs_lt] at plus minus
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]; omega
  · rw [abs_of_nonneg hx, abs_of_nonpos hy]; omega
  · rw [abs_of_nonpos hx, abs_of_nonneg hy]; omega
  · rw [abs_of_nonpos hx, abs_of_nonpos hy]; omega

/-- An arbitrary collection of more than 4HGR integer points has a pair
whose difference is the image of stationary weights. The choice of the
collection can impose additional bounds on that difference. -/
theorem lattice_collision {P : Type*} [Fintype P] (point : P → ℤ × ℤ)
    (H G R : ℕ) (hH : 0 < H) (hG : 0 < G) (hR : 0 < R)
    (large : 4*H*G*R < Fintype.card P) (s : ℤ) :
    ∃ p q : P, p ≠ q ∧ ∃ A B : ℤ, B ≡ s*A [ZMOD (R:ℤ)] ∧
      (point p).1-(point q).1 = H*(A+B)+G*(A-B) ∧
      (point p).2-(point q).2 = H*(A+B)-G*(A-B) := by
  let encode (p : P) := record H G R hH hG hR s (point p).1 (point p).2
  have size : Fintype.card (Labels H G R) < Fintype.card P := by
    simpa only [Labels, Fintype.card_prod, Fintype.card_fin, Nat.mul_left_comm,
      Nat.mul_comm, Nat.mul_assoc, show 4=2*2 by decide] using large
  obtain ⟨p,q,neq,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun p => (encode p).2) size
  let A := (encode p).1.1 - (encode q).1.1
  let B := (encode p).1.2 - (encode q).1.2
  have rebuild' (t : P) :
      (point t).1 = H*((encode t).1.1+(encode t).1.2) +
        G*((encode t).1.1-(encode t).1.2) + errorX (encode t).2 ∧
      (point t).2 = H*((encode t).1.1+(encode t).1.2) -
        G*((encode t).1.1-(encode t).1.2) + errorY (encode t).2 :=
    rebuild H G R hH hG hR s (point t).1 (point t).2
  have hp := rebuild' p
  have hq := rebuild' q
  rw [eq] at hp
  have dx : (point p).1 - (point q).1 = H*(A+B) + G*(A-B) := by
    dsimp only [A,B]; linear_combination hp.1 - hq.1
  have dy : (point p).2 - (point q).2 = H*(A+B) - G*(A-B) := by
    dsimp only [A,B]; linear_combination hp.2 - hq.2
  refine ⟨p,q,neq,A,B,?_,dx,dy⟩
  have sp := slope_residue H G R hH hG hR s (point p).1 (point p).2
  have sq := slope_residue H G R hH hG hR s (point q).1 (point q).2
  change ((encode p).2.2.2.2.2.val : ℤ) = ((encode p).1.2-s*(encode p).1.1) % R at sp
  change ((encode q).2.2.2.2.2.val : ℤ) = ((encode q).1.2-s*(encode q).1.1) % R at sq
  rw [eq] at sp
  have lane : (encode p).1.2 - s*(encode p).1.1 ≡
      (encode q).1.2 - s*(encode q).1.1 [ZMOD (R:ℤ)] := sp.symm.trans sq
  apply Int.modEq_iff_dvd.mpr
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp lane
  exact ⟨k, by dsimp only [A,B]; linear_combination hk⟩

end MidpointWeightLattice

open MidpointWeightLattice in
/-- Every slope admits nonzero stationary weights of width strictly less
than R² once the weighted diamond passes the integer-area threshold. -/
theorem exists_short_midpoint_weights (H G R : ℕ) (hH : 0 < H) (hG : 0 < G)
    (hR : 0 < R) (area : 4*H*G < R^3) (s : ℤ) :
    ∃ A B : ℤ, (A ≠ 0 ∨ B ≠ 0) ∧ B ≡ s*A [ZMOD (R:ℤ)] ∧
      H*|A+B| + G*|A-B| < (R:ℤ)^2 := by
  let point (p : Fin (R^2) × Fin (R^2)) : ℤ × ℤ := (p.1, p.2)
  have size : 4*H*G*R < Fintype.card (Fin (R^2) × Fin (R^2)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    calc
      _ < R^3*R := Nat.mul_lt_mul_of_pos_right area hR
      _ = _ := by ring
  obtain ⟨p,q,neq,A,B,lane,dx,dy⟩ := lattice_collision point H G R hH hG hR size s
  change (p.1:ℤ)-q.1 = _ at dx
  change (p.2:ℤ)-q.2 = _ at dy
  have bounds (i j : Fin (R^2)) : |(i : ℤ)-j| < (R:ℤ)^2 := by
    have hi : (i : ℤ) < (R:ℤ)^2 := by exact_mod_cast i.isLt
    have hj : (j : ℤ) < (R:ℤ)^2 := by exact_mod_cast j.isLt
    have hi0 : 0 ≤ (i:ℤ) := by positivity
    have hj0 : 0 ≤ (j:ℤ) := by positivity
    rw [abs_lt]; omega
  refine ⟨A,B,?_,?_,?_⟩
  · by_contra! zeros
    rw [zeros.1, zeros.2] at dx dy
    simp only [add_zero, sub_zero, mul_zero] at dx dy
    apply neq
    apply Prod.ext <;> apply Fin.ext <;> omega
  · exact lane
  · have near := norm_lt (x := (H:ℤ)*(A+B)) (y := (G:ℤ)*(A-B))
        (by rw [←dx]; apply bounds) (by rw [←dy]; apply bounds)
    simpa only [abs_mul, abs_of_nonneg (Int.natCast_nonneg H),
      abs_of_nonneg (Int.natCast_nonneg G)] using near

/-- For a Gauss-reduced basis, put U = b₁·b₁, V = b₂·b₂ and T = 2 b₁·b₂.
Every vector shorter in squared length than 3U has both integer basis
coefficients at most one in absolute value. Up to sign, there are four
nonzero possibilities: b₁, b₂, b₁+b₂ and b₁-b₂. -/
theorem gauss_four_vectors {U V T i j : ℤ} (positive : 0 < U) (ordered : U ≤ V)
    (reduced : |T| ≤ U) (short : U*i^2 + T*i*j + V*j^2 < 3*U) :
    |i| ≤ 1 ∧ |j| ≤ 1 := by
  have bound : |T*i*j| ≤ U*(|i| * |j|) := by
    simp only [abs_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right reduced (abs_nonneg i)) (abs_nonneg j)
  have cross : -(U*(|i| * |j|)) ≤ T*i*j := (neg_le_neg bound).trans (neg_abs_le _)
  have lower : U*(|i|^2-|i| * |j|+|j|^2) ≤ U*i^2 + T*i*j + V*j^2 := by
    rw [sq_abs, sq_abs]
    nlinarith [mul_nonneg (sub_nonneg.mpr ordered) (sq_nonneg j)]
  have small := (mul_lt_mul_left positive).mp
    (show U*(|i|^2-|i| * |j|+|j|^2) < U*3 by linarith [lower.trans_lt short])
  have bound_one (a b : ℤ) (h : a^2-a*b+b^2 < 3) : a ≤ 1 := by
    by_contra! big
    have two : (2 : ℤ) ≤ a := by omega
    have square := mul_self_le_mul_self (by decide : (0:ℤ) ≤ 2) two
    nlinarith [sq_nonneg (a-2*b)]
  exact ⟨bound_one _ _ small, bound_one |j| |i| (by linarith only [small])⟩

/-- A square of radius r either already contains the first reduced basis
vector (when its squared length is below r²), or every lattice vector in
the open square is one of the four directions in `gauss_four_vectors`. -/
theorem gauss_four_vectors_of_square {U V T i j x y r : ℤ}
    (positive : 0 < U) (ordered : U ≤ V) (reduced : |T| ≤ U)
    (first : r^2 ≤ U) (hx : |x| < r) (hy : |y| < r)
    (norm : x^2+y^2 = U*i^2 + T*i*j + V*j^2) : |i| ≤ 1 ∧ |j| ≤ 1 := by
  have square (a : ℤ) (h : |a| < r) : a^2 < r^2 := by
    have sum : 0 < r+|a| := by linarith [abs_nonneg a]
    have product := mul_pos (sub_pos.mpr h) sum
    nlinarith [sq_abs a]
  apply gauss_four_vectors positive ordered reduced
  linarith [square x hx, square y hy]

end PrimeFactors
