import PrimeFactors.HankelTranslation

/-! Finite obstructions to a constant-coefficient Somos-4 relation among the Hankel
determinants of the translated cubic Hasse readings. -/
namespace PrimeFactors.HasseHankelBilinear

open Polynomial Finset Matrix HankelTranslation

variable {R : Type*} [CommRing R]

private noncomputable def pc (B Cc : R) (k j : ℕ) : R :=
  ((1 + C B * X^2 + C Cc * X^3 : R[X])^k).coeff j

private theorem pc_succ (B Cc : R) (k j : ℕ) :
    pc B Cc (k+1) j = pc B Cc k j +
      (if 2≤j then pc B Cc k (j-2)*B else 0) +
      (if 3≤j then pc B Cc k (j-3)*Cc else 0) := by
  unfold pc
  rw [pow_succ]
  simp only [mul_add, mul_one, ←mul_assoc, coeff_add, coeff_mul_X_pow',
    coeff_mul_C]

private theorem pc_zero (B Cc : R) (j : ℕ) :
    pc B Cc 0 j = if j=0 then 1 else 0 := by
  simp [pc, coeff_one]

private noncomputable def minor (s : ℕ→R) (k : ℕ) (cols : List ℕ) : R :=
  (Matrix.of fun i j : Fin k => s (i.val + (cols[j.val]?).getD 0)).det

private theorem minor_zero (s : ℕ→R) : minor s 0 [] = 1 := Matrix.det_isEmpty

private theorem minor_succ (s : ℕ→R) (k : ℕ) (cols : List ℕ) :
    minor s (k+1) cols = ∑ j ∈ range (k+1),
      (-1)^(k+j) * s (k+(cols[j]?).getD 0) * minor s k (cols.eraseIdx j) := by
  unfold minor
  rw [Matrix.det_succ_row _ (Fin.last k), ←Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  congr 2
  ext i l
  simp only [Matrix.submatrix_apply, Matrix.of_apply, List.getElem?_eraseIdx]
  have last : i.castSucc < Fin.last k := Fin.castSucc_lt_last i
  by_cases h : l.val < j.val
  · have lt : l.castSucc < j := h
    simp [Fin.succAbove, lt, h, last]
  · have lt : ¬l.castSucc < j := h
    simp [Fin.succAbove, lt, h, last]

private theorem top_minor (s : ℕ→R) (n : ℕ) :
    hankel s n = minor s n (List.range n) := by
  unfold hankel minor
  congr 1
  ext i j
  have hj : j.val < (List.range n).length := by simp
  simp [List.getElem?_eq_getElem hj]


set_option exponentiation.threshold 512
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem m0 (B Cc : R) : moment B Cc 0 = 1 := by
  change pc B Cc 0 0 = _
  norm_num [pc_succ, pc_zero]

private theorem m1 (B Cc : R) : moment B Cc 1 = 0 := by
  change pc B Cc 1 1 = _
  norm_num [pc_succ, pc_zero]

private theorem m2 (B Cc : R) : moment B Cc 2 = 2*B := by
  change pc B Cc 2 2 = _
  norm_num [pc_succ, pc_zero]
  ring

private theorem m3 (B Cc : R) : moment B Cc 3 = 3*Cc := by
  change pc B Cc 3 3 = _
  norm_num [pc_succ, pc_zero]
  ring

private theorem m4 (B Cc : R) : moment B Cc 4 = 6*B^2 := by
  change pc B Cc 4 4 = _
  norm_num [pc_succ, pc_zero]
  ring

private theorem m5 (B Cc : R) : moment B Cc 5 = 20*B*Cc := by
  change pc B Cc 5 5 = _
  norm_num [pc_succ, pc_zero]
  ring

private theorem m6 (B Cc : R) : moment B Cc 6 = 20*B^3+15*Cc^2 := by
  change pc B Cc 6 6 = _
  norm_num [pc_succ, pc_zero]
  ring

private theorem m7 (B Cc : R) : moment B Cc 7 = 105*B^2*Cc := by
  change pc B Cc 7 7 = _
  norm_num [pc_succ, pc_zero]
  ring

private theorem m8 (B Cc : R) : moment B Cc 8 = 70*B^4+168*B*Cc^2 := by
  change pc B Cc 8 8 = _
  norm_num [pc_succ, pc_zero]
  ring

private theorem m9 (B Cc : R) : moment B Cc 9 = 504*B^3*Cc+84*Cc^3 := by
  change pc B Cc 9 9 = _
  norm_num [pc_succ, pc_zero]
  ring

private theorem m10 (B Cc : R) : moment B Cc 10 = 252*B^5+1260*B^2*Cc^2 := by
  change pc B Cc 10 10 = _
  norm_num [pc_succ, pc_zero]
  ring

private theorem m11 (B Cc : R) : moment B Cc 11 = 2310*B^4*Cc+1320*B*Cc^3 := by
  change pc B Cc 11 11 = _
  norm_num [pc_succ, pc_zero]
  ring

private theorem m12 (B Cc : R) : moment B Cc 12 = 924*B^6+7920*B^3*Cc^2+495*Cc^4 := by
  change pc B Cc 12 12 = _
  norm_num [pc_succ, pc_zero]
  ring

-- A Laplace certificate for a column subset only needs the already-checked
-- subsets one column shorter. This gives 128 subminors through order seven.
private theorem expand1 (s : ℕ→R) (v0 : ℕ) :
    minor s 1 [v0] =
    0 + (-1)^0 * s (0+v0) * minor s 0 [] := by
  rw [minor_succ]
  simp only [sum_range_succ, sum_range_zero, List.eraseIdx, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, Nat.reduceAdd]

private theorem expand2 (s : ℕ→R) (v0 v1 : ℕ) :
    minor s 2 [v0, v1] =
    0 + (-1)^1 * s (1+v0) * minor s 1 [v1]
      + (-1)^2 * s (1+v1) * minor s 1 [v0] := by
  rw [minor_succ]
  simp only [sum_range_succ, sum_range_zero, List.eraseIdx, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, Nat.reduceAdd]

private theorem expand3 (s : ℕ→R) (v0 v1 v2 : ℕ) :
    minor s 3 [v0, v1, v2] =
    0 + (-1)^2 * s (2+v0) * minor s 2 [v1, v2]
      + (-1)^3 * s (2+v1) * minor s 2 [v0, v2]
      + (-1)^4 * s (2+v2) * minor s 2 [v0, v1] := by
  rw [minor_succ]
  simp only [sum_range_succ, sum_range_zero, List.eraseIdx, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, Nat.reduceAdd]

private theorem expand4 (s : ℕ→R) (v0 v1 v2 v3 : ℕ) :
    minor s 4 [v0, v1, v2, v3] =
    0 + (-1)^3 * s (3+v0) * minor s 3 [v1, v2, v3]
      + (-1)^4 * s (3+v1) * minor s 3 [v0, v2, v3]
      + (-1)^5 * s (3+v2) * minor s 3 [v0, v1, v3]
      + (-1)^6 * s (3+v3) * minor s 3 [v0, v1, v2] := by
  rw [minor_succ]
  simp only [sum_range_succ, sum_range_zero, List.eraseIdx, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, Nat.reduceAdd]

private theorem expand5 (s : ℕ→R) (v0 v1 v2 v3 v4 : ℕ) :
    minor s 5 [v0, v1, v2, v3, v4] =
    0 + (-1)^4 * s (4+v0) * minor s 4 [v1, v2, v3, v4]
      + (-1)^5 * s (4+v1) * minor s 4 [v0, v2, v3, v4]
      + (-1)^6 * s (4+v2) * minor s 4 [v0, v1, v3, v4]
      + (-1)^7 * s (4+v3) * minor s 4 [v0, v1, v2, v4]
      + (-1)^8 * s (4+v4) * minor s 4 [v0, v1, v2, v3] := by
  rw [minor_succ]
  simp only [sum_range_succ, sum_range_zero, List.eraseIdx, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, Nat.reduceAdd]

private theorem expand6 (s : ℕ→R) (v0 v1 v2 v3 v4 v5 : ℕ) :
    minor s 6 [v0, v1, v2, v3, v4, v5] =
    0 + (-1)^5 * s (5+v0) * minor s 5 [v1, v2, v3, v4, v5]
      + (-1)^6 * s (5+v1) * minor s 5 [v0, v2, v3, v4, v5]
      + (-1)^7 * s (5+v2) * minor s 5 [v0, v1, v3, v4, v5]
      + (-1)^8 * s (5+v3) * minor s 5 [v0, v1, v2, v4, v5]
      + (-1)^9 * s (5+v4) * minor s 5 [v0, v1, v2, v3, v5]
      + (-1)^10 * s (5+v5) * minor s 5 [v0, v1, v2, v3, v4] := by
  rw [minor_succ]
  simp only [sum_range_succ, sum_range_zero, List.eraseIdx, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, Nat.reduceAdd]

private theorem expand7 (s : ℕ→R) (v0 v1 v2 v3 v4 v5 v6 : ℕ) :
    minor s 7 [v0, v1, v2, v3, v4, v5, v6] =
    0 + (-1)^6 * s (6+v0) * minor s 6 [v1, v2, v3, v4, v5, v6]
      + (-1)^7 * s (6+v1) * minor s 6 [v0, v2, v3, v4, v5, v6]
      + (-1)^8 * s (6+v2) * minor s 6 [v0, v1, v3, v4, v5, v6]
      + (-1)^9 * s (6+v3) * minor s 6 [v0, v1, v2, v4, v5, v6]
      + (-1)^10 * s (6+v4) * minor s 6 [v0, v1, v2, v3, v5, v6]
      + (-1)^11 * s (6+v5) * minor s 6 [v0, v1, v2, v3, v4, v6]
      + (-1)^12 * s (6+v6) * minor s 6 [v0, v1, v2, v3, v4, v5] := by
  rw [minor_succ]
  simp only [sum_range_succ, sum_range_zero, List.eraseIdx, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, Nat.reduceAdd]

private theorem c0 (B Cc : R) : minor (moment B Cc) 0 [] = 1 := by
  exact minor_zero ..

private theorem c1 (B Cc : R) : minor (moment B Cc) 1 [0] = 1 := by
  simp only [expand1, Nat.reduceAdd, c0, m0]
  ring

private theorem c2 (B Cc : R) : minor (moment B Cc) 1 [1] = 0 := by
  simp only [expand1, Nat.reduceAdd, c0, m1]
  ring

private theorem c4 (B Cc : R) : minor (moment B Cc) 1 [2] = 2*B := by
  simp only [expand1, Nat.reduceAdd, c0, m2]
  ring

private theorem c8 (B Cc : R) : minor (moment B Cc) 1 [3] = 3*Cc := by
  simp only [expand1, Nat.reduceAdd, c0, m3]
  ring

private theorem c16 (B Cc : R) : minor (moment B Cc) 1 [4] = 6*B^2 := by
  simp only [expand1, Nat.reduceAdd, c0, m4]
  ring

private theorem c32 (B Cc : R) : minor (moment B Cc) 1 [5] = 20*B*Cc := by
  simp only [expand1, Nat.reduceAdd, c0, m5]
  ring

private theorem c64 (B Cc : R) : minor (moment B Cc) 1 [6] = 20*B^3+15*Cc^2 := by
  simp only [expand1, Nat.reduceAdd, c0, m6]
  ring

private theorem c3 (B Cc : R) : minor (moment B Cc) 2 [0, 1] = 2*B := by
  simp only [expand2, Nat.reduceAdd, c2, c1, m1, m2]
  ring

private theorem c5 (B Cc : R) : minor (moment B Cc) 2 [0, 2] = 3*Cc := by
  simp only [expand2, Nat.reduceAdd, c4, c1, m1, m3]
  ring

private theorem c9 (B Cc : R) : minor (moment B Cc) 2 [0, 3] = 6*B^2 := by
  simp only [expand2, Nat.reduceAdd, c8, c1, m1, m4]
  ring

private theorem c17 (B Cc : R) : minor (moment B Cc) 2 [0, 4] = 20*B*Cc := by
  simp only [expand2, Nat.reduceAdd, c16, c1, m1, m5]
  ring

private theorem c33 (B Cc : R) : minor (moment B Cc) 2 [0, 5] = 20*B^3+15*Cc^2 := by
  simp only [expand2, Nat.reduceAdd, c32, c1, m1, m6]
  ring

private theorem c65 (B Cc : R) : minor (moment B Cc) 2 [0, 6] = 105*B^2*Cc := by
  simp only [expand2, Nat.reduceAdd, c64, c1, m1, m7]
  ring

private theorem c6 (B Cc : R) : minor (moment B Cc) 2 [1, 2] = -4*B^2 := by
  simp only [expand2, Nat.reduceAdd, c4, c2, m2, m3]
  ring

private theorem c10 (B Cc : R) : minor (moment B Cc) 2 [1, 3] = -6*B*Cc := by
  simp only [expand2, Nat.reduceAdd, c8, c2, m2, m4]
  ring

private theorem c18 (B Cc : R) : minor (moment B Cc) 2 [1, 4] = -12*B^3 := by
  simp only [expand2, Nat.reduceAdd, c16, c2, m2, m5]
  ring

private theorem c34 (B Cc : R) : minor (moment B Cc) 2 [1, 5] = -40*B^2*Cc := by
  simp only [expand2, Nat.reduceAdd, c32, c2, m2, m6]
  ring

private theorem c66 (B Cc : R) : minor (moment B Cc) 2 [1, 6] = -40*B^4-30*B*Cc^2 := by
  simp only [expand2, Nat.reduceAdd, c64, c2, m2, m7]
  ring

private theorem c12 (B Cc : R) : minor (moment B Cc) 2 [2, 3] = 12*B^3-9*Cc^2 := by
  simp only [expand2, Nat.reduceAdd, c8, c4, m3, m4]
  ring

private theorem c20 (B Cc : R) : minor (moment B Cc) 2 [2, 4] = 22*B^2*Cc := by
  simp only [expand2, Nat.reduceAdd, c16, c4, m3, m5]
  ring

private theorem c36 (B Cc : R) : minor (moment B Cc) 2 [2, 5] = 40*B^4-30*B*Cc^2 := by
  simp only [expand2, Nat.reduceAdd, c32, c4, m3, m6]
  ring

private theorem c68 (B Cc : R) : minor (moment B Cc) 2 [2, 6] = 150*B^3*Cc-45*Cc^3 := by
  simp only [expand2, Nat.reduceAdd, c64, c4, m3, m7]
  ring

private theorem c24 (B Cc : R) : minor (moment B Cc) 2 [3, 4] = -36*B^4+60*B*Cc^2 := by
  simp only [expand2, Nat.reduceAdd, c16, c8, m4, m5]
  ring

private theorem c40 (B Cc : R) : minor (moment B Cc) 2 [3, 5] = -60*B^3*Cc+45*Cc^3 := by
  simp only [expand2, Nat.reduceAdd, c32, c8, m4, m6]
  ring

private theorem c72 (B Cc : R) : minor (moment B Cc) 2 [3, 6] = -120*B^5+225*B^2*Cc^2 := by
  simp only [expand2, Nat.reduceAdd, c64, c8, m4, m7]
  ring

private theorem c48 (B Cc : R) : minor (moment B Cc) 2 [4, 5] = 120*B^5-310*B^2*Cc^2 := by
  simp only [expand2, Nat.reduceAdd, c32, c16, m5, m6]
  ring

private theorem c80 (B Cc : R) : minor (moment B Cc) 2 [4, 6] = 230*B^4*Cc-300*B*Cc^3 := by
  simp only [expand2, Nat.reduceAdd, c64, c16, m5, m7]
  ring

private theorem c96 (B Cc : R) : minor (moment B Cc) 2 [5, 6] = -400*B^6+1500*B^3*Cc^2-225*Cc^4 := by
  simp only [expand2, Nat.reduceAdd, c64, c32, m6, m7]
  ring

private theorem c7 (B Cc : R) : minor (moment B Cc) 3 [0, 1, 2] = 4*B^3-9*Cc^2 := by
  simp only [expand3, Nat.reduceAdd, c6, c5, c3, m2, m3, m4]
  ring

private theorem c11 (B Cc : R) : minor (moment B Cc) 3 [0, 1, 3] = 10*B^2*Cc := by
  simp only [expand3, Nat.reduceAdd, c10, c9, c3, m2, m3, m5]
  ring

private theorem c19 (B Cc : R) : minor (moment B Cc) 3 [0, 1, 4] = 16*B^4-30*B*Cc^2 := by
  simp only [expand3, Nat.reduceAdd, c18, c17, c3, m2, m3, m6]
  ring

private theorem c35 (B Cc : R) : minor (moment B Cc) 3 [0, 1, 5] = 70*B^3*Cc-45*Cc^3 := by
  simp only [expand3, Nat.reduceAdd, c34, c33, c3, m2, m3, m7]
  ring

private theorem c67 (B Cc : R) : minor (moment B Cc) 3 [0, 1, 6] = 60*B^5-39*B^2*Cc^2 := by
  simp only [expand3, Nat.reduceAdd, c66, c65, c3, m2, m3, m8]
  ring

private theorem c13 (B Cc : R) : minor (moment B Cc) 3 [0, 2, 3] = -12*B^4+42*B*Cc^2 := by
  simp only [expand3, Nat.reduceAdd, c12, c9, c5, m2, m4, m5]
  ring

private theorem c21 (B Cc : R) : minor (moment B Cc) 3 [0, 2, 4] = -16*B^3*Cc+45*Cc^3 := by
  simp only [expand3, Nat.reduceAdd, c20, c17, c5, m2, m4, m6]
  ring

private theorem c37 (B Cc : R) : minor (moment B Cc) 3 [0, 2, 5] = -40*B^5+165*B^2*Cc^2 := by
  simp only [expand3, Nat.reduceAdd, c36, c33, c5, m2, m4, m7]
  ring

private theorem c69 (B Cc : R) : minor (moment B Cc) 3 [0, 2, 6] = -120*B^4*Cc+414*B*Cc^3 := by
  simp only [expand3, Nat.reduceAdd, c68, c65, c5, m2, m4, m8]
  ring

private theorem c25 (B Cc : R) : minor (moment B Cc) 3 [0, 3, 4] = 48*B^5-190*B^2*Cc^2 := by
  simp only [expand3, Nat.reduceAdd, c24, c17, c9, m2, m5, m6]
  ring

private theorem c41 (B Cc : R) : minor (moment B Cc) 3 [0, 3, 5] = 110*B^4*Cc-210*B*Cc^3 := by
  simp only [expand3, Nat.reduceAdd, c40, c33, c9, m2, m5, m7]
  ring

private theorem c73 (B Cc : R) : minor (moment B Cc) 3 [0, 3, 6] = 180*B^6-642*B^3*Cc^2 := by
  simp only [expand3, Nat.reduceAdd, c72, c65, c9, m2, m5, m8]
  ring

private theorem c49 (B Cc : R) : minor (moment B Cc) 3 [0, 4, 5] = -160*B^6+880*B^3*Cc^2-225*Cc^4 := by
  simp only [expand3, Nat.reduceAdd, c48, c33, c17, m2, m6, m7]
  ring

private theorem c81 (B Cc : R) : minor (moment B Cc) 3 [0, 4, 6] = -240*B^5*Cc+1185*B^2*Cc^3 := by
  simp only [expand3, Nat.reduceAdd, c80, c65, c17, m2, m6, m8]
  ring

private theorem c97 (B Cc : R) : minor (moment B Cc) 3 [0, 5, 6] = 600*B^7-3615*B^4*Cc^2+2070*B*Cc^4 := by
  simp only [expand3, Nat.reduceAdd, c96, c65, c33, m2, m7, m8]
  ring

private theorem c14 (B Cc : R) : minor (moment B Cc) 3 [1, 2, 3] = -8*B^3*Cc-27*Cc^3 := by
  simp only [expand3, Nat.reduceAdd, c12, c10, c6, m3, m4, m5]
  ring

private theorem c22 (B Cc : R) : minor (moment B Cc) 3 [1, 2, 4] = -8*B^5+6*B^2*Cc^2 := by
  simp only [expand3, Nat.reduceAdd, c20, c18, c6, m3, m4, m6]
  ring

private theorem c38 (B Cc : R) : minor (moment B Cc) 3 [1, 2, 5] = -60*B^4*Cc-90*B*Cc^3 := by
  simp only [expand3, Nat.reduceAdd, c36, c34, c6, m3, m4, m7]
  ring

private theorem c70 (B Cc : R) : minor (moment B Cc) 3 [1, 2, 6] = -40*B^6-42*B^3*Cc^2-135*Cc^4 := by
  simp only [expand3, Nat.reduceAdd, c68, c66, c6, m3, m4, m8]
  ring

private theorem c26 (B Cc : R) : minor (moment B Cc) 3 [1, 3, 4] = 12*B^4*Cc+90*B*Cc^3 := by
  simp only [expand3, Nat.reduceAdd, c24, c18, c10, m3, m5, m6]
  ring

private theorem c42 (B Cc : R) : minor (moment B Cc) 3 [1, 3, 5] = -10*B^3*Cc^2+135*Cc^4 := by
  simp only [expand3, Nat.reduceAdd, c40, c34, c10, m3, m5, m7]
  ring

private theorem c74 (B Cc : R) : minor (moment B Cc) 3 [1, 3, 6] = 20*B^5*Cc+267*B^2*Cc^3 := by
  simp only [expand3, Nat.reduceAdd, c72, c66, c10, m3, m5, m8]
  ring

private theorem c50 (B Cc : R) : minor (moment B Cc) 3 [1, 4, 5] = -100*B^5*Cc-330*B^2*Cc^3 := by
  simp only [expand3, Nat.reduceAdd, c48, c34, c18, m3, m6, m7]
  ring

private theorem c82 (B Cc : R) : minor (moment B Cc) 3 [1, 4, 6] = -40*B^7-126*B^4*Cc^2-450*B*Cc^4 := by
  simp only [expand3, Nat.reduceAdd, c80, c66, c18, m3, m6, m8]
  ring

private theorem c98 (B Cc : R) : minor (moment B Cc) 3 [1, 5, 6] = 200*B^6*Cc+930*B^3*Cc^3-675*Cc^5 := by
  simp only [expand3, Nat.reduceAdd, c96, c66, c34, m3, m7, m8]
  ring

private theorem c28 (B Cc : R) : minor (moment B Cc) 3 [2, 3, 4] = 24*B^6-80*B^3*Cc^2-135*Cc^4 := by
  simp only [expand3, Nat.reduceAdd, c24, c20, c12, m4, m5, m6]
  ring

private theorem c44 (B Cc : R) : minor (moment B Cc) 3 [2, 3, 5] = 100*B^5*Cc-75*B^2*Cc^3 := by
  simp only [expand3, Nat.reduceAdd, c40, c36, c12, m4, m5, m7]
  ring

private theorem c76 (B Cc : R) : minor (moment B Cc) 3 [2, 3, 6] = 120*B^7-264*B^4*Cc^2-612*B*Cc^4 := by
  simp only [expand3, Nat.reduceAdd, c72, c68, c12, m4, m5, m8]
  ring

private theorem c52 (B Cc : R) : minor (moment B Cc) 3 [2, 4, 5] = -80*B^7+450*B^4*Cc^2+450*B*Cc^4 := by
  simp only [expand3, Nat.reduceAdd, c48, c36, c20, m4, m6, m7]
  ring

private theorem c84 (B Cc : R) : minor (moment B Cc) 3 [2, 4, 6] = -80*B^6*Cc+546*B^3*Cc^3+675*Cc^5 := by
  simp only [expand3, Nat.reduceAdd, c80, c68, c20, m4, m6, m8]
  ring

private theorem c100 (B Cc : R) : minor (moment B Cc) 3 [2, 5, 6] = 400*B^8-2130*B^5*Cc^2-1665*B^2*Cc^4 := by
  simp only [expand3, Nat.reduceAdd, c96, c68, c36, m4, m7, m8]
  ring

private theorem c56 (B Cc : R) : minor (moment B Cc) 3 [3, 4, 5] = -180*B^6*Cc+100*B^3*Cc^3-675*Cc^5 := by
  simp only [expand3, Nat.reduceAdd, c48, c40, c24, m5, m6, m7]
  ring

private theorem c88 (B Cc : R) : minor (moment B Cc) 3 [3, 4, 6] = -120*B^8+52*B^5*Cc^2+705*B^2*Cc^4 := by
  simp only [expand3, Nat.reduceAdd, c80, c72, c24, m5, m6, m8]
  ring

private theorem c104 (B Cc : R) : minor (moment B Cc) 3 [3, 5, 6] = 400*B^7*Cc-555*B^4*Cc^3+3060*B*Cc^5 := by
  simp only [expand3, Nat.reduceAdd, c96, c72, c40, m5, m7, m8]
  ring

private theorem c112 (B Cc : R) : minor (moment B Cc) 3 [4, 5, 6] = 400*B^9-1690*B^6*Cc^2-2580*B^3*Cc^4-3375*Cc^6 := by
  simp only [expand3, Nat.reduceAdd, c96, c80, c48, m6, m7, m8]
  ring

private theorem c15 (B Cc : R) : minor (moment B Cc) 4 [0, 1, 2, 3] = 8*B^6-44*B^3*Cc^2-54*Cc^4 := by
  simp only [expand4, Nat.reduceAdd, c14, c13, c11, c7, m3, m4, m5, m6]
  ring

private theorem c23 (B Cc : R) : minor (moment B Cc) 4 [0, 1, 2, 4] = 28*B^5*Cc-93*B^2*Cc^3 := by
  simp only [expand4, Nat.reduceAdd, c22, c21, c19, c7, m3, m4, m5, m7]
  ring

private theorem c39 (B Cc : R) : minor (moment B Cc) 4 [0, 1, 2, 5] = 40*B^7-188*B^4*Cc^2-342*B*Cc^4 := by
  simp only [expand4, Nat.reduceAdd, c38, c37, c35, c7, m3, m4, m5, m8]
  ring

private theorem c71 (B Cc : R) : minor (moment B Cc) 4 [0, 1, 2, 6] = 216*B^6*Cc-810*B^3*Cc^3-351*Cc^5 := by
  simp only [expand4, Nat.reduceAdd, c70, c69, c67, c7, m3, m4, m5, m9]
  ring

private theorem c27 (B Cc : R) : minor (moment B Cc) 4 [0, 1, 3, 4] = -32*B^7+234*B^4*Cc^2+180*B*Cc^4 := by
  simp only [expand4, Nat.reduceAdd, c26, c25, c19, c11, m3, m4, m6, m7]
  ring

private theorem c43 (B Cc : R) : minor (moment B Cc) 4 [0, 1, 3, 5] = -40*B^6*Cc+300*B^3*Cc^3+270*Cc^5 := by
  simp only [expand4, Nat.reduceAdd, c42, c41, c35, c11, m3, m4, m6, m8]
  ring

private theorem c75 (B Cc : R) : minor (moment B Cc) 4 [0, 1, 3, 6] = -120*B^8+1008*B^5*Cc^2+624*B^2*Cc^4 := by
  simp only [expand4, Nat.reduceAdd, c74, c73, c67, c11, m3, m4, m6, m9]
  ring

private theorem c51 (B Cc : R) : minor (moment B Cc) 4 [0, 1, 4, 5] = 160*B^8-1182*B^5*Cc^2-675*B^2*Cc^4 := by
  simp only [expand4, Nat.reduceAdd, c50, c49, c35, c19, m3, m4, m7, m8]
  ring

private theorem c83 (B Cc : R) : minor (moment B Cc) 4 [0, 1, 4, 6] = 444*B^7*Cc-2193*B^4*Cc^3-1170*B*Cc^5 := by
  simp only [expand4, Nat.reduceAdd, c82, c81, c67, c19, m3, m4, m7, m9]
  ring

private theorem c99 (B Cc : R) : minor (moment B Cc) 4 [0, 1, 5, 6] = -600*B^9+5640*B^6*Cc^2-618*B^3*Cc^4-1755*Cc^6 := by
  simp only [expand4, Nat.reduceAdd, c98, c97, c67, c35, m3, m4, m8, m9]
  ring

private theorem c29 (B Cc : R) : minor (moment B Cc) 4 [0, 2, 3, 4] = -52*B^6*Cc+190*B^3*Cc^3-270*Cc^5 := by
  simp only [expand4, Nat.reduceAdd, c28, c25, c21, c13, m3, m5, m6, m7]
  ring

private theorem c45 (B Cc : R) : minor (moment B Cc) 4 [0, 2, 3, 5] = -40*B^8+124*B^5*Cc^2+606*B^2*Cc^4 := by
  simp only [expand4, Nat.reduceAdd, c44, c41, c37, c13, m3, m5, m6, m8]
  ring

private theorem c77 (B Cc : R) : minor (moment B Cc) 4 [0, 2, 3, 6] = -408*B^7*Cc+1632*B^4*Cc^3-846*B*Cc^5 := by
  simp only [expand4, Nat.reduceAdd, c76, c73, c69, c13, m3, m5, m6, m9]
  ring

private theorem c53 (B Cc : R) : minor (moment B Cc) 4 [0, 2, 4, 5] = 120*B^7*Cc-613*B^4*Cc^3+1710*B*Cc^5 := by
  simp only [expand4, Nat.reduceAdd, c52, c49, c37, c21, m3, m5, m7, m8]
  ring

private theorem c85 (B Cc : R) : minor (moment B Cc) 4 [0, 2, 4, 6] = -24*B^6*Cc^2-72*B^3*Cc^4+1755*Cc^6 := by
  simp only [expand4, Nat.reduceAdd, c84, c81, c69, c21, m3, m5, m7, m9]
  ring

private theorem c101 (B Cc : R) : minor (moment B Cc) 4 [0, 2, 5, 6] = -960*B^8*Cc+5070*B^5*Cc^3-9297*B^2*Cc^5 := by
  simp only [expand4, Nat.reduceAdd, c100, c97, c69, c37, m3, m5, m8, m9]
  ring

private theorem c57 (B Cc : R) : minor (moment B Cc) 4 [0, 3, 4, 5] = 160*B^9-1046*B^6*Cc^2-1470*B^3*Cc^4-1350*Cc^6 := by
  simp only [expand4, Nat.reduceAdd, c56, c49, c41, c25, m3, m6, m7, m8]
  ring

private theorem c89 (B Cc : R) : minor (moment B Cc) 4 [0, 3, 4, 6] = 852*B^8*Cc-4374*B^5*Cc^3-300*B^2*Cc^5 := by
  simp only [expand4, Nat.reduceAdd, c88, c81, c73, c25, m3, m6, m7, m9]
  ring

private theorem c105 (B Cc : R) : minor (moment B Cc) 4 [0, 3, 5, 6] = -600*B^10+5640*B^7*Cc^2+96*B^4*Cc^4+4230*B*Cc^6 := by
  simp only [expand4, Nat.reduceAdd, c104, c97, c73, c41, m3, m6, m8, m9]
  ring

private theorem c113 (B Cc : R) : minor (moment B Cc) 4 [0, 4, 5, 6] = -2040*B^9*Cc+12945*B^6*Cc^3-13470*B^3*Cc^5-8775*Cc^7 := by
  simp only [expand4, Nat.reduceAdd, c112, c97, c81, c49, m3, m7, m8, m9]
  ring

private theorem c30 (B Cc : R) : minor (moment B Cc) 4 [1, 2, 3, 4] = 16*B^8-120*B^5*Cc^2-315*B^2*Cc^4 := by
  simp only [expand4, Nat.reduceAdd, c28, c26, c22, c14, m4, m5, m6, m7]
  ring

private theorem c46 (B Cc : R) : minor (moment B Cc) 4 [1, 2, 3, 5] = 40*B^7*Cc-284*B^4*Cc^3-486*B*Cc^5 := by
  simp only [expand4, Nat.reduceAdd, c44, c42, c38, c14, m4, m5, m6, m8]
  ring

private theorem c78 (B Cc : R) : minor (moment B Cc) 4 [1, 2, 3, 6] = 80*B^9-608*B^6*Cc^2-1938*B^3*Cc^4-243*Cc^6 := by
  simp only [expand4, Nat.reduceAdd, c76, c74, c70, c14, m4, m5, m6, m9]
  ring

private theorem c54 (B Cc : R) : minor (moment B Cc) 4 [1, 2, 4, 5] = -80*B^9+676*B^6*Cc^2+1158*B^3*Cc^4 := by
  simp only [expand4, Nat.reduceAdd, c52, c50, c38, c22, m4, m5, m7, m8]
  ring

private theorem c86 (B Cc : R) : minor (moment B Cc) 4 [1, 2, 4, 6] = -152*B^8*Cc+966*B^5*Cc^3+1629*B^2*Cc^5 := by
  simp only [expand4, Nat.reduceAdd, c84, c82, c70, c22, m4, m5, m7, m9]
  ring

private theorem c102 (B Cc : R) : minor (moment B Cc) 4 [1, 2, 5, 6] = 400*B^10-3800*B^7*Cc^2-5304*B^4*Cc^4+1620*B*Cc^6 := by
  simp only [expand4, Nat.reduceAdd, c100, c98, c70, c38, m4, m5, m8, m9]
  ring

private theorem c58 (B Cc : R) : minor (moment B Cc) 4 [1, 3, 4, 5] = -80*B^8*Cc+666*B^5*Cc^3+45*B^2*Cc^5 := by
  simp only [expand4, Nat.reduceAdd, c56, c50, c42, c26, m4, m6, m7, m8]
  ring

private theorem c90 (B Cc : R) : minor (moment B Cc) 4 [1, 3, 4, 6] = -80*B^10+516*B^7*Cc^2+3213*B^4*Cc^4+810*B*Cc^6 := by
  simp only [expand4, Nat.reduceAdd, c88, c82, c74, c26, m4, m6, m7, m9]
  ring

private theorem c106 (B Cc : R) : minor (moment B Cc) 4 [1, 3, 5, 6] = 200*B^9*Cc-2160*B^6*Cc^3+4434*B^3*Cc^5+1215*Cc^7 := by
  simp only [expand4, Nat.reduceAdd, c104, c98, c74, c42, m4, m6, m8, m9]
  ring

private theorem c114 (B Cc : R) : minor (moment B Cc) 4 [1, 4, 5, 6] = 400*B^11-3720*B^8*Cc^2-8922*B^5*Cc^4-2745*B^2*Cc^6 := by
  simp only [expand4, Nat.reduceAdd, c112, c98, c82, c50, m4, m7, m8, m9]
  ring

private theorem c60 (B Cc : R) : minor (moment B Cc) 4 [2, 3, 4, 5] = 80*B^10-668*B^7*Cc^2-1265*B^4*Cc^4-2430*B*Cc^6 := by
  simp only [expand4, Nat.reduceAdd, c56, c52, c44, c28, m5, m6, m7, m8]
  ring

private theorem c92 (B Cc : R) : minor (moment B Cc) 4 [2, 3, 4, 6] = 296*B^9*Cc-1904*B^6*Cc^3-2910*B^3*Cc^5-1215*Cc^7 := by
  simp only [expand4, Nat.reduceAdd, c88, c84, c76, c28, m5, m6, m7, m9]
  ring

private theorem c108 (B Cc : R) : minor (moment B Cc) 4 [2, 3, 5, 6] = -400*B^11+4120*B^8*Cc^2+3642*B^5*Cc^4+10341*B^2*Cc^6 := by
  simp only [expand4, Nat.reduceAdd, c104, c100, c76, c44, m5, m6, m8, m9]
  ring

private theorem c116 (B Cc : R) : minor (moment B Cc) 4 [2, 4, 5, 6] = -720*B^10*Cc+5450*B^7*Cc^3+2397*B^4*Cc^5-8100*B*Cc^7 := by
  simp only [expand4, Nat.reduceAdd, c112, c100, c84, c52, m5, m7, m8, m9]
  ring

private theorem c120 (B Cc : R) : minor (moment B Cc) 4 [3, 4, 5, 6] = 400*B^12-4400*B^9*Cc^2-4131*B^6*Cc^4-22740*B^3*Cc^6-6075*Cc^8 := by
  simp only [expand4, Nat.reduceAdd, c112, c104, c88, c56, m6, m7, m8, m9]
  ring

private theorem c31 (B Cc : R) : minor (moment B Cc) 5 [0, 1, 2, 3, 4] = 16*B^10-156*B^7*Cc^2+13*B^4*Cc^4-972*B*Cc^6 := by
  simp only [expand5, Nat.reduceAdd, c30, c29, c27, c23, c15, m4, m5, m6, m7, m8]
  ring

private theorem c47 (B Cc : R) : minor (moment B Cc) 5 [0, 1, 2, 3, 5] = 72*B^9*Cc-548*B^6*Cc^3-138*B^3*Cc^5-486*Cc^7 := by
  simp only [expand5, Nat.reduceAdd, c46, c45, c43, c39, c15, m4, m5, m6, m7, m9]
  ring

private theorem c79 (B Cc : R) : minor (moment B Cc) 5 [0, 1, 2, 3, 6] = 96*B^11-816*B^8*Cc^2-666*B^5*Cc^4-6363*B^2*Cc^6 := by
  simp only [expand5, Nat.reduceAdd, c78, c77, c75, c71, c15, m4, m5, m6, m7, m10]
  ring

private theorem c55 (B Cc : R) : minor (moment B Cc) 5 [0, 1, 2, 4, 5] = -80*B^11+968*B^8*Cc^2-1018*B^5*Cc^4+5319*B^2*Cc^6 := by
  simp only [expand5, Nat.reduceAdd, c54, c53, c51, c39, c23, m4, m5, m6, m8, m9]
  ring

private theorem c87 (B Cc : R) : minor (moment B Cc) 5 [0, 1, 2, 4, 6] = -96*B^10*Cc+1332*B^7*Cc^3-1611*B^4*Cc^5+6318*B*Cc^7 := by
  simp only [expand5, Nat.reduceAdd, c86, c85, c83, c71, c23, m4, m5, m6, m8, m10]
  ring

private theorem c103 (B Cc : R) : minor (moment B Cc) 5 [0, 1, 2, 5, 6] = 480*B^12-5640*B^9*Cc^2+6048*B^6*Cc^4-34686*B^3*Cc^6+3159*Cc^8 := by
  simp only [expand5, Nat.reduceAdd, c102, c101, c99, c71, c39, m4, m5, m6, m9, m10]
  ring

private theorem c59 (B Cc : R) : minor (moment B Cc) 5 [0, 1, 3, 4, 5] = -208*B^10*Cc+1774*B^7*Cc^3-129*B^4*Cc^5-3240*B*Cc^7 := by
  simp only [expand5, Nat.reduceAdd, c58, c57, c51, c43, c27, m4, m5, m7, m8, m9]
  ring

private theorem c91 (B Cc : R) : minor (moment B Cc) 5 [0, 1, 3, 4, 6] = -144*B^12+924*B^9*Cc^2+3669*B^6*Cc^4+9978*B^3*Cc^6 := by
  simp only [expand5, Nat.reduceAdd, c90, c89, c83, c75, c27, m4, m5, m7, m8, m10]
  ring

private theorem c107 (B Cc : R) : minor (moment B Cc) 5 [0, 1, 3, 5, 6] = 600*B^11*Cc-6312*B^8*Cc^3+6666*B^5*Cc^5+26199*B^2*Cc^7 := by
  simp only [expand5, Nat.reduceAdd, c106, c105, c99, c75, c43, m4, m5, m7, m9, m10]
  ring

private theorem c115 (B Cc : R) : minor (moment B Cc) 5 [0, 1, 4, 5, 6] = 720*B^13-7560*B^10*Cc^2+384*B^7*Cc^4-50352*B^4*Cc^6-21060*B*Cc^8 := by
  simp only [expand5, Nat.reduceAdd, c114, c113, c99, c83, c51, m4, m5, m8, m9, m10]
  ring

private theorem c61 (B Cc : R) : minor (moment B Cc) 5 [0, 2, 3, 4, 5] = 80*B^12-1056*B^9*Cc^2+1275*B^6*Cc^4-7908*B^3*Cc^6-2430*Cc^8 := by
  simp only [expand5, Nat.reduceAdd, c60, c57, c53, c45, c29, m4, m6, m7, m8, m9]
  ring

private theorem c93 (B Cc : R) : minor (moment B Cc) 5 [0, 2, 3, 4, 6] = 192*B^11*Cc-2580*B^8*Cc^3+2994*B^5*Cc^5-16587*B^2*Cc^7 := by
  simp only [expand5, Nat.reduceAdd, c92, c89, c85, c77, c29, m4, m6, m7, m8, m10]
  ring

private theorem c109 (B Cc : R) : minor (moment B Cc) 5 [0, 2, 3, 5, 6] = -480*B^13+6600*B^10*Cc^2-11622*B^7*Cc^4+52677*B^4*Cc^6+7614*B*Cc^8 := by
  simp only [expand5, Nat.reduceAdd, c108, c105, c101, c77, c45, m4, m6, m7, m9, m10]
  ring

private theorem c117 (B Cc : R) : minor (moment B Cc) 5 [0, 2, 4, 5, 6] = -480*B^12*Cc+6840*B^9*Cc^3-12579*B^6*Cc^5+43182*B^3*Cc^7-15795*Cc^9 := by
  simp only [expand5, Nat.reduceAdd, c116, c113, c101, c85, c53, m4, m6, m8, m9, m10]
  ring

private theorem c121 (B Cc : R) : minor (moment B Cc) 5 [0, 3, 4, 5, 6] = 720*B^14-9600*B^11*Cc^2+14757*B^8*Cc^4-83646*B^5*Cc^6-80235*B^2*Cc^8 := by
  simp only [expand5, Nat.reduceAdd, c120, c113, c105, c89, c57, m4, m7, m8, m9, m10]
  ring

private theorem c62 (B Cc : R) : minor (moment B Cc) 5 [1, 2, 3, 4, 5] = 64*B^11*Cc-476*B^8*Cc^3-1708*B^5*Cc^5+5913*B^2*Cc^7 := by
  simp only [expand5, Nat.reduceAdd, c60, c58, c54, c46, c30, m5, m6, m7, m8, m9]
  ring

private theorem c94 (B Cc : R) : minor (moment B Cc) 5 [1, 2, 3, 4, 6] = 32*B^13-120*B^10*Cc^2-1426*B^7*Cc^4-5856*B^4*Cc^6+4374*B*Cc^8 := by
  simp only [expand5, Nat.reduceAdd, c92, c90, c86, c78, c30, m5, m6, m7, m8, m10]
  ring

private theorem c110 (B Cc : R) : minor (moment B Cc) 5 [1, 2, 3, 5, 6] = -240*B^12*Cc+2144*B^9*Cc^3+7152*B^6*Cc^5-40986*B^3*Cc^7+2187*Cc^9 := by
  simp only [expand5, Nat.reduceAdd, c108, c106, c102, c78, c46, m5, m6, m7, m9, m10]
  ring

private theorem c118 (B Cc : R) : minor (moment B Cc) 5 [1, 2, 4, 5, 6] = -160*B^14+1360*B^11*Cc^2+3040*B^8*Cc^4+15918*B^5*Cc^6+14499*B^2*Cc^8 := by
  simp only [expand5, Nat.reduceAdd, c116, c114, c102, c86, c54, m5, m6, m8, m9, m10]
  ring

private theorem c122 (B Cc : R) : minor (moment B Cc) 5 [1, 3, 4, 5, 6] = 160*B^13*Cc-1312*B^10*Cc^3-10506*B^7*Cc^5+41955*B^4*Cc^7+14580*B*Cc^9 := by
  simp only [expand5, Nat.reduceAdd, c120, c114, c106, c90, c58, m5, m7, m8, m9, m10]
  ring

private theorem c124 (B Cc : R) : minor (moment B Cc) 5 [2, 3, 4, 5, 6] = 160*B^15-1920*B^12*Cc^2+522*B^9*Cc^4-12408*B^6*Cc^6-79812*B^3*Cc^8+10935*Cc^10 := by
  simp only [expand5, Nat.reduceAdd, c120, c116, c108, c92, c60, m6, m7, m8, m9, m10]
  ring

private theorem c63 (B Cc : R) : minor (moment B Cc) 6 [0, 1, 2, 3, 4, 5] = 32*B^15-480*B^12*Cc^2+1134*B^9*Cc^4-3004*B^6*Cc^6-19872*B^3*Cc^8+4374*Cc^10 := by
  simp only [expand6, Nat.reduceAdd, c62, c61, c59, c55, c47, c31, m5, m6, m7, m8, m9, m10]
  ring

private theorem c95 (B Cc : R) : minor (moment B Cc) 6 [0, 1, 2, 3, 4, 6] = 176*B^14*Cc-2268*B^11*Cc^3+3779*B^8*Cc^5-11052*B^5*Cc^7-23409*B^2*Cc^9 := by
  simp only [expand6, Nat.reduceAdd, c94, c93, c91, c87, c79, c31, m5, m6, m7, m8, m9, m11]
  ring

private theorem c111 (B Cc : R) : minor (moment B Cc) 6 [0, 1, 2, 3, 5, 6] = -192*B^16+3432*B^13*Cc^2-12568*B^10*Cc^4+24780*B^7*Cc^6+117702*B^4*Cc^8-40338*B*Cc^10 := by
  simp only [expand6, Nat.reduceAdd, c110, c109, c107, c103, c79, c47, m5, m6, m7, m8, m10, m11]
  ring

private theorem c119 (B Cc : R) : minor (moment B Cc) 6 [0, 1, 2, 4, 5, 6] = -688*B^15*Cc+9736*B^12*Cc^3-21836*B^9*Cc^5+50697*B^6*Cc^7-7938*B^3*Cc^9+28431*Cc^11 := by
  simp only [expand6, Nat.reduceAdd, c118, c117, c115, c103, c87, c55, m5, m6, m7, m9, m10, m11]
  ring

private theorem c123 (B Cc : R) : minor (moment B Cc) 6 [0, 1, 3, 4, 5, 6] = 288*B^17-5648*B^14*Cc^2+24284*B^11*Cc^4-45567*B^8*Cc^6-227874*B^5*Cc^8-33129*B^2*Cc^10 := by
  simp only [expand6, Nat.reduceAdd, c122, c121, c115, c107, c91, c59, m5, m6, m8, m9, m10, m11]
  ring

private theorem c125 (B Cc : R) : minor (moment B Cc) 6 [0, 2, 3, 4, 5, 6] = 496*B^16*Cc-7200*B^13*Cc^3+15009*B^10*Cc^5-48174*B^7*Cc^7+132723*B^4*Cc^9-133164*B*Cc^11 := by
  simp only [expand6, Nat.reduceAdd, c124, c121, c117, c109, c93, c61, m5, m7, m8, m9, m10, m11]
  ring

private theorem c126 (B Cc : R) : minor (moment B Cc) 6 [1, 2, 3, 4, 5, 6] = -64*B^18+1280*B^15*Cc^2-4792*B^12*Cc^4-4404*B^9*Cc^6+123087*B^6*Cc^8+26892*B^3*Cc^10+19683*Cc^12 := by
  simp only [expand6, Nat.reduceAdd, c124, c122, c118, c110, c94, c62, m6, m7, m8, m9, m10, m11]
  ring

private theorem c127 (B Cc : R) : minor (moment B Cc) 7 [0, 1, 2, 3, 4, 5, 6] = 64*B^21-1360*B^18*Cc^2+7224*B^15*Cc^4-17229*B^12*Cc^6-36084*B^9*Cc^8-440298*B^6*Cc^10+430596*B^3*Cc^12+72171*Cc^14 := by
  simp only [expand7, Nat.reduceAdd, c126, c125, c123, c119, c111, c95, c63, m6, m7, m8, m9, m10, m11, m12]
  ring

private theorem d0 (B Cc : R) : hankel (moment B Cc) 0 = 1 := (top_minor ..).trans (c0 B Cc)

private theorem d1 (B Cc : R) : hankel (moment B Cc) 1 = 1 := (top_minor ..).trans (c1 B Cc)

private theorem d2 (B Cc : R) : hankel (moment B Cc) 2 = 2*B := (top_minor ..).trans (c3 B Cc)

private theorem d3 (B Cc : R) : hankel (moment B Cc) 3 = 4*B^3-9*Cc^2 := (top_minor ..).trans (c7 B Cc)

private theorem d4 (B Cc : R) : hankel (moment B Cc) 4 = 8*B^6-44*B^3*Cc^2-54*Cc^4 := (top_minor ..).trans (c15 B Cc)

private theorem d5 (B Cc : R) : hankel (moment B Cc) 5 = 16*B^10-156*B^7*Cc^2+13*B^4*Cc^4-972*B*Cc^6 := (top_minor ..).trans (c31 B Cc)

private theorem d6 (B Cc : R) : hankel (moment B Cc) 6 = 32*B^15-480*B^12*Cc^2+1134*B^9*Cc^4-3004*B^6*Cc^6-19872*B^3*Cc^8+4374*Cc^10 := (top_minor ..).trans (c63 B Cc)

private theorem d7 (B Cc : R) : hankel (moment B Cc) 7 = 64*B^21-1360*B^18*Cc^2+7224*B^15*Cc^4-17229*B^12*Cc^6-36084*B^9*Cc^8-440298*B^6*Cc^10+430596*B^3*Cc^12+72171*Cc^14 := (top_minor ..).trans (c127 B Cc)


/-- The first four equations of constant-coefficient Somos-4, beginning with the empty determinant. -/
def FirstFour (D : ℕ → R) (a b : R) : Prop :=
  ∀ n < 4, D n * D (n+4) = a * (D (n+1) * D (n+3)) + b * D (n+2)^2

private def triple (x y z r s t u v w : R) : R :=
  x*(s*w-t*v) - y*(r*w-t*u) + z*(r*v-s*u)

private theorem dependent (a b x y r s u v : R) :
    triple x y (a*x+b*y) r s (a*r+b*s) u v (a*u+b*v) = 0 := by
  unfold triple
  ring

def homZero (x y : R) : R :=
  (-26368) * y^6
    + (795712) * x^1 * y^5
    + (-5672064) * x^2 * y^4
    + (9444924) * x^3 * y^3
    + (4411422) * x^4 * y^2
    + (6213267) * x^5 * y^1
    + (11691702) * x^6

def pZero (z : R) : R := homZero z 1

def homOne (x y : R) : R :=
  (7110656) * y^10
    + (-331866112) * x^1 * y^9
    + (4804732928) * x^2 * y^8
    + (-20123449856) * x^3 * y^7
    + (-42695682816) * x^4 * y^6
    + (277267821408) * x^5 * y^5
    + (-790326605952) * x^6 * y^4
    + (963638542530) * x^7 * y^3
    + (-1652488154568) * x^8 * y^2
    + (-642558404367) * x^9 * y^1
    + (-172014697116) * x^10

def pOne (z : R) : R := homOne z 1

/-- Positive common Bézout denominator for the two integer obstruction polynomials. -/
def bezoutDenominator : ℕ := 1335108314285289836173182834372969487124180419608775943244321496282286256128000000000

private theorem bezout (z : R) : (bezoutDenominator:R) =
    (-4139914264668728566317468163916531186297953748575194115514387430879771101435035648
    + (104671018841391281048581675666223691119797252377552398398871433858109906963528562688)*z^1
    + (-594027002654251193197623175836204578413446848919719008328292827420033634436900491776)*z^2
    + (-861351594983927148158699438608283918595422113713067366803871521923804396601411358848)*z^3
    + (6666322495863474124906204710726484628011088854481172915043834621068106057702592322720)*z^4
    + (-20590335815584436918340882175902169569429684781157502910448694098946282556788067915344)*z^5
    + (24357197662253615966949701228875468470095680752942686086421388011059524564140652223242)*z^6
    + (-46257556120986154177311365335909136810943901103903093949603296327927218916216932661808)*z^7
    + (-17884404161329580677111094573987048840741918587050162080544815635906330861063155233499)*z^8
    + (-4729137942415744522782258496909216370895601355013209266215001699860499869824595493068)*z^9) * pZero z + (-15164022984166263281543336889279712706279176495505047986379744186915457328622144
    + (143688505553354470647498385333491651747526955846622414220622058007673603269186272)*z^1
    + (-265618556708097982463623169795481582353367453921204695059640778674575973623302300)*z^2
    + (-129799408776040833681837489214476131545980164790612179500518151818375866528238558)*z^3
    + (-185689273352444746500407315756048408677764807058381044521261754852134940630825567)*z^4
    + (-321435740472405675741203199903615838553687112452855954277518374537905180291838446)*z^5) * pOne z := by
  unfold bezoutDenominator pZero pOne homZero homOne
  push_cast
  ring

/-- The three-by-three consistency minor for three consecutive rows. -/
def rawMinor (D : ℕ → R) (n : ℕ) : R :=
  triple (D (n+1)*D (n+3)) (D (n+2)^2) (D n*D (n+4))
    (D (n+2)*D (n+4)) (D (n+3)^2) (D (n+1)*D (n+5))
    (D (n+3)*D (n+5)) (D (n+4)^2) (D (n+2)*D (n+6))

theorem raw_zero (B Cc : R) :
    rawMinor (hankel (moment B Cc)) 0 = 2*B*Cc^4*homZero (Cc^2) (B^3) := by
  unfold rawMinor triple homZero
  norm_num only [Nat.reduceAdd, d0, d1, d2, d3, d4, d5, d6]
  ring

theorem raw_one (B Cc : R) :
    rawMinor (hankel (moment B Cc)) 1 = B*Cc^8*homOne (Cc^2) (B^3) := by
  unfold rawMinor triple homOne
  norm_num only [Nat.reduceAdd, d1, d2, d3, d4, d5, d6, d7]
  ring

private theorem n0 (B Cc _z : R) :
    hankel (moment B Cc) 0 = B^0 * 1 := by
  rw [d0]
  ring

private theorem n1 (B Cc _z : R) :
    hankel (moment B Cc) 1 = B^0 * 1 := by
  rw [d1]
  ring

private theorem n2 (B Cc _z : R) :
    hankel (moment B Cc) 2 = B^1 * 2 := by
  rw [d2]
  ring

private theorem n3 (B Cc z : R) (hz : Cc^2=B^3*z) :
    hankel (moment B Cc) 3 = B^3 * (4 + z*-9) := by
  rw [d3]
  rw [hz]
  ring

private theorem n4 (B Cc z : R) (hz : Cc^2=B^3*z) :
    hankel (moment B Cc) 4 = B^6 * (8 + z*(-44 + z*-54)) := by
  rw [d4]
  rw [show Cc^4=(Cc^2)^2 by ring, hz]
  ring

private theorem n5 (B Cc z : R) (hz : Cc^2=B^3*z) :
    hankel (moment B Cc) 5 = B^10 * (16 + z*(-156 + z*(13 + z*-972))) := by
  rw [d5]
  rw [show Cc^4=(Cc^2)^2 by ring, show Cc^6=(Cc^2)^3 by ring, hz]
  ring

private theorem n6 (B Cc z : R) (hz : Cc^2=B^3*z) :
    hankel (moment B Cc) 6 = B^15 * (32 + z*(-480 + z*(1134 + z*(-3004 + z*(-19872 + z*4374))))) := by
  rw [d6]
  rw [show Cc^4=(Cc^2)^2 by ring, show Cc^6=(Cc^2)^3 by ring, show Cc^8=(Cc^2)^4 by ring, show Cc^10=(Cc^2)^5 by ring, hz]
  ring

private theorem n7 (B Cc z : R) (hz : Cc^2=B^3*z) :
    hankel (moment B Cc) 7 = B^21 * (64 + z*(-1360 + z*(7224 + z*(-17229 + z*(-36084 + z*(-440298 + z*(430596 + z*72171))))))) := by
  rw [d7]
  rw [show Cc^4=(Cc^2)^2 by ring, show Cc^6=(Cc^2)^3 by ring, show Cc^8=(Cc^2)^4 by ring, show Cc^10=(Cc^2)^5 by ring, show Cc^12=(Cc^2)^6 by ring, show Cc^14=(Cc^2)^7 by ring, hz]
  ring

private theorem obstruction_zero (B Cc z a b : R) (hz : Cc^2=B^3*z)
    (rel : FirstFour (hankel (moment B Cc)) a b) :
    2*B^25*z^2*pZero z=0 := by
  let D := hankel (moment B Cc)
  have h : triple (D 1*D 3) (D 2^2) (D 0*D 4)
      (D 2*D 4) (D 3^2) (D 1*D 5) (D 3*D 5) (D 4^2) (D 2*D 6) = 0 := by
    rw [show D 0 * D 4 = _ from rel 0 (by decide), show D 1 * D 5 = _ from rel 1 (by decide),
      show D 2 * D 6 = _ from rel 2 (by decide)]
    exact dependent ..
  dsimp only [D] at h
  rw [n0 B Cc z, n1 B Cc z, n2 B Cc z, n3 B Cc z hz, n4 B Cc z hz, n5 B Cc z hz, n6 B Cc z hz] at h
  convert h using 1
  unfold triple pZero homZero
  ring

private theorem obstruction_one (B Cc z a b : R) (hz : Cc^2=B^3*z)
    (rel : FirstFour (hankel (moment B Cc)) a b) :
    B^43*z^4*pOne z=0 := by
  let D := hankel (moment B Cc)
  have h : triple (D 2*D 4) (D 3^2) (D 1*D 5)
      (D 3*D 5) (D 4^2) (D 2*D 6) (D 4*D 6) (D 5^2) (D 3*D 7) = 0 := by
    rw [show D 1 * D 5 = _ from rel 1 (by decide), show D 2 * D 6 = _ from rel 2 (by decide),
      show D 3 * D 7 = _ from rel 3 (by decide)]
    exact dependent ..
  dsimp only [D] at h
  rw [n1 B Cc z, n2 B Cc z, n3 B Cc z hz, n4 B Cc z hz, n5 B Cc z hz, n6 B Cc z hz, n7 B Cc z hz] at h
  convert h using 1
  unfold triple pOne homOne
  ring


/-- Over any field where the two explicit integer contents survive, four consecutive
recurrence equations cannot hold simultaneously when both centered cubic coefficients are nonzero. -/
theorem no_somos {K : Type*} [Field K] (B Cc : K) (hB : B≠0) (hC : Cc≠0)
    (two : (2:K)≠0) (den : (bezoutDenominator:K)≠0) (a b : K) :
    ¬ FirstFour (hankel (moment B Cc)) a b := by
  intro rel
  let z := Cc^2/B^3
  have nz : z≠0 := div_ne_zero (pow_ne_zero _ hC) (pow_ne_zero _ hB)
  have hz : Cc^2=B^3*z := by dsimp [z]; field_simp
  have e0 := obstruction_zero B Cc z a b hz rel
  have e1 := obstruction_one B Cc z a b hz rel
  have p : pZero z=0 := (mul_eq_zero.mp e0).resolve_left (by simp [two,hB,nz])
  have q : pOne z=0 := (mul_eq_zero.mp e1).resolve_left (by simp [hB,nz])
  apply den
  simpa [p,q] using bezout z

theorem denominator_lt : 0 < bezoutDenominator ∧ bezoutDenominator < 2^280 := by
  decide +kernel

/-- When the quadratic coefficient vanishes the zeroth and third equations
already give a nonzero constant times the sixteenth power of the cubic coefficient. -/
theorem no_somos_zero {K : Type*} [Field K] (Cc : K) (hC : Cc≠0)
    (hc : (767637:K)≠0) (a b : K) :
    ¬ FirstFour (hankel (moment 0 Cc)) a b := by
  intro rel
  have e0 := rel 0 (by decide)
  have e3 := rel 3 (by decide)
  norm_num [d0,d1,d2,d3,d4,d5,d6,d7] at e0 e3
  have bad : (767637:K)*Cc^16=0 := by
    linear_combination (26244*Cc^12)*e0 - e3
  exact mul_ne_zero hc (pow_ne_zero _ hC) bad

/-- For rational translations only the three degenerate integers can escape this obstruction. -/
theorem rational_shift (c a b : ℚ) (hm : c≠ -1) (hz : c≠0) (hp : c≠1) :
    ¬ FirstFour (hankel (fun n => TranslatedHasse.value n c)) a b := by
  have hC : c^3-c≠0 := by
    have eqn : c^3-c = c*(c-1)*(c+1) := by ring
    rw [eqn]
    exact mul_ne_zero (mul_ne_zero hz (sub_ne_zero.mpr hp)) (by intro h; apply hm; linarith)
  have eqn : hankel (fun n => TranslatedHasse.value n c) =
      hankel (moment (3*c^2-1) (c^3-c)) :=
    funext (hasse_hankel c)
  rw [eqn]
  by_cases hB : 3*c^2-1=0
  · rw [hB]
    exact no_somos_zero _ hC (by norm_num) a b
  · exact no_somos _ _ hB hC (by norm_num) (by norm_num [bezoutDenominator]) a b

/-- The same conclusion holds in every prime field larger than the Bézout cutoff,
even if the two recurrence coefficients are chosen only after reduction. -/
theorem prime_shift (p : ℕ) [Fact p.Prime] (large : 2^280 ≤ p)
    (c a b : ZMod p) (hC : c^3-c≠0) :
    ¬ FirstFour (hankel (fun n => TranslatedHasse.value n c)) a b := by
  have nonzero (v : ℕ) (pos : 0<v) (small : v<2^280) : (v:ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact Nat.not_dvd_of_pos_of_lt pos (small.trans_le large)
  rw [show hankel (fun n => TranslatedHasse.value n c) =
      hankel (moment (3*c^2-1) (c^3-c)) from funext (hasse_hankel c)]
  by_cases hB : 3*c^2-1=0
  · rw [hB]
    exact no_somos_zero _ hC (nonzero 767637 (by decide) (by decide)) a b
  · exact no_somos _ _ hB hC (nonzero 2 (by decide) (by decide))
      (nonzero _ denominator_lt.1 denominator_lt.2) a b

/-- At the small prime 101 the same obstruction certificate is already nonzero. -/
theorem shift_two_mod_101 (a b : ZMod 101) :
    ¬ FirstFour (hankel (fun n => TranslatedHasse.value n (2 : ZMod 101))) a b := by
  letI : Fact (Nat.Prime 101) := ⟨by decide⟩
  rw [show hankel (fun n => TranslatedHasse.value n (2 : ZMod 101)) =
      hankel (moment (3*(2 : ZMod 101)^2-1) (2^3-2)) from funext (hasse_hankel _)]
  exact no_somos _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) a b

end PrimeFactors.HasseHankelBilinear
