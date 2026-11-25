import PrimeFactors.UnitQuarticRecovery
import Mathlib.Data.Int.Interval

namespace PrimeFactors.ProjectedQuarticLevels

open Finset Polynomial QuarticFactorLane

/-- The weighted spread drops the constant Dickson coordinate. -/
noncomputable def withoutConstant (v : Fin 5 → ℤ) (i : Fin 5) : ℤ := if i=0 then 0 else v i

theorem projected_spread (v : Fin 5 → ℤ) {N x y : ℤ} {s B : ℕ}
    (pair : x*y=N) (gap : |x-y| ≤ 2*(s:ℤ)) (bound : |x|≤B) :
    |trace (UnitQuarticRecovery.inFactorCoordinates N s v) x y-v 0| ≤
      ∑ i, |withoutConstant v i| * (UnitQuarticBox.weight s B i:ℤ) := by
  have eq : trace (UnitQuarticRecovery.inFactorCoordinates N s (withoutConstant v)) x y =
      trace (UnitQuarticRecovery.inFactorCoordinates N s v) x y-v 0 := by
    simp [UnitQuarticRecovery.inFactorCoordinates, withoutConstant, trace]
    ring
  rw [← eq]
  exact UnitQuarticRecovery.trace_bound _ pair gap bound

theorem nonconstant_original (v : Fin 5 → ℤ) (N s : ℤ) (nz : ∃ i : Fin 4, v i.succ ≠ 0) :
    let w := UnitQuarticRecovery.inFactorCoordinates N s v
    w.a≠0 ∨ w.b≠0 ∨ w.c≠0 ∨ w.d≠0 := by
  obtain ⟨i, hi⟩ := nz
  dsimp only [UnitQuarticRecovery.inFactorCoordinates]
  by_contra! h
  obtain ⟨ha,hb,hc,hd⟩ := h
  fin_cases i <;> simp_all

/-- All j with C-S ≤ jM ≤ C+S, when the modulus M is positive. -/
noncomputable def levels (M C S : ℤ) : Finset ℤ := Icc (-((S-C)/M)) ((S+C)/M)

theorem mem_levels {M C S j : ℤ} (hM : 0<M) :
    j ∈ levels M C S ↔ |j*M-C| ≤ S := by
  rw [levels, Finset.mem_Icc, neg_le, Int.le_ediv_iff_mul_le hM,
    Int.le_ediv_iff_mul_le hM, neg_mul, abs_le]
  omega

theorem level_count {M C S : ℤ} {k : ℕ} (hM : 0<M) (width : 2*S < (k:ℤ)*M) :
    (levels M C S).card ≤ k := by
  let lo := -((S-C)/M)
  let hi := (S+C)/M
  change (Icc lo hi).card ≤ k
  by_cases order : lo ≤ hi
  · have hl : |lo*M-C| ≤ S := (mem_levels hM).mp (mem_Icc.mpr ⟨le_rfl,order⟩)
    have hh : |hi*M-C| ≤ S := (mem_levels hM).mp (mem_Icc.mpr ⟨order,le_rfl⟩)
    obtain ⟨hl,_⟩ := abs_le.mp hl
    obtain ⟨_,hh⟩ := abs_le.mp hh
    have dist : hi-lo < (k:ℤ) := by
      by_contra! contrary
      have := mul_le_mul_of_nonneg_right contrary hM.le
      linarith
    rw [Int.card_Icc]
    omega
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge order), card_empty]
    exact Nat.zero_le _

/-- Subtract an exact multiple of the modulus from the trace. -/
noncomputable def shifted (w : Weights) (j M : ℤ) : Weights := {w with e := w.e-j*M}

noncomputable def parent (w : Weights) (N M C S : ℤ) : ℤ[X] :=
  ∏ j ∈ levels M C S, polynomial (shifted w j M) N

theorem parent_ne_zero {w : Weights} {N : ℤ} (M C S : ℤ) (hN : N≠0)
    (nonconstant : w.a≠0 ∨ w.b≠0 ∨ w.c≠0 ∨ w.d≠0) : parent w N M C S ≠ 0 := by
  unfold parent
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply polynomial_nonzero hN
  simpa only [shifted] using nonconstant.imp_right (Or.imp_right (Or.imp_right Or.inl))

theorem parent_degree {w : Weights} {N M C S : ℤ} {k : ℕ} (hM : 0<M)
    (width : 2*S < (k:ℤ)*M) : (parent w N M C S).natDegree ≤ 4*k := by
  unfold parent
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc _ ≤ ∑ _j ∈ levels M C S, 4 := by
             apply sum_le_sum
             intro j _
             unfold polynomial
             compute_degree
       _ = 4*(levels M C S).card := by simp [Nat.mul_comm]
       _ ≤ _ := Nat.mul_le_mul_left 4 (level_count hM width)

/-- One product polynomial covers all true signed coordinates in the coarse lane.
The lift's signed unit congruence is checked independently of the size bound on
the four nonconstant coordinates. An interval with no multiple rejects the lane. -/
theorem parent_root {w : Weights} {N x y M C S : ℤ} (hM : 0<M) (unit : IsCoprime M x)
    (pair : x*y=N) (div : M ∣ value w N x) (spread : |trace w x y-C| ≤ S) :
    (parent w N M C S).IsRoot x := by
  rw [pair_identity w pair] at div
  obtain ⟨j, hj⟩ := unit.pow_right.dvd_of_dvd_mul_left div
  have belongs : j ∈ levels M C S := (mem_levels hM).mpr (by simpa [hj, mul_comm M j] using spread)
  rw [Polynomial.IsRoot, parent, eval_prod]
  exact prod_eq_zero belongs (by
    rw [eval_polynomial, pair_identity _ pair]
    have eq : trace (shifted w j M) x y = trace w x y-j*M := by simp [shifted, trace]; ring
    rw [eq, hj]
    ring)

/-- Failure at a single auxiliary modulus rules out every integer root of the
primitive polynomial in the progression coordinate. -/
theorem reject_modulus (P : ℤ[X]) (q : ℕ)
    (noRoot : ∀ z : ZMod q, ¬(P.map (Int.castRingHom (ZMod q))).IsRoot z) (k : ℤ) :
    ¬P.IsRoot k := fun hk => noRoot _ hk.map

/-- Integer form of the norm-to-level comparison, usable for either short-vector
constant. W is the product of the four weights; R is the coarse radix. -/
theorem width_from_determinant {S M R W A H k : ℕ} (hR : 0<R) (hM : 0<M)
    (short : (2*S)^4*(12960*R^10) ≤ A*W*M^4)
    (size : W ≤ H*R^10) (cost : A*H < k^4*12960) : 2*S < k*M := by
  by_contra! h
  have lower := Nat.mul_le_mul_right (12960*R^10) (Nat.pow_le_pow_left h 4)
  have upper := Nat.mul_le_mul_right (M^4) (Nat.mul_le_mul_left A size)
  have strict := Nat.mul_lt_mul_of_pos_right cost (Nat.mul_pos (pow_pos hR 10) (pow_pos hM 4))
  have same : (k*M)^4*(12960*R^10) = (k^4*12960)*(R^10*M^4) := by ring
  have same' : A*(H*R^10)*M^4 = A*H*(R^10*M^4) := by ring
  rw [same] at lower
  rw [same'] at upper
  exact (not_lt_of_ge (lower.trans (short.trans upper))) strict

/-- At an auxiliary prime a true level must belong to the image obtained by
evaluating F(z)/(M z²) once per nonzero residue z. -/
noncomputable def levelImage (P : ℤ[X]) (M : ℤ) (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  univ.image fun z : (ZMod p)ˣ =>
    (P.map (Int.castRingHom (ZMod p))).eval (z : ZMod p) / ((M : ZMod p)*(z : ZMod p)^2)

theorem level_mem_image {p : ℕ} [Fact p.Prime] {P : ℤ[X]} {M j x y N : ℤ}
    (pair : x*y=N) (unitN : (N : ZMod p) ≠ 0) (unitM : (M : ZMod p) ≠ 0)
    (value : P.eval x=j*M*x^2) : (j : ZMod p) ∈ levelImage P M p := by
  have unitX : (x : ZMod p) ≠ 0 := by
    intro contra
    apply unitN
    rw [← pair, Int.cast_mul, contra, zero_mul]
  apply mem_image.mpr
  refine ⟨Units.mk0 (x : ZMod p) unitX, mem_univ _, ?_⟩
  change (P.map (Int.castRingHom (ZMod p))).eval (x : ZMod p) /
    ((M : ZMod p)*(x : ZMod p)^2) = (j : ZMod p)
  apply (div_eq_iff (mul_ne_zero unitM (pow_ne_zero 2 unitX))).mpr
  rw [eval_map]
  change P.eval₂ (Int.castRingHom (ZMod p)) ((Int.castRingHom (ZMod p)) x) = _
  rw [eval₂_hom, value, map_mul, map_mul, map_pow]
  change (j : ZMod p)*(M : ZMod p)*(x : ZMod p)^2 = _
  ring

/-- For rank four LLL and a weighted l1 spread S, (2S/M)^4 ≤ 2^11 W/(12960R^10).
At R=2^614 at most one level fits; at half that radix at most six fit.
The sharper exact shortest l1 vector uses the 4! Minkowski constant. -/
theorem scale_receipts :
    2^11 * 4 < 12960 ∧
    5^4 * 12960 ≤ 2^11 * 4096 ∧ 2^11 * 4096 < 6^4 * 12960 ∧
    3^4 * 12960 ≤ 16 * 24 * 4096 ∧ 16 * 24 * 4096 < 4^4 * 12960 := by
  decide +kernel

end PrimeFactors.ProjectedQuarticLevels
