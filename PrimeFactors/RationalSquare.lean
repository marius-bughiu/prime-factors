import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- A reconstruction from the public square supplies a square congruence with known root. -/
theorem rationalSquare_relation {R : Type*} [CommRing R] {a b x : R}
    (relation : a * x^2 = b) : (a*x)^2 = a*b := by
  rw [← relation]
  ring

/-- A Euclidean update preserves every represented integer pair. -/
theorem rationalSquare_span_step (i j t u v c d : ℤ) :
    i*u+j*v = (j+i*t)*v+i*(u-t*v) ∧
    i*c+j*d = (j+i*t)*d+i*(c-t*d) := by constructor <;> ring

/-- For adjacent Euclidean vectors (b,T) and (B,-S), no nonzero combination
fits both strict bounds. One can change the sign of the second coordinate
of the whole lattice to put its vectors in this convention. -/
theorem rationalSquare_adjacent_min {b B T S i j : ℤ}
    (hb : 0 ≤ b) (hB : 0 < B) (hT : 0 < T) (hS : 0 ≤ S)
    (hu : |i*b+j*B| < B) (hv : |i*T-j*S| < T) : i = 0 ∧ j = 0 := by
  obtain ⟨u₁,u₂⟩ := abs_lt.mp hu
  obtain ⟨v₁,v₂⟩ := abs_lt.mp hv
  have nonnegative (k l : ℤ) (hk : 0 ≤ k) (hl : 1 ≤ l) :
      B ≤ k*b+l*B := by nlinarith [mul_nonneg hk hb, mul_nonneg (sub_nonneg.mpr hl) hB.le]
  have opposite (k l : ℤ) (hk : 1 ≤ k) (hl : 0 ≤ l) :
      T ≤ k*T+l*S := by nlinarith [mul_nonneg (sub_nonneg.mpr hk) hT.le, mul_nonneg hl hS]
  by_cases jp : 0 < j
  · by_cases ip : 0 ≤ i
    · have := nonnegative i j ip (by omega)
      omega
    · have := opposite (-i) j (by omega) jp.le
      nlinarith
  · by_cases jn : j < 0
    · by_cases ine : i ≤ 0
      · have := nonnegative (-i) (-j) (by omega) (by omega)
        nlinarith
      · have := opposite i (-j) (by omega) (by omega)
        nlinarith
    · have jz : j = 0 := by omega
      subst j
      simp only [zero_mul, sub_zero] at v₁ v₂
      constructor
      · by_contra nz
        rcases lt_or_gt_of_ne nz with h | h
        · have := opposite (-i) 0 (by omega) (by omega)
          nlinarith
        · have := opposite i 0 (by omega) (by omega)
          nlinarith
      · rfl

/-- Two small fractions representing the same residue have zero determinant. -/
theorem rationalSquare_box_unique {n h u v b a r : ℤ}
    (limit : 2*h^2 < n) (hh : 0 ≤ h)
    (hu : |u| ≤ h) (hv : |v| ≤ h) (hb : |b| ≤ h) (ha : |a| ≤ h)
    (first : u ≡ v*r [ZMOD n]) (second : b ≡ a*r [ZMOD n]) : u*a = b*v := by
  have eqv : u*a ≡ b*v [ZMOD n] := by
    calc
      u*a ≡ (v*r)*a [ZMOD n] := first.mul_right a
      _ = (a*r)*v := by ring
      _ ≡ b*v [ZMOD n] := second.symm.mul_right v
  have divides := Int.modEq_iff_dvd.mp eqv
  obtain ⟨k, hk⟩ := divides
  have bound : |b*v-u*a| < n := calc
    _ ≤ |b*v| + |u*a| := abs_sub _ _
    _ ≤ h*h+h*h := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul hb hv (abs_nonneg _) hh) (mul_le_mul hu ha (abs_nonneg _) hh)
    _ < n := by nlinarith
  rw [hk, abs_mul, abs_of_pos (show 0 < n by nlinarith [sq_nonneg h])] at bound
  have kz : k = 0 := by
    by_contra nz
    have h₁ : 1 ≤ |k| := by have := abs_pos.mpr nz; omega
    nlinarith [mul_nonneg (show 0 ≤ n by nlinarith [sq_nonneg h]) (sub_nonneg.mpr h₁)]
  subst k
  simpa using (sub_eq_zero.mp (show b*v-u*a = 0 by simpa using hk)).symm

/-- Positive reduced fractions with the same determinant are literally the same pair. -/
theorem rationalSquare_reduced_unique {u v b a : ℕ}
    (hv : 0 < v) (ha : 0 < a) (left : u.Coprime v) (right : b.Coprime a)
    (equal : u*a = b*v) : u=b ∧ v=a := by
  have h₁ : v ∣ a := left.symm.dvd_of_dvd_mul_left (equal ▸ dvd_mul_left v b)
  have h₂ : a ∣ v := right.symm.dvd_of_dvd_mul_left (equal.symm ▸ dvd_mul_left a u)
  have same := Nat.dvd_antisymm h₁ h₂
  subst a
  exact ⟨Nat.eq_of_mul_eq_mul_right hv equal, rfl⟩

/-- Final arithmetic comparison at B=65536, once the proposal and fixed-work
bounds in the stated operation model have been established. -/
theorem rationalSquare_work_comparison (direct proposals work : ℚ)
    (large : (2:ℚ)^1012 < direct)
    (saving : (2:ℚ)^45 * proposals ≤ direct)
    (budget : work ≤ (2:ℚ)^20 * proposals + (2:ℚ)^47) :
    (2:ℚ)^24 * work < direct := by
  have fixedCost : (2:ℚ)^72 < direct :=
    lt_trans (by norm_num) large
  linarith only [saving, budget, fixedCost]

end PrimeFactors
