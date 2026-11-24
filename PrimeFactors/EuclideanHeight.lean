import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors.EuclideanHeight

/-- Check the minimum product of denominator and absolute remainder, one Euclidean
interval at a time. The first omitted denominator must reach the requested limit. -/
def check : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _, _, _ => false
  | fuel+1, limit, bound, a, b, R, S =>
    let c := a+(R/S)*b
    S != 0 && b ≤ c && bound ≤ b*S &&
      (limit ≤ c || check fuel limit bound b c S (R%S))

private theorem stripe {b c S T i j : ℤ} (bp : 0 < b) (cp : 0 < c)
    (sp : 0 ≤ S) (tp : 0 ≤ T) (pos : 0 < i*b+j*c) (small : i*b+j*c < c) :
    S ≤ |i*S-j*T| := by
  rcases le_or_gt 0 j with hj | hj
  · by_cases hi : 0 < i
    · have jzero : j = 0 := by
        by_contra h
        have : 1 ≤ j := by omega
        nlinarith [mul_pos hi bp, mul_nonneg (show 0 ≤ j-1 by omega) cp.le]
      subst j
      exact le_trans (by nlinarith [mul_nonneg (show 0 ≤ i-1 by omega) sp]) (le_abs_self _)
    · have ineg : i < 0 := by
        by_contra h
        have iz : i=0 := by omega
        subst i
        simp only [zero_mul, zero_add] at pos small
        have : 1 ≤ j := by
          by_contra! notPositive
          have zero : j = 0 := by omega
          simp [zero] at pos
        nlinarith [mul_nonneg (show 0 ≤ j-1 by omega) cp.le]
      exact le_trans (by nlinarith [mul_nonneg (show 0 ≤ -i-1 by omega) sp, mul_nonneg hj tp])
        (neg_le_abs _)
  · have hi : 0 < i := by
      by_contra! nonpositive
      nlinarith [mul_nonpos_of_nonpos_of_nonneg nonpositive bp.le, mul_neg_of_neg_of_pos hj cp]
    exact le_trans (by nlinarith [mul_nonneg (show 0 ≤ i-1 by omega) sp,
      mul_nonpos_of_nonpos_of_nonneg hj.le tp]) (le_abs_self _)

private theorem check_basis {fuel limit bound a b R S : ℕ}
    (ok : check fuel limit bound a b R S = true)
    {i j : ℤ} (bp : 0 < b) (vpos : 0 < i*a+j*b)
    (low : (b : ℤ) ≤ i*a+j*b) (high : i*a+j*b < limit) :
    (bound : ℤ) ≤ (i*a+j*b)*|j*S-i*R| := by
  induction fuel generalizing a b R S i j with
  | zero => simp [check] at ok
  | succ fuel ih =>
    simp only [check, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨⟨_, monotone⟩, hb⟩, edge⟩ := ok
    let t := R/S
    let c := a+t*b
    have split : (R : ℤ) = (t : ℤ)*S+(R%S : ℕ) := by
      exact_mod_cast (Nat.div_add_mod' R S).symm
    have den : i*a+j*b = (j-i*t)*b+i*c := by dsimp [c]; push_cast; ring
    have remn : j*S-i*R = (j-i*t)*S-i*(R%S : ℕ) := by rw [split]; ring
    have cp : 0 < c := lt_of_lt_of_le bp monotone
    by_cases short : i*a+j*b < c
    · have gap := stripe (by exact_mod_cast bp) (by exact_mod_cast cp)
          (show (0 : ℤ) ≤ S by positivity) (show (0 : ℤ) ≤ (R%S : ℕ) by positivity)
          (den ▸ vpos) (den ▸ short)
      rw [← remn] at gap
      exact (show (bound : ℤ) ≤ (b : ℤ)*S by exact_mod_cast hb).trans
        (mul_le_mul low gap (by positivity) vpos.le)
    · have next := edge.resolve_left (by intro endAt; exact short (high.trans_le (by exact_mod_cast endAt)))
      have result := ih next cp (den ▸ vpos) (den ▸ le_of_not_gt short) (den ▸ high)
      rw [← den, abs_sub_comm, ← remn] at result
      exact result

/-- A successful check covers every signed remainder of every denominator below N,
including nonprimitive fractions. The integer k is unrestricted. -/
theorem lower_bound {fuel N r B : ℕ} (ok : check fuel N B 0 1 N r = true)
    {v k : ℤ} (positive : 0 < v) (small : v < N) :
    (B : ℤ) ≤ v * |v*r-k*N| := by
  simpa using (check_basis (i := k) (j := v) ok (by decide)
    (by simpa using positive) (by simp; omega) (by simpa using small))

/-- The other sign of a modular residue gives the same absolute remainder
set for every denominator. -/
theorem lower_bound_neg {fuel N r B : ℕ} (ok : check fuel N B 0 1 N r = true)
    {v k : ℤ} (positive : 0 < v) (small : v < N) :
    (B : ℤ) ≤ v * |v*((N : ℤ)-r)-k*N| := by
  have equal : v*((N : ℤ)-r)-k*N = -(v*r-(v-k)*N) := by ring
  rw [equal, abs_neg]
  exact lower_bound ok positive small

/-- Either mixed sign for the rational u/v forces its height up to B. -/
theorem ratio_bound {fuel N r B u v : ℕ} (ok : check fuel N B 0 1 N r = true)
    (vp : 0<v) (small : v<N)
    (mixed : (u : ℤ) ≡ (v : ℤ)*r [ZMOD (N : ℤ)] ∨
      -(u : ℤ) ≡ (v : ℤ)*r [ZMOD (N : ℤ)]) : B≤u*v := by
  have pos : (0 : ℤ)<v := by exact_mod_cast vp
  have top : (v : ℤ)<N := by exact_mod_cast small
  have lower {t : ℤ} (matchRoot : t ≡ (v : ℤ)*r [ZMOD (N : ℤ)]) : (B : ℤ) ≤ v*|t| := by
    obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp matchRoot
    have eqn : (v : ℤ)*r-k*N=t := by rw [mul_comm k]; omega
    simpa only [eqn] using (lower_bound (k:=k) ok pos top)
  rcases mixed with plus | minus
  · have h := lower plus
    rw [abs_of_nonneg (Nat.cast_nonneg u), mul_comm] at h
    exact_mod_cast h
  · have h := lower minus
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg u), mul_comm] at h
    exact_mod_cast h

/-- The Euclidean minimum excludes a small first row even when its partner
may have any height satisfying the original strict shortness condition. -/
theorem exclude {N B u v g A H : ℕ} (gp : 0<g) (minimum : B≤u*v)
    (cutoff : N*H≤2*B^2) (heights : 2*(g*u*v)^2<N*A) : H<A := by
  have up : u*v ≤ g*u*v := by
    rw [mul_assoc]
    exact Nat.le_mul_of_pos_left _ gp
  have strict : N*H<N*A := by
    calc
      _ ≤ 2*B^2 := cutoff
      _ ≤ 2*(g*u*v)^2 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (minimum.trans up) 2)
      _ < _ := heights
  exact lt_of_not_ge fun bad => (not_lt_of_ge (Nat.mul_le_mul_left _ bad)) strict

end PrimeFactors.EuclideanHeight
