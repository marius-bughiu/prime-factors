import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

namespace PrimeFactors.PowerFactorLanes
open Polynomial Finset

/-- Divisibilities of the translated polynomial's coefficients up to order k-1. -/
def conditions (P : ℤ[X]) (u R : ℤ) (k : ℕ) : Prop :=
  ∀ j < k, R^(k-j) ∣ (taylor u P).coeff j

/-- A congruence on the whole lane. This works for any polynomial, including
terms of degree greater than k and the case k=0. -/
theorem taylor_lane {P : ℤ[X]} {u R x : ℤ} {k : ℕ}
    (hc : conditions P u R k) (lane : x ≡ u [ZMOD R]) : R^k ∣ P.eval x := by
  obtain ⟨t,ht⟩ := Int.modEq_iff_dvd.mp lane.symm
  rw [← taylor_eval_sub u P x,eval_eq_sum_range,ht]
  apply Finset.dvd_sum
  intro j _
  rw [mul_pow]
  by_cases small : j<k
  · obtain ⟨q,hq⟩ := hc j small
    have power : R^(k-j)*R^j=R^k := by rw [← pow_add,Nat.sub_add_cancel small.le]
    rw [hq]
    exact ⟨q*t^j,by rw [← power]; ring⟩
  · have powers : R^k ∣ R^j := pow_dvd_pow R (le_of_not_gt small)
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left powers _) _

/-- Indices 0 through m-1 encode powers of y, m is the constant, and indices
m+1 through 2m encode powers of x. All exponent subtractions are in ℕ. -/
noncomputable def trace (m : ℕ) (c : ℕ → ℤ) (x y : ℤ) : ℤ :=
  ∑ j ∈ range (2*m+1), c j*x^(j-m)*y^(m-j)

noncomputable def polynomial (m : ℕ) (c : ℕ → ℤ) (N : ℤ) : ℤ[X] :=
  ∑ j ∈ range (2*m+1), monomial j (c j*N^(m-j))

theorem pair_term (m j : ℕ) (a x y : ℤ) :
    a*(x*y)^(m-j)*x^j = x^m*(a*x^(j-m)*y^(m-j)) := by
  by_cases low : j≤m
  · rw [Nat.sub_eq_zero_of_le low,pow_zero,mul_one,mul_pow]
    calc _ = (x^(m-j)*x^j)*(a*y^(m-j)) := by ring
         _ = _ := by rw [← pow_add,Nat.sub_add_cancel low]
  · have high := le_of_not_ge low
    simp only [Nat.sub_eq_zero_of_le high,pow_zero,mul_one]
    calc _ = a*(x^m*x^(j-m)) := by rw [← pow_add,Nat.add_sub_of_le high]
         _ = _ := by ring

theorem pair_identity {N x y : ℤ} (m : ℕ) (c : ℕ → ℤ) (pair : x*y=N) :
    (polynomial m c N).eval x = x^m * trace m c x y := by
  rw [← pair,polynomial,trace,eval_finset_sum,mul_sum]
  exact sum_congr rfl fun j _ => by rw [eval_monomial]; exact pair_term m j (c j) x y

theorem coeff_at {m j : ℕ} (c : ℕ → ℤ) (N : ℤ) (hj : j≤2*m) :
    (polynomial m c N).coeff j = c j*N^(m-j) := by
  simp [polynomial,finset_sum_coeff,coeff_monomial,mem_range.mpr (Nat.lt_succ_of_le hj)]

theorem polynomial_nonzero {m : ℕ} {c : ℕ → ℤ} {N : ℤ}
    (pos : N≠0) (nz : ∃ j≤2*m, c j≠0) : polynomial m c N ≠ 0 := by
  obtain ⟨j,hj,nonzero⟩ := nz
  intro eq
  have bad := coeff_at c N hj
  rw [eq,coeff_zero] at bad
  exact (mul_ne_zero nonzero (pow_ne_zero _ pos)) bad.symm

theorem degree_bound (m : ℕ) (c : ℕ → ℤ) (N : ℤ) :
    (polynomial m c N).natDegree ≤ 2*m := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ (mem_range.mp hj))

/-- The radix can be tested for coprimality with the input alone. -/
theorem trace_divides {m : ℕ} {c : ℕ → ℤ} {N R u x y : ℤ} (cop : IsCoprime R N)
    (hc : conditions (polynomial m c N) u R (2*m)) (lane : x ≡ u [ZMOD R]) (pair : x*y=N) :
    R^(2*m) ∣ trace m c x y := by
  have cx : IsCoprime R x := (show IsCoprime R (x*y) from pair.symm ▸ cop).of_mul_right_left
  have div := taylor_lane hc lane
  rw [pair_identity m c pair] at div
  exact cx.pow.dvd_of_dvd_mul_left div

theorem trace_vanishes {m : ℕ} {c : ℕ → ℤ} {N R u x y : ℤ} (cop : IsCoprime R N)
    (hc : conditions (polynomial m c N) u R (2*m)) (lane : x ≡ u [ZMOD R]) (pair : x*y=N)
    (short : |trace m c x y| < R^(2*m)) : trace m c x y = 0 :=
  Int.eq_zero_of_abs_lt_dvd (trace_divides cop hc lane pair) short

noncomputable def candidates (m : ℕ) (c : ℕ → ℤ) (N : ℤ) : Finset ℤ :=
  (polynomial m c N).roots.toFinset

theorem candidates_card (m : ℕ) (c : ℕ → ℤ) (N : ℤ) : (candidates m c N).card ≤ 2*m :=
  ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)).trans (degree_bound m c N)

theorem mem_candidates {m : ℕ} {c : ℕ → ℤ} {N R u x y : ℤ}
    (pos : N≠0) (nz : ∃ j≤2*m, c j≠0) (cop : IsCoprime R N)
    (hc : conditions (polynomial m c N) u R (2*m)) (lane : x ≡ u [ZMOD R]) (pair : x*y=N)
    (short : |trace m c x y| < R^(2*m)) : x ∈ candidates m c N := by
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots (polynomial_nonzero pos nz)).mpr
  rw [Polynomial.IsRoot,pair_identity m c pair,trace_vanishes cop hc lane pair short,mul_zero]

end PrimeFactors.PowerFactorLanes
