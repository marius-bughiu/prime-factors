import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors.QuarticFactorLane
open Polynomial

/-- Integer coefficients of a trace on a factor pair. -/
structure Weights where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ

def trace (w : Weights) (x y : ℤ) : ℤ := w.d*y^2+w.b*y+w.e+w.a*x+w.c*x^2

def value (w : Weights) (N x : ℤ) : ℤ :=
  w.d*N^2+w.b*N*x+w.e*x^2+w.a*x^3+w.c*x^4

/-- Divisibilities of the first four coefficients of F(u+t), with no factorial division. -/
def conditions (w : Weights) (N R u : ℤ) : Prop :=
  R^4 ∣ value w N u ∧
  R^3 ∣ w.b*N+2*w.e*u+3*w.a*u^2+4*w.c*u^3 ∧
  R^2 ∣ w.e+3*w.a*u+6*w.c*u^2 ∧
  R ∣ w.a+4*w.c*u

theorem expansion (w : Weights) (N u t : ℤ) :
    value w N (u+t) = value w N u +
      (w.b*N+2*w.e*u+3*w.a*u^2+4*w.c*u^3)*t +
      (w.e+3*w.a*u+6*w.c*u^2)*t^2 + (w.a+4*w.c*u)*t^3 + w.c*t^4 := by
  unfold value
  ring

/-- The entire residue class has value divisible by the fourth power of the radix. -/
theorem fourth_power {w : Weights} {N R u x : ℤ} (divisions : conditions w N R u)
    (lane : x ≡ u [ZMOD R]) : R^4 ∣ value w N x := by
  obtain ⟨⟨k₀,h₀⟩,⟨k₁,h₁⟩,⟨k₂,h₂⟩,⟨k₃,h₃⟩⟩ := divisions
  obtain ⟨t,ht⟩ := Int.modEq_iff_dvd.mp lane.symm
  rw [show x=u+R*t by linarith only [ht],expansion,h₀,h₁,h₂,h₃]
  exact ⟨k₀+k₁*t+k₂*t^2+k₃*t^3+w.c*t^4,by ring⟩

theorem pair_identity {N x y : ℤ} (w : Weights) (pair : x*y=N) :
    value w N x = x^2 * trace w x y := by
  rw [← pair]
  unfold value trace
  ring

/-- A public coprimality test on the product suffices for cancellation at each factor. -/
theorem trace_divides {w : Weights} {N R u x y : ℤ} (cop : IsCoprime R N)
    (divisions : conditions w N R u) (lane : x ≡ u [ZMOD R]) (pair : x*y=N) :
    R^4 ∣ trace w x y := by
  have cx : IsCoprime R x := (show IsCoprime R (x*y) from pair.symm ▸ cop).of_mul_right_left
  have div := fourth_power divisions lane
  rw [pair_identity w pair] at div
  exact cx.pow.dvd_of_dvd_mul_left div

theorem trace_vanishes {w : Weights} {N R u x y : ℤ} (cop : IsCoprime R N)
    (divisions : conditions w N R u) (lane : x ≡ u [ZMOD R]) (pair : x*y=N)
    (short : |trace w x y| < R^4) : trace w x y = 0 :=
  Int.eq_zero_of_abs_lt_dvd (trace_divides cop divisions lane pair) short

noncomputable def polynomial (w : Weights) (N : ℤ) : ℤ[X] :=
  C (w.d*N^2)*X^0 + C (w.b*N)*X^1 + C w.e*X^2 + C w.a*X^3 + C w.c*X^4

theorem eval_polynomial (w : Weights) (N x : ℤ) : (polynomial w N).eval x=value w N x := by
  simp [polynomial,value]

theorem polynomial_nonzero {w : Weights} {N : ℤ} (pos : N≠0)
    (nonzero : w.a≠0 ∨ w.b≠0 ∨ w.c≠0 ∨ w.d≠0 ∨ w.e≠0) : polynomial w N ≠ 0 := by
  intro eq
  have zeroCoeff (i : ℕ) : (polynomial w N).coeff i = 0 := by rw [eq,coeff_zero]
  have a := zeroCoeff 3
  have b := zeroCoeff 1
  have c := zeroCoeff 4
  have d := zeroCoeff 0
  have e := zeroCoeff 2
  simp only [polynomial,coeff_add,coeff_C_mul_X_pow] at a b c d e
  norm_num at a b c d e
  rcases nonzero with ha|hb|hc|hd|he
  · exact ha a
  · exact hb (b.resolve_right pos)
  · exact hc c
  · exact hd (d.resolve_right pos)
  · exact he e

/-- A finite, exact search space for a lane whose trace is forced to vanish. -/
noncomputable def candidates (w : Weights) (N : ℤ) : Finset ℤ :=
  (polynomial w N).roots.toFinset

theorem candidates_card (w : Weights) (N : ℤ) : (candidates w N).card ≤ 4 := by
  have degree : (polynomial w N).natDegree ≤ 4 := by unfold polynomial; compute_degree
  exact ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)).trans degree

theorem mem_candidates {w : Weights} {N R u x y : ℤ} (pos : N≠0)
    (nonzero : w.a≠0 ∨ w.b≠0 ∨ w.c≠0 ∨ w.d≠0 ∨ w.e≠0) (cop : IsCoprime R N)
    (divisions : conditions w N R u) (lane : x ≡ u [ZMOD R]) (pair : x*y=N)
    (short : |trace w x y| < R^4) : x ∈ candidates w N := by
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots (polynomial_nonzero pos nonzero)).mpr
  rw [Polynomial.IsRoot,eval_polynomial,pair_identity w pair,trace_vanishes cop divisions lane pair short,mul_zero]

end PrimeFactors.QuarticFactorLane
