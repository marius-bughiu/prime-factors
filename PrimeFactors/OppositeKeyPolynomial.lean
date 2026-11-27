import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic

/-! A positive-degree common divisor of the even and odd coefficient
polynomials detects opposite nonzero roots of a split polynomial. -/
namespace PrimeFactors.OppositeKeyPolynomial
open Polynomial Finset
open scoped Polynomial

/-- Interleave the coefficients of two polynomials. -/
noncomputable def join {R : Type*} [CommRing R] (e o : R[X]) : R[X] :=
  e.comp (X^2) + X * o.comp (X^2)

theorem eval_join {R : Type*} [CommRing R] (e o : R[X]) (a : R) :
    (join e o).eval a=e.eval (a^2)+a*o.eval (a^2) := by
  simp [join,eval_comp]

/-- Multiplication by one more linear factor updates both halves. -/
theorem join_step {R : Type*} [CommRing R] (e o : R[X]) (a : R) :
    join (X*o-C a*e) (e-C a*o)=(X-C a)*join e o := by
  simp [join,mul_comp,sub_comp]
  ring

private theorem eq_at_root {K : Type*} [Field K] {m : ℕ} (v : Fin m → K) (a : K) :
    (∏ i, (X-C (v i))).eval a = 0 ↔ ∃ i, v i=a := by
  simp only [Polynomial.eval_prod,eval_sub,eval_X,eval_C,Finset.prod_eq_zero_iff,mem_univ,true_and,sub_eq_zero]
  exact exists_congr fun _ => eq_comm

private theorem comp_divides {K : Type*} [Field K] {d e : K[X]} (hd : d∣e) (t : K[X]) :
    d.comp t∣e.comp t := by
  obtain ⟨g,rfl⟩ := hd
  exact ⟨_,mul_comp _ _ _⟩

/-- The finite-field equivalence behind the shorter Euclidean search.
The constant term is tested separately before applying this theorem. -/
theorem opposite_iff {K : Type*} [Field K] (two : (2:K)≠0) {m : ℕ} (v : Fin m → K)
    (nonzero : ∀ i, v i≠0) {e o : K[X]}
    (decomposition : join e o=∏ i, (X-C (v i))) :
    (∃ i j, v i = -v j) ↔ ∃ d : K[X], 0<d.natDegree ∧ d∣e ∧ d∣o := by
  constructor
  · rintro ⟨i,j,eq⟩
    let a := v j
    have root (z : K) (h : ∃ k, v k=z) : e.eval (z^2)+z*o.eval (z^2)=0 := by
      rw [←eval_join,decomposition]
      exact (eq_at_root v z).mpr h
    have pos := root a ⟨j,rfl⟩
    have neg := root (-a) ⟨i,eq⟩
    rw [neg_sq] at neg
    have oh : o.eval (a^2)=0 := by
      apply (mul_eq_zero.mp (show (2*a)*o.eval (a^2)=0 by linear_combination pos-neg)).resolve_left
      exact mul_ne_zero two (nonzero j)
    have eh : e.eval (a^2)=0 := by simpa [oh] using pos
    exact ⟨X-C (a^2),by rw [natDegree_X_sub_C]; decide,dvd_iff_isRoot.mpr eh,dvd_iff_isRoot.mpr oh⟩
  · rintro ⟨d,degree,de,do'⟩
    have factor : d.comp (X^2)∣∏ i, (X-C (v i)) := by
      rw [←decomposition]
      exact dvd_add (comp_divides de _) (dvd_mul_of_dvd_right (comp_divides do' _) _)
    have split := splits_of_splits_of_dvd (RingHom.id K)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero (v i)))
      (splits_prod _ (fun i _ => splits_X_sub_C _)) factor
    have hd : (d.comp (X^2)).degree≠0 := by
      intro h
      have n := natDegree_eq_of_degree_eq_some h
      have pos : 0<(d.comp (X^2)).natDegree := by
        rw [natDegree_comp,natDegree_X_pow]; omega
      exact (Nat.ne_of_gt pos) n
    obtain ⟨a,h⟩ := exists_root_of_splits (RingHom.id K) split hd
    have root : d.eval (a^2)=0 := by
      change (d.comp (X^2)).eval a=0 at h
      simpa [eval_comp] using h
    have eh := eval_eq_zero_of_dvd_of_eval_eq_zero de root
    have oh := eval_eq_zero_of_dvd_of_eval_eq_zero do' root
    have both (b : K) (same : b^2=a^2) : ∃ i, v i=b := by
      apply (eq_at_root v b).mp
      rw [←decomposition,eval_join,same,eh,oh]
      ring
    obtain ⟨i,hi⟩ := both (-a) (neg_sq a)
    obtain ⟨j,hj⟩ := both a rfl
    exact ⟨i,j,hj ▸ hi⟩

end PrimeFactors.OppositeKeyPolynomial
