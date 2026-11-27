import PrimeFactors.JacobiMomentRecurrence
import Mathlib.FieldTheory.Finite.Basic

/-! # Sparse recurrences on the squares of a prime field

A polynomial with fewer than half as many nonzero terms as there are field units
misses at least one residue class of exponents. Orthogonality then restores the
one excluded square to its root set. This applies to projected Jacobi recurrences.
-/
namespace PrimeFactors.JacobiSparseSupport
open Finset Polynomial JacobiMomentRecurrence

private theorem twice {p : ℕ} [Fact p.Prime] (odd : p≠2) : 2*((p-1)/2)=p-1 := by
  obtain ⟨k,h⟩ := (Fact.out : p.Prime).odd_of_ne_two odd
  omega

private theorem hits {d r j : ℕ} (hr : r<d) : d ∣ j+(d-r) ↔ j%d=r := by
  have one : d ∣ r+(d-r) := by rw [Nat.add_sub_of_le hr.le]
  constructor
  · intro h
    have eqn := (Nat.modEq_zero_iff_dvd.mpr h).trans (Nat.modEq_zero_iff_dvd.mpr one).symm
    have h' := Nat.ModEq.add_right_cancel' (d-r) eqn
    simpa [Nat.ModEq,Nat.mod_eq_of_lt hr] using h'
  · intro h
    have h' : j ≡ r [MOD d] := by simpa [Nat.ModEq, Nat.mod_eq_of_lt hr] using h
    exact Nat.modEq_zero_iff_dvd.mp ((h'.add_right (d-r)).trans (Nat.modEq_zero_iff_dvd.mpr one))

/-- Summing over the field units isolates the coefficient bucket with exponent r (mod d). -/
theorem bucket {p : ℕ} [Fact p.Prime] (odd : p≠2) (P : (ZMod p)[X]) {r : ℕ}
    (hr : r<(p-1)/2) :
    (∑ t : (ZMod p)ˣ, P.eval ((t:ZMod p)^2) * ((t:ZMod p)^2)^((p-1)/2-r)) =
      -(∑ j ∈ P.support.filter (fun j => j%((p-1)/2)=r), P.coeff j) := by
  classical
  let d := (p-1)/2
  have term (j : ℕ) :
      (∑ t : (ZMod p)ˣ, ((t:ZMod p)^2)^j*((t:ZMod p)^2)^(d-r)) =
      if j%d=r then (-1:ZMod p) else 0 := by
    simp_rw [←pow_add, ←pow_mul]
    rw [FiniteField.sum_pow_units, ZMod.card, ←twice odd]
    simp only [Nat.mul_dvd_mul_iff_left (by decide : 0<2), d, hits hr]
  calc
    _ = ∑ j ∈ P.support, P.coeff j*(∑ t : (ZMod p)ˣ, ((t:ZMod p)^2)^j*((t:ZMod p)^2)^(d-r)) := by
      simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul, mul_assoc]
      rw [sum_comm]
      simp_rw [mul_sum]
      rfl
    _ = _ := by
      simp_rw [term, Finset.sum_filter]
      rw [← Finset.sum_neg_distrib]
      apply sum_congr rfl
      intro j _
      by_cases h : j%d=r <;> simp [d] at h ⊢ <;> simp [h]

private theorem two_ne {p : ℕ} [Fact p.Prime] (odd : p≠2) : (2:ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])

/-- If a polynomial vanishes on every active square, its Fourier sums consist of
the two traces 2 and -2 that were removed from the sequence. -/
theorem exceptional_sum {p : ℕ} [Fact p.Prime] (odd : p≠2) (P : (ZMod p)[X])
    (roots : ∀ z∈evenBases p, P.eval z=0) (h : ℕ) :
    (∑ t : (ZMod p)ˣ, P.eval ((t:ZMod p)^2)*((t:ZMod p)^2)^h) = 2*(P.eval 4*4^h) := by
  classical
  let a : (ZMod p)ˣ := Units.mk0 2 (two_ne odd)
  have distinct : a ≠ -a := by
    intro eqn
    have contra := congrArg Units.val eqn
    change (2:ZMod p) = -2 at contra
    apply mul_ne_zero (two_ne odd) (two_ne odd)
    linear_combination contra
  calc
    _ = ∑ t ∈ ({a,-a} : Finset (ZMod p)ˣ), P.eval ((t:ZMod p)^2)*((t:ZMod p)^2)^h := by
      symm
      apply sum_subset (subset_univ _)
      intro t _ outside
      have ne : t≠a ∧ t≠-a := by simpa using outside
      have reg : (t:ZMod p) ∈ active p := by
        simp only [active,mem_sdiff,mem_univ,mem_insert,mem_singleton,true_and,not_or]
        exact ⟨Units.ne_zero t,fun h => ne.1 (Units.ext h), fun h => ne.2 (Units.ext h)⟩
      rw [roots _ (mem_image_of_mem _ reg),zero_mul]
    _ = _ := by
      rw [sum_pair distinct]
      change P.eval (2^2)*(2^2)^h + P.eval ((-2)^2)*((-2)^2)^h = _
      norm_num
      ring

/-- Fewer than d terms omit some residue class of exponents. As a consequence
they cannot single out the missing square 4 among the nonzero squares. -/
theorem sparse_forces_extra_root {p : ℕ} [Fact p.Prime] (odd : p≠2) (P : (ZMod p)[X])
    (few : P.support.card < (p-1)/2) (roots : ∀ z∈evenBases p, P.eval z=0) : P.eval 4=0 := by
  classical
  let d := (p-1)/2
  have size : (P.support.image (fun j => j%d)).card < (range d).card := by
    rw [card_range]; exact card_image_le.trans_lt few
  obtain ⟨r,hr,missing⟩ := exists_mem_not_mem_of_card_lt_card size
  have hr' := mem_range.mp hr
  have empty : (P.support.filter fun j => j%d=r) = ∅ := by
    exact filter_eq_empty_iff.mpr (fun j hj hit => missing (mem_image.mpr ⟨j,hj,hit⟩))
  have b := bucket odd P hr'
  rw [exceptional_sum odd P roots, empty] at b
  simp only [sum_empty, neg_zero] at b
  have four : (4:ZMod p)≠0 := by
    rw [show (4:ZMod p)=2*2 by norm_num]; exact mul_ne_zero (two_ne odd) (two_ne odd)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp b).resolve_left (two_ne odd))).resolve_right (pow_ne_zero _ four)

theorem bucket_zero {p : ℕ} [Fact p.Prime] (odd : p≠2) (P : (ZMod p)[X])
    (few : P.support.card < (p-1)/2) (roots : ∀ z∈evenBases p, P.eval z=0) {r : ℕ}
    (hr : r<(p-1)/2) :
    (∑ j ∈ P.support.filter (fun j => j%((p-1)/2)=r), P.coeff j) = 0 := by
  have h := bucket odd P hr
  rw [exceptional_sum odd P roots,sparse_forces_extra_root odd P few roots] at h
  simpa using h.symm

/-- A recurrence modulo the product projects to a zero sum of coefficients in
each exponent class modulo half the unit group order of a hidden prime. -/
theorem projected_buckets {N p : ℕ} [NeZero N] [Fact p.Prime] (odd : p≠2)
    (f : ZMod N →+* ZMod p)
    (project : ∀ k, f (ProjectiveWordMoments.moment N k) = component p k)
    (P : (ZMod N)[X]) (few : P.support.card < (p-1)/2)
    (fit : ∀ n, shift P (fun k => ProjectiveWordMoments.moment N (2*(k+1))) n=0)
    {r : ℕ} (hr : r<(p-1)/2) :
    ∑ j ∈ P.support.filter (fun j => j%((p-1)/2)=r), f (P.coeff j) = 0 := by
  classical
  have roots := (component_even_roots odd (P.map f) 0).mp (fun i => by
    have zero := congrArg f (fit (0+(i:ℕ)))
    simpa only [shift_map,project,map_zero] using zero)
  have sub := Polynomial.support_map_subset f P
  have local_sum := bucket_zero odd (P.map f) ((Finset.card_le_card sub).trans_lt few) roots hr
  rw [← local_sum]
  symm
  simp only [Polynomial.coeff_map]
  apply sum_subset (filter_subset_filter _ sub)
  intro j hj excluded
  have absent : j ∉ (P.map f).support := fun hj' => excluded (mem_filter.mpr ⟨hj', (mem_filter.mp hj).2⟩)
  simpa only [Polynomial.coeff_map] using Polynomial.not_mem_support_iff.mp absent

end PrimeFactors.JacobiSparseSupport
