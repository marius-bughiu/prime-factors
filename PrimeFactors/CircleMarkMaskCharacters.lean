import PrimeFactors.CircleMarkSharedScores
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! Restriction of a masked Jacobi score to units, and its principal
Dirichlet character coefficient in any exact character expansion. -/

namespace PrimeFactors.CircleMarkMaskCharacters

open Finset Polynomial CircleMarkJacobiMask CircleMarkSharedScores CircleMarkTargetFrequency
open scoped Classical Topology

/-- The ordinary Jacobi factor vanishes outside the units, regardless of the mask. -/
theorem score_nonunit {n : ℕ} [NeZero n] (C : Finset ℕ) {t : ZMod n}
    (ht : ¬ IsUnit t) : score n C t = 0 := by
  rw [← ZMod.natCast_zmod_val t, ZMod.isUnit_iff_coprime] at ht
  have jac := jacobiSym.eq_zero_iff_not_coprime.mpr
    (show (t.val : ℤ).gcd n ≠ 1 by simpa only [Int.gcd_natCast_natCast] using ht)
  rw [score, jacobiSym.mul_left, jac, zero_mul]

/-- A mask coordinate erases its own square modulo any modulus greater than one. -/
theorem score_at_square {n : ℕ} [NeZero n] (hn : 1 < n) {C : Finset ℕ} {x : ℕ}
    (hx : x ∈ C) : score n C ((x : ZMod n)^2) = 0 := by
  let t := (x : ZMod n)^2
  have root : (((squareMask C).eval (t.val : ℤ) : ℤ) : ZMod n) = 0 := by
    simp only [squareMask, eval_prod, eval_sub, eval_X, eval_C, Int.cast_prod, Int.cast_sub,
      Int.cast_pow, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact Finset.prod_eq_zero hx (sub_self _)
  have dvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp root
  change jacobiSym ((t.val : ℤ) * ((squareMask C).eval (t.val : ℤ))^2) n = 0
  rw [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.mod_left ((squareMask C).eval _) n,
    Int.emod_eq_zero_of_dvd dvd, jacobiSym.zero_left hn]
  simp

/-- A single coprime coordinate supplies a unit on which every Dirichlet
character has nonzero value and the masked score vanishes. -/
theorem not_character {n : ℕ} [NeZero n] (hn : 1 < n) {C : Finset ℕ} {x : ℕ}
    (hx : x ∈ C) (cop : x.Coprime n) (χ : DirichletCharacter ℂ n) :
    ∃ t : ZMod n, IsUnit t ∧ (score n C t : ℂ) ≠ χ t := by
  have u := ((ZMod.isUnit_iff_coprime x n).mpr cop).pow 2
  refine ⟨(x : ZMod n)^2, u, ?_⟩
  rw [score_at_square hn hx, Int.cast_zero]
  exact (u.map χ.toMonoidHom).ne_zero.symm

/-- A nonempty menu of positive coordinates below both primes always has
the required coprime coordinate. -/
theorem safe_not_character {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p ≤ q) {C : Finset ℕ} (nonempty : C.Nonempty)
    (safe : ∀ x ∈ C, 0 < x ∧ x < p) (χ : DirichletCharacter ℂ (p*q)) :
    ∃ t : ZMod (p*q), IsUnit t ∧ (score (p*q) C t : ℂ) ≠ χ t := by
  obtain ⟨x,hx⟩ := nonempty
  obtain ⟨pos,lt⟩ := safe x hx
  have cop {r : ℕ} (hr : r.Prime) (xr : x < r) : x.Coprime r :=
    (hr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos xr)).symm
  exact not_character (hp.out.one_lt.trans_le (Nat.le_mul_of_pos_right p hq.out.pos))
    hx ((cop hp.out lt).mul_right (cop hq.out (lt.trans_le order))) χ

/-- The singleton at one always supplies a unit obstruction. -/
theorem singleton_not_character {n : ℕ} [NeZero n] (hn : 1 < n) (χ : DirichletCharacter ℂ n) :
    ∃ t : ZMod n, IsUnit t ∧ (score n {1} t : ℂ) ≠ χ t :=
  not_character hn (mem_singleton_self 1) (Nat.coprime_one_left n) χ

/-- A complete period of one character gives the totient for the principal
character and zero for every other character. -/
theorem character_sum (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) :
    (∑ t, χ t) = if χ = 1 then (n.totient : ℂ) else 0 := by
  split_ifs with h
  · subst χ
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · exact MulChar.sum_eq_zero_of_ne_one h

/-- An expansion on units suffices since all the summands vanish off units.
Coefficients of characters omitted from a finite combination can be set to zero. -/
theorem principal_coefficient {n : ℕ} [NeZero n] (C : Finset ℕ)
    (a : DirichletCharacter ℂ n → ℂ)
    (repr : ∀ t : ZMod n, IsUnit t → (score n C t : ℂ) = ∑ χ, a χ * χ t) :
    (globalSum n (squareMask C) : ℂ) = (n.totient : ℂ) * a 1 := by
  have all (t : ZMod n) : (score n C t : ℂ) = ∑ χ, a χ * χ t := by
    by_cases h : IsUnit t
    · exact repr t h
    · simp [score_nonunit C h, MulChar.map_nonunit _ h]
  rw [← sum_score, Int.cast_sum]
  simp only [all]
  rw [sum_comm]
  simp only [← mul_sum, character_sum]
  simp [mul_ite, mul_comm]

/-- The finite Fourier coefficient obtained by averaging the score against
the inverse character on the unit group. Nonunits have zero contribution. -/
noncomputable def coefficient (n : ℕ) [NeZero n] (C : Finset ℕ)
    (χ : DirichletCharacter ℂ n) : ℂ :=
  (∑ t : ZMod n, (score n C t : ℂ) * χ t⁻¹) / n.totient

/-- Ordinary character orthogonality gives an exact expansion of the masked
score. Both the coefficient formula and the expansion are finite sums. -/
theorem expansion (n : ℕ) [NeZero n] (C : Finset ℕ) (t : ZMod n) :
    (score n C t : ℂ) = ∑ χ, coefficient n C χ * χ t := by
  have term (x : ZMod n) : (score n C x : ℂ) * (∑ χ : DirichletCharacter ℂ n, χ x⁻¹ * χ t) =
      if x = t then (score n C x : ℂ) * n.totient else 0 := by
    by_cases hu : IsUnit x
    · rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu t, mul_ite, mul_zero]
    · simp [score_nonunit C hu]
  have phi : (n.totient : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n.totient
  simp only [coefficient, div_mul_eq_mul_div, sum_mul, ← sum_div]
  rw [eq_div_iff phi, sum_comm]
  simp only [mul_assoc, ← mul_sum, term]
  simp

/-- The singleton's complete Jacobi sum equals one for two distinct odd primes. -/
theorem singleton_sum {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p ≠ q)
    (op : p ≠ 2) (oq : q ≠ 2) : globalSum (p*q) (squareMask {1}) = 1 := by
  rw [factorization diff, square_sum p op, square_sum q oq]
  simp [covered]

/-- In any character expansion of the singleton score the normalized principal
coefficient is the reciprocal of the size of the unit group. -/
theorem singleton_coefficient {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p ≠ q) (op : p ≠ 2) (oq : q ≠ 2) (a : DirichletCharacter ℂ (p*q) → ℂ)
    (repr : ∀ t : ZMod (p*q), IsUnit t → (score (p*q) {1} t : ℂ) = ∑ χ, a χ * χ t) :
    a 1 = ((p*q).totient : ℂ)⁻¹ := by
  have h := principal_coefficient {1} a repr
  rw [singleton_sum diff op oq, Int.cast_one, mul_comm] at h
  rw [← one_div]
  exact (eq_div_iff (by exact_mod_cast NeZero.ne ((p*q).totient) : ((p*q).totient : ℂ) ≠ 0)).mpr h.symm

/-- Exact knowledge of this coefficient gives the sum of the two primes. -/
theorem singleton_factor_sum {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p ≠ q) (op : p ≠ 2) (oq : q ≠ 2) (a : DirichletCharacter ℂ (p*q) → ℂ)
    (repr : ∀ t : ZMod (p*q), IsUnit t → (score (p*q) {1} t : ℂ) = ∑ χ, a χ * χ t) :
    (p : ℂ) + q = ((p*q : ℕ) : ℂ) + 1 - (a 1)⁻¹ := by
  rw [singleton_coefficient diff op oq a repr, inv_inv, Nat.totient_mul ((Nat.coprime_primes hp.out hq.out).mpr diff),
    Nat.totient_prime hp.out, Nat.totient_prime hq.out]
  push_cast [Nat.cast_sub hp.out.one_le, Nat.cast_sub hq.out.one_le]
  ring

/-- The reconstruction applies to the explicit coefficient defined by finite Fourier inversion. -/
theorem fourier_singleton_factor_sum {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p ≠ q) (op : p ≠ 2) (oq : q ≠ 2) :
    (p : ℂ) + q = ((p*q : ℕ) : ℂ) + 1 - (coefficient (p*q) {1} 1)⁻¹ :=
  singleton_factor_sum diff op oq _ fun t _ => expansion (p*q) {1} t

/-- At one, the residue of the periodic L-function of the masked
score measures the unnormalized complete sum divided by the public modulus. -/
theorem masked_residue (n : ℕ) [NeZero n] (C : Finset ℕ) :
    Filter.Tendsto (fun s : ℂ => (s-1) * ZMod.LFunction (fun t => (score n C t : ℂ)) s)
      (𝓝[≠] 1) (𝓝 ((globalSum n (squareMask C) : ℂ) / n)) := by
  simpa only [← sum_div, ← Int.cast_sum, sum_score] using
    ZMod.LFunction_residue_one (fun t => (score n C t : ℂ))

/-- For the singleton mask the periodic L-function has residue 1/N, while its normalized principal character coefficient is 1/φ(N). -/
theorem singleton_residue {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p ≠ q) (op : p ≠ 2) (oq : q ≠ 2) :
    Filter.Tendsto (fun s : ℂ => (s-1) * ZMod.LFunction (fun t => (score (p*q) {1} t : ℂ)) s)
      (𝓝[≠] 1) (𝓝 (1 / ((p*q : ℕ) : ℂ))) := by
  simpa only [singleton_sum diff op oq, Int.cast_one] using masked_residue (p*q) {1}

end PrimeFactors.CircleMarkMaskCharacters
