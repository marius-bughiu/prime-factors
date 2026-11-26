import PrimeFactors.WeightedTripleSupport
import Mathlib.Data.Int.ModEq

/-! Square relations for weighted rows on both sides of their endpoints.
The signed root convention includes either choice of gcd sign. -/

namespace PrimeFactors.WeightedSignedSupport
open Finset

private theorem gcd_of_modEq {x y n : ℤ} (same : x ≡ y [ZMOD n]) :
    Int.gcd x n = Int.gcd y n := by
  have divides (a b : ℤ) (h : a ≡ b [ZMOD n]) : Int.gcd a n ∣ Int.gcd b n := by
    apply Int.natCast_dvd_natCast.mp
    apply Int.dvd_coe_gcd _ Int.gcd_dvd_right
    have delta := (Int.gcd_dvd_right (a:=a) (b:=n)).trans h.dvd
    simpa only [sub_add_cancel] using dvd_add delta (Int.gcd_dvd_left (a:=a) (b:=n))
  exact Nat.dvd_antisymm (divides x y same) (divides y x same.symm)

/-- Proportional nonzero remainders have an integer square root of their
product agreeing globally with the product of their labels. The root may be negative. -/
theorem pair_root {A B r s n : ℕ} {d e : ℤ}
    (first : (A:ℤ)^2 = d+4*r*n) (second : (B:ℤ)^2 = e+4*s*n)
    (ap : 0<A) (bp : 0<B) (nz : d≠0) (unit : A.Coprime n) (same : s*A^2=r*B^2) :
    ∃ w : ℤ, w≠0 ∧ w^2=d*e ∧ w ≡ (A:ℤ)*B [ZMOD (n:ℤ)] := by
  have eq : (s:ℤ)*A^2=(r:ℤ)*B^2 := by exact_mod_cast same
  have cross : (B:ℤ)^2*d=(A:ℤ)^2*e := by
    linear_combination (A:ℤ)^2*second-(B:ℤ)^2*first+4*(n:ℤ)*eq
  have sq : ((B:ℤ)*d)^2=(A:ℤ)^2*(d*e) := by
    linear_combination d*cross
  obtain ⟨w, hw⟩ := (Int.pow_dvd_pow_iff (by decide : 2≠0)).mp
    (show (A:ℤ)^2 ∣ ((B:ℤ)*d)^2 from ⟨d*e,sq⟩)
  have an : (A:ℤ)≠0 := by exact_mod_cast ap.ne'
  have bn : (B:ℤ)≠0 := by exact_mod_cast bp.ne'
  refine ⟨w, fun zero => mul_ne_zero bn nz (by rw [hw, zero, mul_zero]), ?_, ?_⟩
  · rw [hw, mul_pow] at sq
    exact mul_left_cancel₀ (pow_ne_zero 2 an) sq
  · apply Int.modEq_iff_dvd.mpr
    apply unit.symm.isCoprime.dvd_of_dvd_mul_left
    refine ⟨4*(r:ℤ)*B, ?_⟩
    linear_combination (B:ℤ)*first + hw

/-- After removing a proportional pair, some signed integer root returns
exactly the same gcd. The remaining product and root may have either sign
before their square relation is imposed. -/
theorem remove_pair {A B r s n : ℕ} {d e P F z : ℤ}
    (first : (A:ℤ)^2=d+4*r*n) (second : (B:ℤ)^2=e+4*s*n)
    (ap : 0<A) (bp : 0<B) (nz : d≠0) (au : A.Coprime n) (bu : B.Coprime n)
    (same : s*A^2=r*B^2) (sq : d*e*F=z^2) :
    ∃ u : ℤ, F=u^2 ∧ Int.gcd ((A:ℤ)*B*P-z) n = Int.gcd (P-u) n := by
  obtain ⟨w, wn, ws, congr⟩ := pair_root first second ap bp nz au same
  obtain ⟨u, zu⟩ := (Int.pow_dvd_pow_iff (by decide : 2≠0)).mp
    (show w^2∣z^2 from ⟨F, by rw [ws, sq]⟩)
  refine ⟨u, ?_, ?_⟩
  · rw [← ws, zu, mul_pow] at sq
    exact mul_left_cancel₀ (pow_ne_zero 2 wn) sq
  · rw [zu]
    have eqMod := (Int.ModEq.refl ((A:ℤ)*B*P)).sub (congr.mul_right u)
    rw [← mul_sub] at eqMod
    rw [gcd_of_modEq eqMod]
    simp only [Int.gcd_eq_natAbs, Int.natAbs_mul, Int.natAbs_ofNat]
    exact Nat.Coprime.gcd_mul_left_cancel _ (au.symm.mul_right bu.symm).symm

/-- Allow a signed square root, so that a match records either actual gcd. -/
def Matches {ι : Type*} (S : Finset ι) (A : ι → ℕ) (D : ι → ℤ) (n g : ℕ) : Prop :=
  ∃ z : ℤ, (∏ i ∈ S, D i) = z^2 ∧ Int.gcd ((∏ i ∈ S, (A i:ℤ))-z) n = g

private theorem erase_two {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℤ)
    {i j : ι} (hi : i∈S) (hj : j∈S) (ne : i≠j) :
    (∏ k ∈ S, f k) = f i*f j*(∏ k ∈ (S.erase i).erase j, f k) := by
  rw [← S.mul_prod_erase f hi,
    ← (S.erase i).mul_prod_erase f (mem_erase_of_ne_of_mem ne.symm hj), mul_assoc]

/-- A proper gcd survives both pair cancellation and the exclusion of the
empty set, for any odd modulus. -/
theorem reduced_subset {ι : Type*} (S : Finset ι) (A r : ι → ℕ) (D : ι → ℤ)
    {n g : ℕ} (odd : Odd n) (proper : 1<g ∧ g<n)
    (rows : ∀ i∈S, (A i:ℤ)^2 = D i+4*(r i:ℤ)*n) (ap : ∀ i∈S, 0<A i)
    (nz : ∀ i∈S, D i≠0) (units : ∀ i∈S, (A i).Coprime n)
    (hit : Matches S A D n g) :
    ∃ T ⊆ S, T.Nonempty ∧ Matches T A D n g ∧
      (∀ i∈T, ∀ j∈T, i≠j → r j*(A i)^2 ≠ r i*(A j)^2) := by
  classical
  let pool := S.powerset.filter (fun T => Matches T A D n g)
  have whole : S∈pool := mem_filter.mpr ⟨mem_powerset.mpr (by rfl), hit⟩
  obtain ⟨T, hT, minimal⟩ := pool.exists_min_image Finset.card ⟨S, whole⟩
  obtain ⟨sub, matched⟩ := mem_filter.mp hT
  have hsub := mem_powerset.mp sub
  refine ⟨T, hsub, ?_, matched, ?_⟩
  · by_contra! empty
    rw [Finset.not_nonempty_iff_eq_empty.mp empty] at matched
    obtain ⟨z, sq, hg⟩ := matched
    simp only [prod_empty] at sq hg
    rcases sq_eq_one_iff.mp sq.symm with one | minus
    · simp [one] at hg
      omega
    · rw [minus] at hg
      change Nat.gcd 2 n = g at hg
      rw [(Nat.coprime_two_left.mpr odd).gcd_eq_one] at hg
      omega
  · intro i hi j hj ne same
    let U := (T.erase i).erase j
    have uSub : U ⊆ S := (erase_subset j _).trans ((erase_subset i _).trans hsub)
    obtain ⟨z, sq, hg⟩ := matched
    rw [erase_two T D hi hj ne] at sq
    rw [erase_two T (fun k => (A k:ℤ)) hi hj ne] at hg
    obtain ⟨u, us, ug⟩ := remove_pair (rows i (hsub hi)) (rows j (hsub hj))
      (ap i (hsub hi)) (ap j (hsub hj)) (nz i (hsub hi))
      (units i (hsub hi)) (units j (hsub hj)) same sq
    have good : U∈pool := mem_filter.mpr ⟨mem_powerset.mpr uSub, u, us, ug.symm.trans hg⟩
    have smaller : U.card<T.card := card_erase_le.trans_lt (card_erase_lt_of_mem hi)
    exact (not_le_of_gt smaller) (minimal U good)

/-- Zero determinants, including proportional catalogue rows not in the
reduced relation, contribute the neutral factor one. -/
noncomputable def modulus {ι : Type*} [DecidableEq ι] (C : Finset ι) (A r : ι → ℕ) (i : ι) : ℕ :=
  ∏ j ∈ C.erase i, max 1 (WeightedTripleSupport.cross (A i) (r i) (A j) (r j))

theorem modulus_pos {ι : Type*} [DecidableEq ι] (C : Finset ι) (A r : ι → ℕ) (i : ι) :
    0 < modulus C A r i := Finset.prod_pos (fun _ _ => lt_of_lt_of_le (by decide : 0<1) (le_max_left ..))

private theorem natAbs_prod {ι : Type*} (T : Finset ι) (D : ι → ℤ) :
    (∏ j ∈ T, D j).natAbs = ∏ j ∈ T, (D j).natAbs := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih => simp only [prod_insert hi, Int.natAbs_mul, ih]

private theorem common_dvd {p A B r s n : ℕ} {d e : ℤ}
    (first : (A:ℤ)^2 = d+4*r*n) (second : (B:ℤ)^2 = e+4*s*n)
    (pd : p∣d.natAbs) (pe : p∣e.natAbs) : p ∣ WeightedTripleSupport.cross A r B s := by
  have di : (p:ℤ) ∣ d := Int.natAbs_dvd_natAbs.mp (by simpa using pd)
  have ei : (p:ℤ) ∣ e := Int.natAbs_dvd_natAbs.mp (by simpa using pe)
  have elim : (s:ℤ)*A^2-(r:ℤ)*B^2=s*d-r*e := by rw [first, second]; ring
  unfold WeightedTripleSupport.cross
  rw [elim]
  exact Int.natAbs_dvd_natAbs.mpr
    (dvd_sub (dvd_mul_of_dvd_right di (s:ℤ)) (dvd_mul_of_dvd_right ei (r:ℤ)))

/-- For every anchor retained in a reduced square relation, its absolute
remainder is a positive square times a squarefree divisor of a fixed catalogue
modulus. No assumptions are made about unused catalogue rows. -/
theorem anchor {ι : Type*} [DecidableEq ι] {C T : Finset ι} {A r : ι → ℕ} {D : ι → ℤ}
    {n : ℕ} {z : ℤ} (sub : T ⊆ C)
    (rows : ∀ j∈T, (A j:ℤ)^2 = D j+4*(r j:ℤ)*n) (nz : ∀ j∈T, D j≠0)
    (distinct : ∀ i∈T, ∀ j∈T, i≠j → r j*(A i)^2 ≠ r i*(A j)^2)
    (square : (∏ j ∈ T, D j) = z^2) {i : ι} (hi : i∈T) :
    ∃ m u : ℕ, Squarefree m ∧ 0<u ∧ (D i).natAbs=m*u^2 ∧ m∣modulus C A r i := by
  have rem : 0 < ∏ j ∈ T.erase i, (D j).natAbs :=
    prod_pos (fun j hj => Int.natAbs_pos.mpr (nz j (mem_of_mem_erase hj)))
  have joint : (D i).natAbs*(∏ j ∈ T.erase i, (D j).natAbs) = z.natAbs^2 := by
    rw [T.mul_prod_erase (fun j => (D j).natAbs) hi, ← natAbs_prod, square, Int.natAbs_pow]
  have supports (p : ℕ) (prime : p.Prime) (pd : p ∣ (D i).natAbs)
      (pr : p ∣ ∏ j ∈ T.erase i, (D j).natAbs) : p ∣ modulus C A r i := by
    obtain ⟨j, hj, dj⟩ := (prime.prime.dvd_finset_prod_iff _).mp pr
    have ne := ne_of_mem_erase hj
    have det : WeightedTripleSupport.cross (A i) (r i) (A j) (r j) ≠ 0 := by
      intro zero
      have eq := sub_eq_zero.mp (Int.natAbs_eq_zero.mp zero)
      exact distinct i hi j (mem_of_mem_erase hj) ne.symm (by exact_mod_cast eq)
    have term := common_dvd (rows i hi) (rows j (mem_of_mem_erase hj)) pd dj
    apply Dvd.dvd.trans _ (Finset.dvd_prod_of_mem
      (fun j => max 1 (WeightedTripleSupport.cross (A i) (r i) (A j) (r j)))
      (mem_erase.mpr ⟨ne, sub (mem_of_mem_erase hj)⟩))
    have bound : 1 ≤ WeightedTripleSupport.cross (A i) (r i) (A j) (r j) := Nat.pos_of_ne_zero det
    simpa only [max_eq_right bound] using term
  have positive := Int.natAbs_pos.mpr (nz i hi)
  obtain ⟨m, u, _, sf, eq, _, div⟩ := WeightedTripleSupport.supported_kernel positive rem joint supports
  refine ⟨m, u, sf, ?_, eq, div⟩
  apply Nat.pos_of_ne_zero
  rintro rfl
  exact positive.ne' (by simpa using eq)

/-- From any proper factor obtained on any chosen subset of a fixed catalogue,
some nonempty reduced subset returns that very factor. Each retained anchor
has a squarefree part supported by the same complete catalogue. -/
theorem supported_subset {ι : Type*} [DecidableEq ι] {C S : Finset ι} {A r : ι → ℕ}
    {D : ι → ℤ} {n g : ℕ} (catalogue : S ⊆ C) (odd : Odd n) (proper : 1<g ∧ g<n)
    (rows : ∀ i∈S, (A i:ℤ)^2 = D i+4*(r i:ℤ)*n) (ap : ∀ i∈S, 0<A i)
    (nz : ∀ i∈S, D i≠0) (units : ∀ i∈S, (A i).Coprime n)
    (hit : Matches S A D n g) :
    ∃ T ⊆ S, T.Nonempty ∧ Matches T A D n g ∧
      (∀ i∈T, ∀ j∈T, i≠j → r j*(A i)^2 ≠ r i*(A j)^2) ∧
      ∀ i∈T, ∃ m u : ℕ, Squarefree m ∧ 0<u ∧ (D i).natAbs=m*u^2 ∧ m∣modulus C A r i := by
  obtain ⟨T, sub, ne, matched, pairwise⟩ := reduced_subset S A r D odd proper rows ap nz units hit
  refine ⟨T, sub, ne, matched, pairwise, ?_⟩
  obtain ⟨z, sq, _⟩ := matched
  exact fun _ hi => anchor (sub.trans catalogue) (fun j hj => rows j (sub hj))
    (fun j hj => nz j (sub hj)) pairwise sq hi

end PrimeFactors.WeightedSignedSupport
