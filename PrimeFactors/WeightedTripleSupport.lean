import PrimeFactors.AffineExcessSingle
import PrimeFactors.SignatureCount
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Polynomial.RingDivision

/-! A square product on two sides of a partition has the same squarefree
part on each side. For weighted remainders, its primes can occur only in
the determinants between the two sides. -/

namespace PrimeFactors.WeightedTripleSupport

/-- The public elimination constant for two weighted rows. -/
def cross (A r B s : ℕ) : ℕ :=
  ((s : ℤ) * (A : ℤ)^2 - (r : ℤ) * (B : ℤ)^2).natAbs

/-- Elimination cancels the common input even when a weight shares a
factor with the divisor. -/
theorem common_divides_cross {p D E A B r s N : ℕ}
    (left : A^2 = D + 4*r*N) (right : B^2 = E + 4*s*N)
    (pd : p ∣ D) (pe : p ∣ E) : p ∣ cross A r B s := by
  have l : (A : ℤ)^2 = D + 4*(r : ℤ)*N := by exact_mod_cast left
  have h : (B : ℤ)^2 = E + 4*(s : ℤ)*N := by exact_mod_cast right
  have e : (s : ℤ)*(A : ℤ)^2 - (r : ℤ)*(B : ℤ)^2 = s*(D : ℤ)-r*(E : ℤ) := by
    rw [l, h]; ring
  have d₁ : (p : ℤ) ∣ (D : ℤ) := by exact_mod_cast pd
  have d₂ : (p : ℤ) ∣ (E : ℤ) := by exact_mod_cast pe
  unfold cross
  rw [e]
  simpa only [Int.natAbs_ofNat] using Int.natAbs_dvd_natAbs.mpr
    (dvd_sub (dvd_mul_of_dvd_right d₁ (s : ℤ)) (dvd_mul_of_dvd_right d₂ (r : ℤ)))

/-- A common squarefree part divides any number containing each prime
common to the two positive inputs. -/
theorem supported_kernel {x y z C : ℕ} (xp : 0 < x) (yp : 0 < y)
    (square : x*y = z^2) (support : ∀ p : ℕ, p.Prime → p ∣ x → p ∣ y → p ∣ C) :
    ∃ m u v : ℕ, Squarefree m ∧ x = m*u^2 ∧ y = m*v^2 ∧ m ∣ C := by
  obtain ⟨m, u, _, up, hu, hm⟩ := Nat.sq_mul_squarefree_of_pos xp
  obtain ⟨n, v, _, vp, hv, hn⟩ := Nat.sq_mul_squarefree_of_pos yp
  have eqn : z^2 = (u*v)^2 * (m*n) := by rw [← square, ← hu, ← hv]; ring
  obtain ⟨w, _, hw⟩ := AffineExcessSingle.remove_square (Nat.mul_pos up vp) eqn
  obtain rfl := eq_of_squarefree_product_square hm hn (show IsSquare (m*n) from
    ⟨w, by simpa only [pow_two] using hw.symm⟩)
  have xeq : x = m*u^2 := by rw [← hu, mul_comm]
  have yeq : y = m*v^2 := by rw [← hv, mul_comm]
  refine ⟨m, u, v, hm, xeq, yeq, ?_⟩
  rw [← Nat.prod_primeFactors_of_squarefree hm]
  apply Finset.prod_primes_dvd
  · exact fun p hp => (Nat.prime_of_mem_primeFactors hp).prime
  · intro p hp
    have pm := Nat.dvd_of_mem_primeFactors hp
    apply support p (Nat.prime_of_mem_primeFactors hp)
    · rw [xeq]; exact dvd_mul_of_dvd_left pm _
    · rw [yeq]; exact dvd_mul_of_dvd_left pm _

/-- For three positive weighted remainders, the possible squarefree parts
of the single row and the opposing pair divide the lcm of the two cross
constants. A finite divisor list is obtained when both constants are nonzero. -/
theorem triple {A₁ A₂ A₃ r₁ r₂ r₃ D₁ D₂ D₃ N z : ℕ}
    (row₁ : A₁^2 = D₁ + 4*r₁*N) (row₂ : A₂^2 = D₂ + 4*r₂*N)
    (row₃ : A₃^2 = D₃ + 4*r₃*N)
    (h₁ : 0 < D₁) (h₂ : 0 < D₂) (h₃ : 0 < D₃) (square : D₁*D₂*D₃ = z^2) :
    ∃ m u v : ℕ, Squarefree m ∧ D₁*D₂ = m*u^2 ∧ D₃ = m*v^2 ∧
      m ∣ Nat.lcm (cross A₁ r₁ A₃ r₃) (cross A₂ r₂ A₃ r₃) := by
  apply supported_kernel (Nat.mul_pos h₁ h₂) h₃ square
  intro p hp left right
  obtain first | second := hp.dvd_mul.mp left
  · exact (common_divides_cross row₁ row₃ first right).trans (Nat.dvd_lcm_left ..)
  · exact (common_divides_cross row₂ row₃ second right).trans (Nat.dvd_lcm_right ..)

/-- With nonzero cross constants, testing the finite lcm divisor list is
equivalent to testing whether the triple product is a square. -/
theorem triple_iff {A₁ A₂ A₃ r₁ r₂ r₃ D₁ D₂ D₃ N : ℕ}
    (row₁ : A₁^2 = D₁ + 4*r₁*N) (row₂ : A₂^2 = D₂ + 4*r₂*N)
    (row₃ : A₃^2 = D₃ + 4*r₃*N)
    (h₁ : 0 < D₁) (h₂ : 0 < D₂) (h₃ : 0 < D₃)
    (c₁ : cross A₁ r₁ A₃ r₃ ≠ 0) (c₂ : cross A₂ r₂ A₃ r₃ ≠ 0) :
    (∃ z : ℕ, D₁*D₂*D₃ = z^2) ↔
      ∃ m ∈ (Nat.lcm (cross A₁ r₁ A₃ r₃) (cross A₂ r₂ A₃ r₃)).divisors,
        Squarefree m ∧ ∃ u v : ℕ, D₁*D₂ = m*u^2 ∧ D₃ = m*v^2 := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨m, u, v, sf, hu, hv, div⟩ := triple row₁ row₂ row₃ h₁ h₂ h₃ hz
    exact ⟨m, Nat.mem_divisors.mpr ⟨div, Nat.lcm_ne_zero c₁ c₂⟩, sf, u, v, hu, hv⟩
  · rintro ⟨m, _, _, u, v, hu, hv⟩
    exact ⟨m*u*v, by rw [hu, hv]; ring⟩

/-- The same support constraint works across any finite cut of a collection
of weighted rows on the same input. Repeated values can be given distinct indices. -/
theorem finite_cut {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (A r D : ι → ℕ) (B s E : κ → ℕ) {N z : ℕ}
    (left : ∀ i ∈ I, (A i)^2 = D i + 4*r i*N)
    (right : ∀ j ∈ J, (B j)^2 = E j + 4*s j*N)
    (lp : ∀ i ∈ I, 0 < D i) (rp : ∀ j ∈ J, 0 < E j)
    (square : (∏ i ∈ I, D i) * (∏ j ∈ J, E j) = z^2) :
    ∃ m u v : ℕ, Squarefree m ∧ (∏ i ∈ I, D i) = m*u^2 ∧ (∏ j ∈ J, E j) = m*v^2 ∧
      m ∣ I.lcm (fun i => J.lcm (fun j => cross (A i) (r i) (B j) (s j))) := by
  apply supported_kernel (Finset.prod_pos lp) (Finset.prod_pos rp) square
  intro p hp pd pe
  obtain ⟨i, hi, di⟩ := (hp.prime.dvd_finset_prod_iff D).mp pd
  obtain ⟨j, hj, ej⟩ := (hp.prime.dvd_finset_prod_iff E).mp pe
  exact (common_divides_cross (left i hi) (right j hj) di ej).trans
    ((Finset.dvd_lcm (f := fun j => cross (A i) (r i) (B j) (s j)) hj).trans
      (Finset.dvd_lcm (f := fun i => J.lcm (fun j => cross (A i) (r i) (B j) (s j))) hi))

private theorem difference_dvd {R ι : Type*} [CommRing R] (I : Finset ι)
    (F : R) (A r : ι → R) :
    F ∣ (∏ i ∈ I, A i)^2 - ∏ i ∈ I, ((A i)^2 - 4*r i*F) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_pow]
    obtain ⟨t, ht⟩ := ih
    refine ⟨(A i)^2*t + 4*r i*(∏ j ∈ I, ((A j)^2 - 4*r j*F)), ?_⟩
    linear_combination (A i)^2 * ht

/-- If a family forces a square identically, each prime component of the
input expression already divides one of the signed differences in the
coefficient ring. The statement applies before substituting any public input. -/
theorem component_sign {R ι : Type*} [CommRing R] (I : Finset ι) (A r : ι → R)
    {F P Z : R} (prime : Prime P) (component : P ∣ F)
    (identity : (∏ i ∈ I, ((A i)^2 - 4*r i*F)) = Z^2) :
    P ∣ (∏ i ∈ I, A i) + Z ∨ P ∣ (∏ i ∈ I, A i) - Z := by
  have div := component.trans (difference_dvd I F A r)
  rw [identity, sq_sub_sq] at div
  exact prime.dvd_or_dvd div

/-- For polynomial labels, weights and a polynomial square root, one fixed
sign works for every specialization of the input variable. The coefficient
ring can contain further independent polynomial parameters. -/
theorem polynomial_forced_sign {R ι : Type*} [CommRing R] [IsDomain R]
    (I : Finset ι) (A r : ι → Polynomial R) {Z : Polynomial R}
    (identity : (∏ i ∈ I, ((A i)^2 - 4*r i*Polynomial.X)) = Z^2) :
    (∀ n : R, n ∣ (∏ i ∈ I, (A i).eval n) + Z.eval n) ∨
    (∀ n : R, n ∣ (∏ i ∈ I, (A i).eval n) - Z.eval n) := by
  obtain pos | neg := component_sign I A r Polynomial.prime_X dvd_rfl identity
  · left; intro n; simpa [Polynomial.eval_prod] using (Polynomial.evalRingHom n).map_dvd pos
  · right; intro n; simpa [Polynomial.eval_prod] using (Polynomial.evalRingHom n).map_dvd neg

end PrimeFactors.WeightedTripleSupport
