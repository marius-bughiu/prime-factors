import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

/-! Linear combinations of neighboring interval reciprocal sums. A zero total
weight cancels every common-interior term. A nonzero weight retains every
common-interior pole, with its full order in a rational formula. -/

namespace PrimeFactors.IntervalReciprocalStencil

open Finset Polynomial

variable {F : Type*} [Field F]

/-- Contribution of slot k to the weighted sum of h+1 translated windows of width w. -/
noncomputable def coefficient (w h : ℕ) (c : ℕ → F) (k : ℕ) : F :=
  ∑ j ∈ range (h+1), if j ≤ k ∧ k < j+w then c j else 0

theorem interior {w h k : ℕ} (c : ℕ → F) (lo : h≤k) (hi : k<w) :
    coefficient w h c k = ∑ j ∈ range (h+1), c j := by
  apply sum_congr rfl
  intro j hj
  simp only [mem_range] at hj
  rw [if_pos (by omega)]

/-- Regrouping applies to arbitrary observations at individual slots, including products'
reciprocal power sums at every order. -/
theorem regroup (w h : ℕ) (c f : ℕ → F) :
    (∑ j ∈ range (h+1), c j * (∑ k ∈ Ico j (j+w), f k)) =
    ∑ k ∈ range (h+w), coefficient w h c k * f k := by
  classical
  symm
  simp only [coefficient,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [mul_sum]
  have eq : (range (h+w)).filter (fun k => j≤k ∧ k<j+w) = Ico j (j+w) := by
    ext k
    have h' := mem_range.mp hj
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [←eq,sum_filter]
  apply sum_congr rfl
  intro k _
  split_ifs <;> simp_all

/-- Every choice of shift coefficients, even chosen after previous readings, is insensitive
to interchanging two common-interior observations. This is an ambiguity of these queries. -/
theorem swap_interior {w h a b : ℕ} (c f : ℕ → F)
    (ha : h≤a ∧ a<w) (hb : h≤b ∧ b<w) :
    (∑ k ∈ range (h+w), coefficient w h c k * f (Equiv.swap a b k)) =
    ∑ k ∈ range (h+w), coefficient w h c k * f k := by
  classical
  let σ := Equiv.swap a b
  have preserves : ∀ k ∈ range (h+w), σ k ∈ range (h+w) := by
    intro k hk
    by_cases ka : k=a
    · subst k; simp only [σ,Equiv.swap_apply_left,mem_range]; omega
    by_cases kb : k=b
    · subst k; simp only [σ,Equiv.swap_apply_right,mem_range]; omega
    simpa only [σ,Equiv.swap_apply_of_ne_of_ne ka kb] using hk
  apply sum_bij' (fun k _ => σ k) (fun k _ => σ k) preserves preserves
    (fun k _ => Equiv.swap_apply_self _ _ _) (fun k _ => Equiv.swap_apply_self _ _ _)
  intro k _
  change _ = coefficient w h c (Equiv.swap a b k) * _
  by_cases ka : k=a
  · subst k
    simp only [Equiv.swap_apply_left,interior c ha.1 ha.2,interior c hb.1 hb.2,σ]
  by_cases kb : k=b
  · subst k
    simp only [Equiv.swap_apply_right,interior c ha.1 ha.2,interior c hb.1 hb.2,σ]
  simp only [σ,Equiv.swap_apply_of_ne_of_ne ka kb]

noncomputable def support (w h : ℕ) (c : ℕ → F) : Finset ℕ := by
  classical exact (range (h+w)).filter (fun k => coefficient w h c k ≠ 0)

theorem zero_sum_support {w h : ℕ} {c : ℕ → F} (zero : ∑ j ∈ range (h+1), c j = 0) :
    support w h c ⊆ range h ∪ Ico w (w+h) := by
  classical
  intro k hk
  obtain ⟨inside,nz⟩ := mem_filter.mp hk
  simp only [mem_range] at inside
  simp only [mem_union,mem_range,mem_Ico]
  by_contra! bad
  have hi : k<w := by omega
  exact nz ((interior c (by omega) hi).trans zero)

theorem nonzero_sum_support {w h : ℕ} {c : ℕ → F} (nonzero : ∑ j ∈ range (h+1), c j ≠ 0) :
    Ico h w ⊆ support w h c := by
  classical
  intro k hk
  obtain ⟨lo,hi⟩ := mem_Ico.mp hk
  exact mem_filter.mpr ⟨mem_range.mpr (by omega),(interior c lo hi) ▸ nonzero⟩

/-- Denominator and cleared numerator for a weighted reciprocal power sum whose distinct
poles are z(i). Only nonzero coefficients belong in s. -/
noncomputable def denominator (s : Finset ℕ) (z : ℕ → F) (m : ℕ) : F[X] :=
  ∏ i ∈ s, (X - C (z i))^m

noncomputable def numerator (s : Finset ℕ) (z c : ℕ → F) (m : ℕ) : F[X] :=
  ∑ i ∈ s, C (c i) * denominator (s.erase i) z m

theorem eval_at_pole {s : Finset ℕ} {z c : ℕ → F} {m i : ℕ} (hi : i∈s) (pos : 0<m)
    (inj : Set.InjOn z (s: Set ℕ)) (nz : c i≠0) : (numerator s z c m).eval (z i)≠0 := by
  classical
  rw [numerator,eval_finset_sum,sum_eq_single i]
  · simp only [eval_mul,eval_C,denominator,eval_prod,eval_pow,eval_sub,eval_X]
    apply mul_ne_zero nz
    apply prod_ne_zero_iff.mpr
    intro j hj
    obtain ⟨ne,mem⟩ := mem_erase.mp hj
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun e => ne (inj mem hi e.symm)))
  · intro j hj ne
    simp only [eval_mul,denominator,eval_prod,eval_pow,eval_sub,eval_X,eval_C]
    have zi : (∏ k ∈ s.erase j, (z i-z k)^m)=0 :=
      prod_eq_zero (mem_erase.mpr ⟨ne.symm,hi⟩) (by simp [pos.ne'])
    rw [zi,mul_zero]
  · exact fun missing => False.elim (missing hi)

/-- Off the poles, the cleared numerator represents the sum of reciprocal powers. -/
theorem represents {s : Finset ℕ} {z c : ℕ → F} (m : ℕ) (x : F)
    (off : ∀ i∈s, x≠z i) :
    (numerator s z c m).eval x =
      (denominator s z m).eval x * ∑ i∈s, c i/(x-z i)^m := by
  classical
  rw [numerator,eval_finset_sum,mul_sum]
  apply sum_congr rfl
  intro i hi
  have nz := pow_ne_zero m (sub_ne_zero.mpr (off i hi))
  have split : denominator s z m = (X-C (z i))^m * denominator (s.erase i) z m :=
    (mul_prod_erase s _ hi).symm
  rw [split,eval_mul,eval_C,eval_mul,eval_pow,eval_sub,eval_X,eval_C]
  rw [div_eq_mul_inv,show (x-z i)^m * (denominator (s.erase i) z m).eval x *
      (c i*((x-z i)^m)⁻¹) = c i*(denominator (s.erase i) z m).eval x *
      ((x-z i)^m*((x-z i)^m)⁻¹) by ac_rfl,mul_inv_cancel₀ nz,mul_one]

/-- The reduced denominator retains the full order m at every nonzero pole. A purported
rational replacement A/B obeying the identity must include all those factors in B. -/
theorem denominator_dvd {s : Finset ℕ} {z c : ℕ → F} {m : ℕ} (pos : 0<m)
    (inj : Set.InjOn z (s: Set ℕ)) (nz : ∀ i ∈ s, c i≠0)
    {A B : F[X]} (eq : numerator s z c m * B = A * denominator s z m) :
    denominator s z m ∣ B := by
  classical
  have cop : IsCoprime (denominator s z m) (numerator s z c m) := by
    apply IsCoprime.prod_left
    intro i hi
    apply IsCoprime.pow_left
    apply (irreducible_X_sub_C (z i)).coprime_iff_not_dvd.mpr
    exact fun div => eval_at_pole hi pos inj (nz i hi) (dvd_iff_isRoot.mp div)
  exact cop.dvd_of_dvd_mul_left (eq ▸ dvd_mul_left ..)

/-- If the stencil total is nonzero, every rational formula has denominator degree
at least m*(w-h) on non-wrapping, distinct poles. -/
theorem interior_degree {w h m : ℕ} {c z : ℕ → F} (pos : 0<m)
    (nonzero : ∑ j ∈ range (h+1), c j ≠ 0) (inj : Set.InjOn z (support w h c : Set ℕ))
    {A B : F[X]} (bnz : B≠0) (eq : numerator (support w h c) z (coefficient w h c) m * B =
      A * denominator (support w h c) z m) : m*(w-h)≤B.natDegree := by
  classical
  have hcard := card_le_card (nonzero_sum_support (w:=w) nonzero)
  rw [Nat.card_Ico] at hcard
  have d := denominator_dvd pos inj (fun _ hi => (mem_filter.mp hi).2) eq
  have deg := natDegree_le_of_dvd d bnz
  rw [denominator,natDegree_prod_of_monic _ _ (fun i _ => (monic_X_sub_C (z i)).pow m)] at deg
  simp only [natDegree_pow,natDegree_X_sub_C,Nat.mul_one,sum_const,nsmul_eq_mul] at deg
  exact (Nat.mul_le_mul_left m hcard).trans (by simpa [Nat.mul_comm] using deg)

/-- Every raw product factors through a single common product and two edges.
This does not divide by that common product, so it is valid at every precision,
even when the common product vanishes modulo a composite. -/
theorem common_product {M : Type*} [CommMonoid M] (f : ℕ → M) {w h j : ℕ}
    (slide : j≤h) (overlap : h≤w) :
    (∏ k∈Ico j (j+w), f k) =
    (∏ k∈Ico h w, f k)*((∏ k∈Ico j h, f k)*(∏ k∈Ico w (j+w), f k)) := by
  rw [←prod_Ico_consecutive f slide (show h≤j+w by omega),
    ←prod_Ico_consecutive f overlap (show w≤j+w by omega)]
  ac_rfl

/-- Evaluation of the first-difference rational formula at a composite modulus needs
only the endpoints to be units. The numerator is exactly minus the window width. -/
theorem first_difference {R : Type*} [CommRing R] {x w a b : R}
    (left : a*x=1) (right : b*(x+w)=1) : (b-a)*(x*(x+w)) = -w := by
  calc
    _ = x*(b*(x+w))-(x+w)*(a*x) := by ring
    _ = -w := by rw [left,right]; ring

theorem first_difference_unit {R : Type*} [CommRing R] {x w a b : R}
    (left : a*x=1) (right : b*(x+w)=1) (unit : IsUnit w) : IsUnit (b-a) := by
  have h := first_difference left right
  have units : IsUnit ((b-a)*(x*(x+w))) := h ▸ unit.neg
  exact ((Commute.all _ _).isUnit_mul_iff.mp units).1

/-- Three translates for N=143. The width-five difference has coprime endpoints and
unit numerator regardless of how many primes of the input lie in the common interior. -/
theorem actual_windows_143 :
    let inside := fun x : ℕ => ((List.range' (x+1) 4).filter (fun d => 143%d=0))
    inside 15 = [] ∧ inside 7 = [11] ∧ inside 9 = [11,13] ∧
    (∀ x ∈ [15,7,9], Nat.Coprime (x*(x+5)) 143) ∧ Nat.Coprime 5 143 := by
  decide

end PrimeFactors.IntervalReciprocalStencil
