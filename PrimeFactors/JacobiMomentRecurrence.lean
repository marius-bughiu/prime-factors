import PrimeFactors.HasseRecurrenceDegree
import PrimeFactors.ProjectiveWordMoments
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots

/-!
# Fixed recurrences for complete Jacobi moments

A scalar recurrence acts by a polynomial in the forward shift. The CRT
components of the positive moments have one nonzero exponential term per
active residue. A separate diagonal-moment argument handles the shorter prefix
before the first disagreement with the central binomial coefficients.
-/

namespace PrimeFactors.JacobiMomentRecurrence

open Finset Polynomial

variable {F : Type*} [Field F]

/-- Apply a polynomial in the one-place forward shift. -/
noncomputable def shift {R : Type*} [CommRing R] (P : R[X]) (u : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ P.support, P.coeff j * u (n + j)

/-- A finite sum of powers, each multiplied by its field-valued weight. -/
noncomputable def signal (S : Finset F) (w : F → F) (n : ℕ) : F := ∑ x ∈ S, w x*x^n

theorem shift_signal (P : F[X]) (S : Finset F) (w : F → F) (n : ℕ) :
    shift P (signal S w) n = ∑ x ∈ S, (w x*P.eval x)*x^n := by
  unfold shift signal
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, mul_sum, sum_mul]
  apply sum_congr rfl
  intro j _
  rw [pow_add]
  ring

/-- A block of as many recurrence equations as there are bases forces every
active base to be a root. The initial offset is arbitrary for nonzero bases. -/
theorem annihilator_iff (P : F[X]) (S : Finset F) (w : F → F) (start : ℕ)
    (weights : ∀ x ∈ S, w x≠0) (bases : ∀ x ∈ S, x≠0) :
    (∀ i : Fin S.card, shift P (signal S w) (start+i)=0) ↔ ∀ x ∈ S, P.eval x=0 := by
  classical
  constructor
  · intro hits
    let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe _)
    let v (j : Fin S.card) : F := e.symm j
    let z (j : Fin S.card) := w (v j)*P.eval (v j)*(v j)^start
    have independent : Function.Injective v := Subtype.val_injective.comp e.symm.injective
    have relation (i : Fin S.card) : (∑ j, z j * (v j)^(i:ℕ))=0 := by
      have h := hits i
      rw [shift_signal] at h
      simp_rw [pow_add, ← mul_assoc] at h
      have reindex := Equiv.sum_comp e.symm (fun x : S => (w (x:F)*P.eval (x:F)*(x:F)^start)*(x:F)^(i:ℕ))
      change _ = ∑ x : S, (w (x:F)*P.eval (x:F)*(x:F)^start)*(x:F)^(i:ℕ) at reindex
      rw [show (∑ j, z j*(v j)^(i:ℕ)) = _ from reindex]
      rw [Finset.univ_eq_attach S, sum_attach S (fun x : F => w x*P.eval x*x^start*x^(i:ℕ))]
      exact h
    have zero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero independent relation
    intro x hx
    have zx := congrFun zero (e ⟨x,hx⟩)
    have vxe : v (e ⟨x,hx⟩) = x := by simp [v]
    change w (v (e ⟨x,hx⟩))*P.eval (v (e ⟨x,hx⟩))*(v (e ⟨x,hx⟩))^start=0 at zx
    rw [vxe] at zx
    exact (mul_eq_zero.mp ((mul_eq_zero.mp zx).resolve_right (pow_ne_zero _ (bases _ hx)))).resolve_left
      (weights _ hx)
  · intro roots i
    rw [shift_signal]
    exact sum_eq_zero fun x hx => by simp [roots x hx]

theorem lower (P : F[X]) (non : P≠0) (S : Finset F) (w : F → F) (start : ℕ)
    (weights : ∀ x ∈ S, w x≠0) (bases : ∀ x ∈ S, x≠0)
    (fit : ∀ i : Fin S.card, shift P (signal S w) (start+i)=0) :
    S.card ≤ P.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  exact (Polynomial.mem_roots non).mpr ((annihilator_iff P S w start weights bases).mp fit x hx)

/-- An annihilator of exactly this degree works on the entire sequence. -/
theorem sharp (S : Finset F) (w : F → F) :
    ∃ P : F[X], P.Monic ∧ P.natDegree=S.card ∧ ∀ n, shift P (signal S w) n=0 := by
  let P : F[X] := ∏ x ∈ S, (X-C x)
  refine ⟨P, monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x), ?_, ?_⟩
  · exact natDegree_finset_prod_X_sub_C_eq_card _ _
  · intro n
    rw [shift_signal]
    apply sum_eq_zero
    intro x hx
    have root : P.eval x=0 := by
      simp only [P,eval_prod,eval_sub,eval_X,eval_C]
      exact prod_eq_zero hx (sub_self x)
    simp [root]

/-- The nonzero trace parameters with nonvanishing signed weight. -/
noncomputable def active (p : ℕ) [Fact p.Prime] : Finset (ZMod p) := univ \ {0,2,-2}

/-- Even degrees identify the two trace parameters with the same square. -/
noncomputable def evenBases (p : ℕ) [Fact p.Prime] : Finset (ZMod p) := (active p).image (·^2)

noncomputable def weight {p : ℕ} [Fact p.Prime] (z : ZMod p) : ZMod p :=
  -((quadraticChar (ZMod p) (z-4) : ℤ) : ZMod p)

/-- One prime-field projection of the composite moment. -/
noncomputable def component (p : ℕ) [Fact p.Prime] (n : ℕ) : ZMod p :=
  -(∑ t : ZMod p, t^n*((quadraticChar (ZMod p) (t^2-4) : ℤ) : ZMod p))

private theorem two_nonzero {p : ℕ} [Fact p.Prime] (odd : p≠2) : (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])

private theorem pair_distinct {p : ℕ} [Fact p.Prime] (odd : p≠2) {t : ZMod p} (t0 : t≠0) :
    t≠-t := by
  intro h
  apply mul_ne_zero (two_nonzero odd) t0
  linear_combination h

theorem active_card {p : ℕ} [Fact p.Prime] (odd : p≠2) : (active p).card = p-3 := by
  have two := two_nonzero odd
  have diff := pair_distinct odd two
  rw [active, card_sdiff (subset_univ _),card_univ,ZMod.card]
  simp [two,Ne.symm two,diff]

private theorem mem_active {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    x ∈ active p ↔ x≠0 ∧ x^2-4 ≠ 0 := by
  have poly : x^2-4=(x-2)*(x+2) := by ring
  simp [active,poly,mul_ne_zero_iff,sub_ne_zero,not_or, add_eq_zero_iff_eq_neg]

private theorem weight_ne {p : ℕ} [Fact p.Prime] {z : ZMod p} (reg : z-4 ≠ 0) : weight z≠0 := by
  rcases sq_eq_one_iff.mp (quadraticChar_sq_one reg) with h | h <;> simp [weight,h]

theorem component_positive {p : ℕ} [Fact p.Prime] (n : ℕ) :
    component p (n+1) = signal (active p) (fun t => weight (t^2)*t) n := by
  unfold component signal
  rw [← sum_neg_distrib]
  calc
    _ = ∑ t : ZMod p, (weight (t^2)*t)*t^n := by
      apply sum_congr rfl
      intro t _
      simp only [weight,pow_succ]
      ring
    _ = _ := by
      symm
      apply sum_subset (subset_univ _)
      intro t _ bad
      by_cases h : t=0
      · simp [h]
      · have z : t^2-4=0 := by simpa [mem_active,h] using bad
        simp [weight,z]

/-- Positive degrees require an order at least the number of active trace parameters. -/
theorem local_order {p : ℕ} [Fact p.Prime] (odd : p≠2) (P : (ZMod p)[X])
    (non : P≠0) (start : ℕ)
    (fit : ∀ i : Fin (p-3), shift P (fun k => component p (k+1)) (start+i)=0) :
    p-3 ≤ P.natDegree := by
  rw [← active_card odd]
  apply lower P non (active p) (fun t => weight (t^2)*t) start
  · intro t ht
    obtain ⟨nz,reg⟩ := (mem_active t).mp ht
    exact mul_ne_zero (weight_ne reg) nz
  · exact fun t ht => ((mem_active t).mp ht).1
  · intro i
    simpa only [component_positive] using fit ⟨i, (active_card odd) ▸ i.isLt⟩

private theorem even_fiber {p : ℕ} [Fact p.Prime] {x : ZMod p} (hx : x∈active p) :
    ((active p).filter fun t => t^2=x^2) = {x,-x} := by
  have nz := ((mem_active x).mp hx).1
  have reg := ((mem_active x).mp hx).2
  have nh : -x ∈ active p := (mem_active _).mpr ⟨neg_ne_zero.mpr nz, by simpa using reg⟩
  ext t
  simp only [mem_filter, sq_eq_sq_iff_eq_or_eq_neg, mem_insert, mem_singleton]
  constructor
  · exact And.right
  · rintro (rfl|rfl)
    · exact ⟨hx,Or.inl rfl⟩
    · exact ⟨nh,Or.inr rfl⟩

private theorem fiber_card {p : ℕ} [Fact p.Prime] (odd : p≠2) {z : ZMod p} (hz : z ∈ evenBases p) :
    ((active p).filter fun t => t^2=z).card=2 := by
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
  rw [even_fiber hx,card_pair (pair_distinct odd ((mem_active _).mp hx).1)]

theorem even_card {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    2*(evenBases p).card=p-3 := by
  rw [← active_card odd, card_eq_sum_card_fiberwise (f := fun t:ZMod p => t^2)
    (t := evenBases p) (fun _ hx => mem_image_of_mem _ hx)]
  rw [sum_congr rfl fun _ hz => fiber_card odd hz, sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]

theorem component_even {p : ℕ} [Fact p.Prime] (odd : p≠2) (n : ℕ) :
    component p (2*(n+1)) = signal (evenBases p) (fun z => 2*weight z*z) n := by
  rw [show 2*(n+1)=2*n+1+1 by omega, component_positive]
  unfold signal
  let f (z : ZMod p) := weight z*z*z^n
  calc
    _ = ∑ t ∈ active p, f (t^2) := by
      apply sum_congr rfl
      intro t _
      simp [f, pow_succ, pow_mul]; ring
    _ = ∑ z ∈ evenBases p, ∑ _t ∈ (active p).filter (fun t => t^2=z), f z :=
      (sum_fiberwise_of_maps_to' (g := fun t:ZMod p => t^2) (fun _ hx => mem_image_of_mem _ hx) f).symm
    _ = _ := by
      apply sum_congr rfl
      intro z hz
      simp [f,fiber_card odd hz]; ring

/-- Matching a whole block of even moments is equivalent to vanishing at every active square. -/
theorem component_even_roots {p : ℕ} [Fact p.Prime] (odd : p≠2) (P : (ZMod p)[X])
    (start : ℕ) :
    (∀ i : Fin (evenBases p).card, shift P (fun k => component p (2*(k+1))) (start+i)=0) ↔
      ∀ z ∈ evenBases p, P.eval z=0 := by
  simp_rw [component_even odd]
  apply annihilator_iff
  · intro z hz
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hz
    obtain ⟨nz,reg⟩ := (mem_active t).mp ht
    exact mul_ne_zero (mul_ne_zero (two_nonzero odd) (weight_ne reg)) (pow_ne_zero _ nz)
  · intro z hz
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hz
    exact pow_ne_zero _ ((mem_active t).mp ht).1

/-- For positive even degrees, each pair of opposite traces contributes one base. -/
theorem local_even_order {p : ℕ} [Fact p.Prime] (odd : p≠2) (P : (ZMod p)[X])
    (non : P≠0) (start : ℕ)
    (fit : ∀ i : Fin ((p-3)/2), shift P (fun k => component p (2*(k+1))) (start+i)=0) :
    (p-3)/2 ≤ P.natDegree := by
  have count : (evenBases p).card=(p-3)/2 := by have := even_card odd; omega
  rw [← count] at fit ⊢
  apply Polynomial.card_le_degree_of_subset_roots
  intro z hz
  exact (Polynomial.mem_roots non).mpr ((component_even_roots odd P start).mp fit z hz)

theorem local_sharp {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    ∃ P : (ZMod p)[X], P.Monic ∧ P.natDegree=p-3 ∧
      ∀ n, shift P (fun k => component p (k+1)) n=0 := by
  obtain ⟨P,mon,deg,all⟩ := sharp (active p) (fun t => weight (t^2)*t)
  exact ⟨P, mon, deg.trans (active_card odd), by simpa only [component_positive] using all⟩

theorem local_even_sharp {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    ∃ P : (ZMod p)[X], P.Monic ∧ P.natDegree=(p-3)/2 ∧
      ∀ n, shift P (fun k => component p (2*(k+1))) n=0 := by
  obtain ⟨P,mon,deg,all⟩ := sharp (evenBases p) (fun t => 2*weight t*t)
  exact ⟨P,mon,by have := even_card odd; omega, by simpa only [component_even odd] using all⟩

theorem shift_map {R K : Type*} [CommRing R] [CommRing K] (f : R →+* K) (P : R[X])
    (u : ℕ → R) (n : ℕ) :
    f (shift P u n) = shift (P.map f) (fun k => f (u k)) n := by
  simp only [shift, map_sum, map_mul, Polynomial.coeff_map]
  symm
  apply sum_subset (Polynomial.support_map_subset f P)
  intro j _ outside
  rw [← Polynomial.coeff_map, Polynomial.not_mem_support_iff.mp outside, zero_mul]

open PrimeFactors.ProjectiveWordMoments

private theorem from_component {p N : ℕ} [Fact p.Prime] [NeZero N] (odd : p≠2)
    (f : ZMod N →+* ZMod p) (component_eq : ∀ k, f (moment N k) = component p k)
    (P : (ZMod N)[X]) (mon : P.Monic) (start : ℕ)
    (fit : ∀ i : Fin (p-3), shift P (fun k => moment N (k+1)) (start+i)=0) :
    p-3 ≤ P.natDegree := by
  rw [← mon.natDegree_map f]
  apply local_order odd (P.map f) (mon.map f).ne_zero start
  intro i
  have h := congrArg f (fit i)
  simpa only [shift_map, component_eq, map_zero] using h

private theorem from_component_even {p N : ℕ} [Fact p.Prime] [NeZero N] (odd : p≠2)
    (f : ZMod N →+* ZMod p) (component_eq : ∀ k, f (moment N k) = component p k)
    (P : (ZMod N)[X]) (mon : P.Monic) (start : ℕ)
    (fit : ∀ i : Fin ((p-3)/2), shift P (fun k => moment N (2*(k+1))) (start+i)=0) :
    (p-3)/2 ≤ P.natDegree := by
  rw [← mon.natDegree_map f]
  apply local_even_order odd (P.map f) (mon.map f).ne_zero start
  intro i
  have h := congrArg f (fit i)
  simpa only [shift_map, component_eq, map_zero] using h

/-- The larger-prime bound applies to the actual composite sequence for any
block of q−3 consecutive recurrence equations, starting at any positive degree. -/
theorem composite_order {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (P : (ZMod (p*q))[X]) (mon : P.Monic) (start : ℕ)
    (fit : ∀ i : Fin (q-3), shift P (fun k => moment (p*q) (k+1)) (start+i)=0) :
    q-3 ≤ P.natDegree := by
  apply from_component hq ((RingHom.snd (ZMod p) (ZMod q)).comp
    (ZMod.chineseRemainder cop).toRingHom) _ P mon start fit
  intro k
  exact congrArg Prod.snd (components cop hp hq k)

/-- Every other moment still has (q−3)/2 active square bases. -/
theorem composite_even_order {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (P : (ZMod (p*q))[X]) (mon : P.Monic) (start : ℕ)
    (fit : ∀ i : Fin ((q-3)/2), shift P (fun k => moment (p*q) (2*(k+1))) (start+i)=0) :
    (q-3)/2 ≤ P.natDegree := by
  apply from_component_even hq ((RingHom.snd (ZMod p) (ZMod q)).comp
    (ZMod.chineseRemainder cop).toRingHom) _ P mon start fit
  intro k
  exact congrArg Prod.snd (components cop hp hq k)

open HasseRecurrenceDegree

private noncomputable def diagonalPolynomial : ℤ[X] := (X+1)^2

private theorem quadratic {p : ℕ} (ι : ℤ →+* ZMod p) :
    diagonalPolynomial.map ι = (X+1)^2 := by simp [diagonalPolynomial]

private theorem diagonal_degree {p : ℕ} [Fact p.Prime] (ι : ℤ →+* ZMod p) :
    (diagonalPolynomial.map ι).natDegree = 2 := by
  rw [quadratic, natDegree_pow, ← C_1, natDegree_X_add_C]

private theorem diagonal {p : ℕ} [Fact p.Prime] (ι : ℤ →+* ZMod p) (i : ℕ) :
    HasseRecurrenceDegree.moment (diagonalPolynomial.map ι) i = (ProjectiveWordMoments.central (2*i) : ZMod p) := by
  rw [HasseRecurrenceDegree.moment, quadratic, ← pow_mul, coeff_X_add_one_pow]
  simp [ProjectiveWordMoments.central, Nat.mul_comm 2 i]

/-- Even before the first exceptional moment, exact recurrence matching on
degrees 0,2,…,2m forces the recurrence order to grow with m. -/
theorem early_bound {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (order : p<q) (s m : ℕ) (small : 2*m<p-1)
    (b : ℕ → ZMod (p*q)) (b0 : b 0=1)
    (rec : ∀ i, s < i → i ≤ m → (∑ j ∈ Finset.range (s+1),
      b j * ProjectiveWordMoments.moment (p*q) (2*(i-j))) = 0) :
    m < 2*(s+1) := by
  let φ : ZMod (p*q) →+* ZMod p := (RingHom.fst _ _).comp (ZMod.chineseRemainder cop).toRingHom
  let ι := Int.castRingHom (ZMod p)
  have diag (j : ℕ) (jm : j≤m) :
      φ (ProjectiveWordMoments.moment (p*q) (2*j)) =
      HasseRecurrenceDegree.moment (diagonalPolynomial.map ι) j := by
    rw [ProjectiveWordMoments.jacobi_moment cop hp hq _ (by omega) (by omega), map_natCast, diagonal]
  have recField (i : ℕ) (si : s < i) (im : i≤m) :
      (∑ j ∈ Finset.range (s+1), φ (b j) * HasseRecurrenceDegree.moment (diagonalPolynomial.map ι) (i-j)) = 0 := by
    have result := congrArg φ (rec i si im)
    simp only [map_sum, map_mul, map_zero] at result
    have rep (j : ℕ) := diag (i-j) (by omega)
    simpa only [rep] using result
  have base : φ (b 0)=1 := by rw [b0, map_one]
  obtain ⟨a, az, fit⟩ := fit_of_recurrence _ _ s m (by simp [HasseRecurrenceDegree.moment]) base recField
  have f0 : (diagonalPolynomial.map ι).coeff 0=1 := by simp [quadratic,Polynomial.coeff_zero_eq_eval_zero]
  have ch : ((diagonalPolynomial.map ι).natDegree : ZMod p) ≠ 0 := by
    simpa only [diagonal_degree,Nat.cast_ofNat] using (Ring.two_ne_zero (R:=ZMod p) (by rwa [ZMod.ringChar_zmod_n]))
  have size := finite_prefix diagonalPolynomial ι s m a _ f0 (by rw [diagonal_degree]) ch az base fit
  simpa only [diagonal_degree,Nat.mul_comm (s+1)] using size

/-- A recurrence matching every even degree before the first exception needs order at
least ⌊(p−3)/4⌋, where p is the smaller prime factor. -/
theorem before_exception {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (order : p<q) (s : ℕ)
    (b : ℕ → ZMod (p*q)) (b0 : b 0=1)
    (rec : ∀ i, s < i → i ≤ (p-3)/2 → (∑ j ∈ Finset.range (s+1),
      b j * ProjectiveWordMoments.moment (p*q) (2*(i-j))) = 0) :
    (p-3)/4 ≤ s := by
  have pp := (Fact.out : p.Prime).two_le
  have := early_bound cop hp hq order s ((p-3)/2) (by omega) b b0 rec
  omega

end PrimeFactors.JacobiMomentRecurrence
