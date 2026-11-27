import PrimeFactors.JacobiMomentRecurrence

/-!
# The exact recurrence order of positive Jacobi moments

A monic recurrence modulo a product of two primes can be constructed from
recurrences at the individual primes. Their degrees can differ. Multiplying
the shorter polynomial by a power of the shift preserves its recurrence and
allows CRT to combine the coefficients, including the common leading one.
-/

namespace PrimeFactors.JacobiSharpComposite

open Polynomial Finset
open JacobiMomentRecurrence ProjectiveWordMoments

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]

/-- Degrees of monic forward-shift annihilators with coefficients in the base ring. -/
def orders (u : ℕ → R) : Set ℕ :=
  {d | ∃ P : R[X], P.Monic ∧ P.natDegree = d ∧ ∀ n, shift P u n = 0}

theorem shift_pad (P : R[X]) (u : ℕ → R) (n t : ℕ) :
    shift (P * X ^ t) u n = shift P u (n + t) := by
  classical
  symm
  unfold shift
  apply sum_bij (fun i _ => i + t)
  · intro i hi
    simpa [Polynomial.mem_support_iff, coeff_mul_X_pow] using hi
  · intro i _ j _ h
    omega
  · intro i hi
    rw [Polynomial.mem_support_iff, coeff_mul_X_pow'] at hi
    by_cases h : t ≤ i
    · rw [if_pos h] at hi
      exact ⟨i-t, Polynomial.mem_support_iff.mpr hi, Nat.sub_add_cancel h⟩
    · simp [h] at hi
  · intro i _
    rw [coeff_mul_X_pow]
    congr 2
    omega

/-- Glue two equal-degree monic polynomials coefficient by coefficient. -/
theorem lift_monic [Nontrivial R] (e : R ≃+* A × B) (P : A[X]) (Q : B[X]) (d : ℕ)
    (pm : P.Monic) (qm : Q.Monic) (pd : P.natDegree = d) (qd : Q.natDegree = d) :
    ∃ T : R[X], T.Monic ∧ T.natDegree = d ∧
      T.map ((RingHom.fst A B).comp e.toRingHom) = P ∧
      T.map ((RingHom.snd A B).comp e.toRingHom) = Q := by
  classical
  let c (i : ℕ) := e.symm (P.coeff i, Q.coeff i)
  let T : R[X] := ∑ i ∈ range (d+1), monomial i (c i)
  have tc (i : ℕ) : T.coeff i = c i := by
    by_cases small : i ≤ d
    · simp [T, finset_sum_coeff, coeff_monomial, small, Nat.lt_succ_iff]
    · have ip := coeff_eq_zero_of_natDegree_lt (p := P) (show P.natDegree < i by omega)
      have iq := coeff_eq_zero_of_natDegree_lt (p := Q) (show Q.natDegree < i by omega)
      simp [T, finset_sum_coeff, coeff_monomial, small, Nat.lt_succ_iff, c, ip, iq,
        show ((0 : A), (0 : B)) = 0 from rfl]
  have top : T.coeff d = 1 := by
    rw [tc]
    dsimp [c]
    rw [← pd, pm.coeff_natDegree, pd, ← qd, qm.coeff_natDegree]
    exact e.symm.map_one
  have deg : T.natDegree = d := by
    apply le_antisymm _ (le_natDegree_of_ne_zero (by rw [top]; exact one_ne_zero))
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [tc]
    dsimp [c]
    rw [coeff_eq_zero_of_natDegree_lt (p := P) (by omega),
      coeff_eq_zero_of_natDegree_lt (p := Q) (by omega)]
    exact e.symm.map_zero
  refine ⟨T, by change T.coeff T.natDegree = 1; rw [deg, top], deg, ?_, ?_⟩
  · ext i
    rw [coeff_map, tc]
    exact congrArg Prod.fst (e.apply_symm_apply _)
  · ext i
    rw [coeff_map, tc]
    exact congrArg Prod.snd (e.apply_symm_apply _)

/-- If the two component sequences have monic annihilators of degrees a≤b,
their CRT combination has one of degree b, including a=0. -/
theorem crt_order [Nontrivial A] (e : R ≃+* A × B) (u : ℕ → R)
    (ua : ℕ → A) (ub : ℕ → B) (proj : ∀ n, e (u n) = (ua n, ub n))
    {a b : ℕ} (le : a ≤ b) (left : a ∈ orders ua) (right : b ∈ orders ub) :
    b ∈ orders u := by
  letI : Nontrivial R := e.symm.injective.nontrivial
  obtain ⟨P, pm, pd, pa⟩ := left
  obtain ⟨Q, qm, qd, qa⟩ := right
  let t := b-a
  have pd' : (P * X^t).natDegree = b := by
    rw [natDegree_mul_X_pow t pm.ne_zero, pd, Nat.add_sub_of_le le]
  obtain ⟨T, tm, td, tl, tr⟩ :=
    lift_monic e (P*X^t) Q b (pm.mul (monic_X_pow t)) qm pd' qd
  refine ⟨T,tm,td,fun n => e.injective ?_⟩
  rw [map_zero]
  apply Prod.ext
  · let f := (RingHom.fst A B).comp e.toRingHom
    change f (shift T u n) = 0
    rw [shift_map, tl]
    have ff : (fun k => f (u k)) = ua := funext fun k => congrArg Prod.fst (proj k)
    rw [ff, shift_pad, pa]
  · let f := (RingHom.snd A B).comp e.toRingHom
    change f (shift T u n) = 0
    rw [shift_map, tr]
    have ff : (fun k => f (u k)) = ub := funext fun k => congrArg Prod.snd (proj k)
    rw [ff, qa]

/-- Minimum monic recurrence order for positive even moments modulo a semiprime. -/
theorem least_even {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p ≠ 2) (hq : q ≠ 2) (size : p < q) :
    IsLeast (orders (fun k => moment (p*q) (2*(k+1)))) ((q-3)/2) := by
  constructor
  · apply crt_order (ZMod.chineseRemainder cop) _
      (fun k => component p (2*(k+1))) (fun k => component q (2*(k+1)))
      (fun k => components cop hp hq (2*(k+1))) (a := (p-3)/2) (b := (q-3)/2) (by omega)
    · exact local_even_sharp hp
    · exact local_even_sharp hq
  · intro d h
    obtain ⟨P,mon,rfl,fit⟩ := h
    exact composite_even_order cop hp hq P mon 0 fun i => fit _

/-- Minimum order when every positive degree is retained. -/
theorem least_positive {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p ≠ 2) (hq : q ≠ 2) (size : p < q) :
    IsLeast (orders (fun k => moment (p*q) (k+1))) (q-3) := by
  constructor
  · apply crt_order (ZMod.chineseRemainder cop) _
      (fun k => component p (k+1)) (fun k => component q (k+1))
      (fun k => components cop hp hq (k+1)) (a := p-3) (b := q-3) (by omega)
    · exact local_sharp hp
    · exact local_sharp hq
  · intro d h
    obtain ⟨P,mon,rfl,fit⟩ := h
    exact composite_order cop hp hq P mon 0 fun i => fit _

/-- Reading the minimum order determines the larger prime. -/
theorem even_recovers_larger {p q d : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p ≠ 2) (hq : q ≠ 2) (size : p < q)
    (given : IsLeast (orders (fun k => moment (p*q) (2*(k+1)))) d) :
    q = 2*d + 3 := by
  have order := given.unique (least_even cop hp hq size)
  obtain ⟨a,ha⟩ := (Fact.out : q.Prime).odd_of_ne_two hq
  have := (Fact.out : p.Prime).two_le
  omega

/-- Distinct odd factors both at least 2h force even-moment order at least h. -/
theorem factor_width_lower {p q h : ℕ} (hp : Odd p) (hq : Odd q)
    (floor : 2*h ≤ p) (size : p < q) : h ≤ (q-3)/2 := by
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hq
  omega

/-- Orders that fit just the stated finite run of consecutive equations. -/
def blockOrders (u : ℕ → R) (start length : ℕ) : Set ℕ :=
  {d | ∃ P : R[X], P.Monic ∧ P.natDegree = d ∧
    ∀ i : Fin length, shift P u (start + i) = 0}

/-- Any run of at least d equations already has the same exact minimum.
Testing all orders up to the public bound length consequently needs at most
2*length consecutive moments. -/
theorem least_even_block {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p ≠ 2) (hq : q ≠ 2) (size : p < q) (start length : ℕ)
    (enough : (q-3)/2 ≤ length) :
    IsLeast (blockOrders (fun k => moment (p*q) (2*(k+1))) start length) ((q-3)/2) := by
  constructor
  · obtain ⟨P, mon, deg, fit⟩ := (least_even cop hp hq size).1
    exact ⟨P, mon, deg, fun i => fit _⟩
  · rintro d ⟨P, mon, rfl, fit⟩
    exact composite_even_order cop hp hq P mon start
      fun i => fit ⟨i.val, lt_of_lt_of_le i.isLt enough⟩

/-- For 77 the even and all-positive minima are four and eight respectively. -/
theorem seventy_seven_orders :
    IsLeast (orders (fun k => moment 77 (2*(k+1)))) 4 ∧
      IsLeast (orders (fun k => moment 77 (k+1))) 8 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact ⟨least_even (p:=7) (q:=11) (by decide) (by decide) (by decide) (by decide),
    least_positive (p:=7) (q:=11) (by decide) (by decide) (by decide) (by decide)⟩

/-- An explicit order-four polynomial for the even moments modulo 77. -/
noncomputable def examplePolynomial (R : Type*) [CommRing R] : R[X] :=
  X^4 + 4*X^3 + 16*X^2 + 42*X + 14

private theorem example_component {p : ℕ} [Fact p.Prime] (odd : p ≠ 2)
    (roots : ∀ t : ZMod p, t ≠ 0 → t ≠ 2 → t ≠ -2 →
      (t^2)^4 + 4*(t^2)^3 + 16*(t^2)^2 + 42*t^2 + 14 = 0) (n : ℕ) :
    shift (examplePolynomial (ZMod p)) (fun k => component p (2*(k+1))) n = 0 := by
  simp_rw [component_even odd]
  rw [shift_signal]
  apply sum_eq_zero
  intro x hx
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hx
  have reg : t ≠ 0 ∧ t ≠ 2 ∧ t ≠ -2 := by
    simpa [active] using ht
  have root : (examplePolynomial (ZMod p)).eval (t^2) = 0 := by
    simpa [examplePolynomial] using roots t reg.1 reg.2.1 reg.2.2
  simp [root]

/-- The displayed polynomial works at every shift, with both prime-field
root certificates checked by finite modular arithmetic. -/
theorem seventy_seven_recurrence (n : ℕ) :
    shift (examplePolynomial (ZMod 77)) (fun k => moment 77 (2*(k+1))) n = 0 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  let e := ZMod.chineseRemainder (m := 7) (n := 11) (by decide)
  have projections (k : ℕ) :
      e (moment 77 (2*(k+1))) = (component 7 (2*(k+1)), component 11 (2*(k+1))) :=
    components (by decide) (by decide) (by decide) _
  apply e.injective
  rw [map_zero]
  apply Prod.ext
  · let f := (RingHom.fst (ZMod 7) (ZMod 11)).comp e.toRingHom
    change f (shift _ _ _) = 0
    rw [shift_map]
    have val (k : ℕ) : f (moment 77 (2*(k+1))) = component 7 (2*(k+1)) :=
      congrArg Prod.fst (projections k)
    simp_rw [val]
    simpa [examplePolynomial] using example_component (p := 7) (by decide) (by decide) n
  · let f := (RingHom.snd (ZMod 7) (ZMod 11)).comp e.toRingHom
    change f (shift _ _ _) = 0
    rw [shift_map]
    have val (k : ℕ) : f (moment 77 (2*(k+1))) = component 11 (2*(k+1)) :=
      congrArg Prod.snd (projections k)
    simp_rw [val]
    simpa [examplePolynomial] using example_component (p := 11) (by decide) (by decide) n

end PrimeFactors.JacobiSharpComposite
