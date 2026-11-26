import PrimeFactors.PascalReadout
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Data.Nat.Prime.Factorial

/-! The first exceptional coefficient of a normalized local expansion, and
the earlier threshold for a direct gcd of an individual half-power coefficient. -/

namespace PrimeFactors.HasseTruncatedSeries

open Polynomial

/-- Up to and including degree p there is exactly one nonconstant term.
This polynomial identity can be evaluated in any residue algebra. -/
theorem first_correction {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p < q) :
    (X : (ZMod (p*q))[X])^(p+1) ∣
      (X+1)^(p*q) - 1 - C (q : ZMod (p*q)) * X^p := by
  rw [X_pow_dvd_iff]
  intro j hj
  rw [coeff_sub, coeff_sub, coeff_X_add_one_pow, coeff_C_mul, coeff_X_pow, coeff_one]
  by_cases zero : j=0
  · subst j
    simp [pp.ne_zero, Ne.symm pp.ne_zero]
  have raw := pascal_row_prefix pp qp order (Nat.pos_of_ne_zero zero) (by omega)
  have digits := (ZMod.natCast_eq_natCast_iff _ _ _).mpr raw
  by_cases eq : p=j
  · subst j
    simp [order.ne, pp.ne_zero] at digits ⊢
    simpa [sub_eq_zero] using digits
  · have jq : j≠q := by omega
    simp [eq, Ne.symm eq, jq, zero] at digits ⊢
    exact digits

/-- The first extra coefficient is a nonzero zero divisor. -/
theorem first_extra {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p < q) :
    ((X+1 : (ZMod (p*q))[X])^(p*q)).coeff p = (q : ZMod (p*q)) ∧
      (q : ZMod (p*q)) ≠ 0 := by
  constructor
  · rw [coeff_X_add_one_pow]
    have digits := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (pascal_row_prefix pp qp order (k:=p) pp.pos (by have := pp.pos; omega))
    simpa [order.ne] using digits
  · rw [ne_eq, ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact Nat.not_dvd_of_pos_of_lt qp.pos (by have h := Nat.mul_le_mul_right q pp.two_le; have := qp.pos; omega)

section Algebra

variable {p q : ℕ} {R : Type*} [CommRing R] [Algebra (ZMod (p*q)) R]

/-- In a jet one order past p, the first correction is q times the pth
power of the increment, independently of its higher coefficients. -/
theorem next_jet (pp : p.Prime) (qp : q.Prime) (order : p<q)
    (t : R) (nil : t^(p+1)=0) :
    (1+t)^(p*q)=1+(q:R)*t^p := by
  obtain ⟨F,hF⟩ := first_correction pp qp order
  have h := congrArg (fun f : (ZMod (p*q))[X] => aeval t f) hF
  simp [nil] at h
  rw [add_comm 1 t]
  linear_combination h

/-- All principal units have exponent dividing pq until the degree-p term
is retained. The assumption t^d=0 with d≤p implies this hypothesis. -/
theorem principal_power (pp : p.Prime) (qp : q.Prime) (order : p<q)
    (t : R) (nil : t^p=0) : (1+t)^(p*q)=1 := by
  simpa [nil] using next_jet pp qp order t (by rw [pow_succ, nil, zero_mul])

/-- The half-power is the unique principal inverse square root. Equivalent
readings of any normalized substitution must return this same root. -/
theorem inverse_square_root (pp : p.Prime) (qp : q.Prime) (order : p<q)
    {m : ℕ} (half : 2*m+1=p*q) (t u : R) (tn : t^p=0) (un : u^p=0) :
    (1+u)^2*(1+t)=1 ↔ 1+u=(1+t)^m := by
  constructor
  · intro equation
    have raised := congrArg (fun z : R => z^m) equation
    simp only [mul_pow, ← pow_mul, one_pow] at raised
    calc
      1+u = (1+u)*((1+u)^(2*m)*(1+t)^m) := by rw [raised, mul_one]
      _ = (1+u)^(p*q)*(1+t)^m := by rw [← half, pow_succ']; ring
      _ = (1+t)^m := by rw [principal_power pp qp order _ un, one_mul]
  · intro eqn
    rw [eqn, ← pow_mul, ← pow_succ, Nat.mul_comm m 2, half]
    exact principal_power pp qp order _ tn

/-- The root belongs to the same principal neighborhood as its input. -/
theorem exists_unique_root (pp : p.Prime) (qp : q.Prime) (order : p<q)
    {m : ℕ} (half : 2*m+1=p*q) (t : R) (nil : t^p=0) :
    ∃! v : R, (v-1)^p=0 ∧ v^2*(1+t)=1 := by
  have div : t ∣ (1+t)^m-1 := by simpa using sub_one_dvd_pow_sub_one (1+t) m
  obtain ⟨a, eqn⟩ := div
  have rn : ((1+t)^m-1)^p=0 := by rw [eqn, mul_pow, nil, zero_mul]
  have add (x : R) : 1+(x-1)=x := by ring
  refine ⟨(1+t)^m, ⟨rn, ?_⟩, ?_⟩
  · have h := inverse_square_root pp qp order half t ((1+t)^m-1) nil rn
    simpa only [add, iff_true] using h
  · rintro v ⟨vn,sq⟩
    simpa only [add] using (inverse_square_root pp qp order half t (v-1) nil vn).mp
      (by simpa only [add] using sq)

/-- Any polynomial whose constant term is one has an increment divisible
by the parameter, including polynomials obtained after a translation. -/
theorem normalized_polynomial (t : R) (F : R[X]) (constant : F.coeff 0=1) :
    ∃ a : R, F.eval t=1+t*a := by
  have divides : X ∣ F-1 := X_dvd_iff.mpr (by simp [coeff_sub, constant])
  obtain ⟨A,hA⟩ := divides
  have h := congrArg (fun f : R[X] => f.eval t) hA
  simp only [eval_sub, eval_one, eval_mul, eval_X] at h
  exact ⟨A.eval t, by linear_combination h⟩

/-- Regular normalized rational expressions remain principal. Both numerator
and denominator may be arbitrary polynomials in the same nilpotent parameter. -/
theorem normalized_quotient {d : ℕ} (t a b : R) (nil : t^d=0) :
    ∃ v c : R, (1+t*b)*v=1 ∧ (1+t*a)*v=1+t*c := by
  have h : IsNilpotent (t*b) := ⟨d, by rw [mul_pow, nil, zero_mul]⟩
  obtain ⟨v,hv⟩ := h.isUnit_one_add.exists_right_inv
  exact ⟨v, (a-b)*v, hv, by linear_combination hv⟩

end Algebra

private theorem choose_unit {r n k : ℕ} (prime : r.Prime) (lo : k≤n) (hi : n<r) :
    ¬ r ∣ n.choose k := by
  intro bad
  apply (Nat.not_le_of_lt hi) ∘ prime.dvd_factorial.mp
  rw [← Nat.choose_mul_factorial_mul_factorial lo]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left bad _) _

/-- A prime r divides the jth raw coefficient precisely after half its local
row is passed, provided j is smaller than r. -/
theorem linear_coordinate {r s j : ℕ} (rp : r.Prime) (ro : Odd r) (so : Odd s)
    (short : j<r) :
    r ∣ ((r*s-1)/2).choose j ↔ r ≤ 2*j := by
  obtain ⟨a,ha⟩ := ro
  obtain ⟨b,hb⟩ := so
  have index : (r*s-1)/2 = r*b + a := by
    have e : r*s = 2*(r*b+a)+1 := by rw [ha,hb]; ring
    omega
  letI : Fact r.Prime := ⟨rp⟩
  have digits := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := r) (n := r*b+a) (k := j)
  simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt (show a<r by omega),
    Nat.mod_eq_of_lt short, Nat.div_eq_of_lt short, Nat.choose_zero_right, mul_one] at digits
  rw [index, digits.dvd_iff (dvd_refl r)]
  by_cases lo : j≤a
  · simpa [show ¬r≤2*j by omega] using choose_unit rp lo (by omega)
  · simp [Nat.choose_eq_zero_of_lt (show a<j by omega), show r≤2*j by omega]

/-- The first divisor window for the raw coordinate of the half power. -/
theorem coordinate_gcd {p q j : ℕ} (pp : p.Prime) (qp : q.Prime)
    (po : Odd p) (qo : Odd q) (order : p<q) (short : j<p) :
    (p*q).gcd (((p*q-1)/2).choose j) =
      if 2*j<p then 1 else if 2*j<q then p else p*q := by
  have left := linear_coordinate pp po qo short
  have right := linear_coordinate qp qo po (lt_trans short order)
  rw [Nat.mul_comm q p] at right
  split_ifs with below before
  · exact Nat.coprime_iff_gcd_eq_one.mp (Nat.coprime_mul_iff_left.mpr
      ⟨pp.coprime_iff_not_dvd.mpr (by omega), qp.coprime_iff_not_dvd.mpr (by omega)⟩)
  · have h := Nat.gcd_mul_of_coprime_of_dvd (qp.coprime_iff_not_dvd.mpr (by omega))
        (left.mpr (by omega))
    simpa only [Nat.mul_comm q p] using h
  · apply Nat.gcd_eq_left
    exact ((Nat.coprime_primes pp qp).mpr order.ne).mul_dvd_of_dvd_of_dvd
      (left.mpr (by omega)) (right.mpr (by omega))

/-- The public column one past half the integer square root is inside the
isolating interval for every pair of comparable odd primes. -/
theorem public_column {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (po : Odd p) (qo : Odd q) (order : p<q) (balanced : q≤2*p) :
    (p*q).gcd (((p*q-1)/2).choose ((p*q).sqrt/2+1)) = p := by
  obtain ⟨a,ha⟩ := po
  obtain ⟨b,hb⟩ := qo
  have lower : p ≤ (p*q).sqrt := Nat.le_sqrt.mpr (Nat.mul_le_mul_left p order.le)
  have upper : (p*q).sqrt < 2*b := by
    apply Nat.sqrt_lt.mpr
    have mul := Nat.mul_le_mul_right q (show p+2≤q by omega)
    nlinarith [mul]
  rw [coordinate_gcd pp qp ⟨a,ha⟩ ⟨b,hb⟩ order (by omega), if_neg (by omega), if_pos (by omega)]

example : (List.range 4).map (fun j => (15:ℕ).choose j % 15) = [1,0,0,5] := by decide +kernel

example : Nat.gcd 187 ((93:ℕ).choose 7) = 11 := by decide +kernel
example : Nat.gcd 187 ((93:ℕ).choose 5) = 1 := by decide +kernel
example : (187:ℕ).choose 11 % 187 = 17 := by decide +kernel

end PrimeFactors.HasseTruncatedSeries
