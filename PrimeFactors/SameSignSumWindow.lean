import PrimeFactors.OrderDivisorSumBits
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Tactic.NormNum.Prime

/-! A public factor-sum interval can exclude a common local sign when the sign
also specifies a common residue. A short interval gives at most one sum per sign. -/

namespace PrimeFactors.SameSignSumWindow

/-- If both factors have residue e = ±1 modulo m, the sum is fixed modulo m². -/
theorem sum_class {p q m e : ℤ} (sign : e = 1 ∨ e = -1)
    (left : m ∣ p-e) (right : m ∣ q-e) :
    p+q ≡ e*(p*q+1) [ZMOD m^2] := by
  have h : m^2 ∣ (p-e)*(q-e) := by simpa only [pow_two] using mul_dvd_mul left right
  rw [Int.modEq_iff_dvd]
  rcases sign with rfl | rfl
  · convert h using 1
    ring
  · convert dvd_neg.mpr h using 1
    ring

/-- Missing a residue entails fewer than M integer locations in the interval. -/
theorem missing_short {L H c M : ℤ} (pos : 0 < M)
    (miss : ∀ x, L ≤ x → x ≤ H → ¬ x ≡ c [ZMOD M]) : H-L+1 < M := by
  let x := L + (c-L)%M
  have low : L ≤ x := le_add_of_nonneg_right (Int.emod_nonneg _ pos.ne')
  have hmod : x ≡ c [ZMOD M] := by
    convert (Int.mod_modEq (c-L) M).add_left L using 1
    ring
  have rem := Int.emod_lt_of_pos (c-L) pos
  have outside : H < x := lt_of_not_ge (fun hi => miss x low hi hmod)
  dsimp [x] at outside
  omega

/-- At most one integer from another specified class can remain in that window. -/
theorem unique_in_window {L H c M x y : ℤ} (width : H-L < M)
    (xl : L ≤ x) (xh : x ≤ H) (yl : L ≤ y) (yh : y ≤ H)
    (xc : x ≡ c [ZMOD M]) (yc : y ≡ c [ZMOD M]) : x = y := by
  have dz := Int.eq_zero_of_abs_lt_dvd (xc.trans yc.symm).dvd
    (show |y-x| < M by rw [abs_lt]; omega)
  omega

/-- With a square root of D, a norm-one point on this trace yields an
ordinary unit of exact order five. This works over a composite modulus. -/
theorem order_five_if_square {R : Type*} [CommRing R] {D a b : R}
    (five : (5 : R) ≠ 0) (norm : a^2-D*b^2=1) (trace : (2*a)^2+2*a-1=0)
    (sq : IsSquare D) : ∃ u : Rˣ, orderOf u = 5 := by
  obtain ⟨i,hi⟩ := sq
  have hi' : i^2 = D := by simpa only [pow_two] using hi.symm
  let v := a+b*i
  have quadratic : v^2+1 = (2*a)*v := by
    dsimp [v]
    linear_combination b^2 * hi' - norm
  have cyclo : v^4+v^3+v^2+v+1=0 := by
    calc
      _ = (v^2+1)^2 + v*(v^2+1)-v^2 := by ring
      _ = ((2*a)*v)^2 + v*((2*a)*v)-v^2 := by rw [quadratic]
      _ = v^2*((2*a)^2+2*a-1) := by ring
      _ = 0 := by rw [trace,mul_zero]
  have power : v^5 = 1 := by linear_combination (v-1)*cyclo
  have ne : v ≠ 1 := by
    intro one
    rw [one] at cyclo
    norm_num at cyclo
    exact five cyclo
  let u := Units.ofPowEqOne v 5 power (by decide)
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨u, orderOf_eq_prime ?_ ?_⟩
  · apply Units.ext
    exact power
  · intro h
    exact ne (congrArg Units.val h)

/-- The consequences of hypothesizing a global square root can be tested on
the factor-sum interval using the public product and the norm/trace certificates. -/
theorem split_five {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (distinct : p ≠ q)
    {D a b : ZMod (p*q)} (five : (5 : ZMod (p*q)) ≠ 0) (norm : a^2-D*b^2=1)
    (trace : (2*a)^2+2*a-1=0) (sq : IsSquare D) :
    p+q ≡ p*q+1 [MOD 5 * Nat.gcd 5 (p*q-1)] := by
  obtain ⟨u,order⟩ := order_five_if_square five norm trace sq
  apply OrderDivisorSumBits.of_dvd_exponent pp.one_lt qp.one_lt
  rw [← order]
  exact OrderDivisorSumBits.unit_order_dvd pp qp distinct u

private theorem bounds_2021 {p q : ℕ} (pair : p*q=2021) (pHi : p ≤ 63) (qHi : q ≤ 63) :
    90 ≤ p+q ∧ p+q ≤ 94 := by
  have pLo : 33 ≤ p := by
    by_contra! small
    have := Nat.mul_le_mul (by omega : p ≤ 32) qHi
    omega
  have qLo : 33 ≤ q := by
    by_contra! small
    have := Nat.mul_le_mul pHi (by omega : q ≤ 32)
    omega
  zify at *
  constructor
  · by_contra! h
    nlinarith [sq_nonneg ((p:ℤ)-q), mul_nonneg (by linarith : 0 ≤ 89-(p+q:ℤ))
      (by positivity : 0 ≤ 89+(p+q:ℤ))]
  · nlinarith [mul_nonneg (by linarith : 0 ≤ (p:ℤ)-33) (by linarith : 0 ≤ (q:ℤ)-33)]

/-- Excluding a square root uses only the product, two six-bit factors, and
the earlier sixteen-class implication. Their individual values are unnecessary. -/
theorem nonsquare_2021 {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p ≠ q)
    (pair : p*q=2021) (pLo : 32 ≤ p) (pHi : p ≤ 63) (qLo : 32 ≤ q) (qHi : q ≤ 63) :
    ¬ IsSquare (-1 : ZMod 2021) := by
  intro root
  rw [← pair] at root
  have congr := OrderDivisorSumBits.square_gives_four_bits pp qp ne (by omega) (by omega) root
  rw [pair] at congr
  obtain ⟨lo,hi⟩ := bounds_2021 pair pHi qHi
  change (p+q)%16 = 2022%16 at congr
  omega

private theorem bounds_24881 {p q : ℕ} (pair : p*q=24881) (pLo : 128 ≤ p) (qLo : 128 ≤ q) :
    316 ≤ p+q ∧ p+q ≤ 322 := by
  zify at *
  constructor
  · by_contra! h
    nlinarith [sq_nonneg ((p:ℤ)-q), mul_nonneg (by linarith : 0 ≤ 315-(p+q:ℤ))
      (by positivity : 0 ≤ 315+(p+q:ℤ))]
  · nlinarith [mul_nonneg (by linarith : 0 ≤ (p:ℤ)-128) (by linarith : 0 ≤ (q:ℤ)-128)]

/-- Both signs pass the ordinary mod-16 interval test (318 and 322). The
norm-one order-five certificate makes the hypothetical square branch impossible. -/
theorem nonsquare_24881 {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p ≠ q)
    (pair : p*q=24881) (pLo : 128 ≤ p) (qLo : 128 ≤ q) :
    ¬ IsSquare (-1 : ZMod 24881) := by
  intro root
  rw [← pair] at root
  have congr := split_five pp qp ne (D := -1) (a := 15252) (b := 8047)
    (by rw [pair]; decide) (by rw [pair]; decide) (by rw [pair]; decide) root
  rw [pair] at congr
  obtain ⟨lo,hi⟩ := bounds_24881 pair pLo qLo
  change (p+q)%25 = 24882%25 at congr
  omega

theorem examples : ¬ IsSquare (-1 : ZMod 2021) ∧ ¬ IsSquare (-1 : ZMod 24881) :=
  ⟨nonsquare_2021 (p := 43) (q := 47) (by norm_num) (by norm_num) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
   nonsquare_24881 (p := 139) (q := 179) (by norm_num) (by norm_num) (by decide) (by decide)
      (by decide) (by decide)⟩

end PrimeFactors.SameSignSumWindow
