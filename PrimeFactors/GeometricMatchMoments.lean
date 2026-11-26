import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The first two moments of an arithmetic progression, read from the highest
coefficients of its scaled root polynomial. All identities clear denominators. -/

namespace PrimeFactors.GeometricMatchMoments
open Finset Polynomial
variable {R : Type*} [CommRing R]

/-- The product of labeled linear terms over the first `r` indices. -/
noncomputable def rootPolynomial (f : ℕ → R) (r : ℕ) : R[X] :=
  ∏ i ∈ range r, (X - C (f i))

private theorem extend (f : ℕ → R) (r : ℕ) :
    rootPolynomial f (r+1) = rootPolynomial f r * (X - C (f r)) := by
  simp only [rootPolynomial, prod_range_succ]

private theorem top (f : ℕ → R) (r : ℕ) : (rootPolynomial f r).coeff r = 1 ∧
    ∀ t, r < t → (rootPolynomial f r).coeff t = 0 := by
  induction r with
  | zero =>
    constructor
    · simp [rootPolynomial]
    · intro t ht
      simp [rootPolynomial, Polynomial.coeff_one, Nat.ne_of_gt ht]
  | succ r ih =>
    rw [extend]
    constructor
    · rw [Polynomial.coeff_mul_X_sub_C, ih.1, ih.2 _ (by omega), zero_mul, sub_zero]
    · intro t ht
      obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
      rw [Polynomial.coeff_mul_X_sub_C, ih.2 u (by omega), ih.2 _ (by omega), zero_mul, sub_zero]

/-- The sign of the first coefficient and the factor of two in Newton's
second identity hold also in rings of small characteristic. -/
theorem coefficients (f : ℕ → R) (m : ℕ) :
    let r := m+2
    (rootPolynomial f r).coeff (m+1) = -(∑ i ∈ range r, f i) ∧
    2 * (rootPolynomial f r).coeff m = (∑ i ∈ range r, f i)^2 - ∑ i ∈ range r, (f i)^2 := by
  dsimp only
  induction m with
  | zero =>
    constructor <;> simp [rootPolynomial, prod_range_succ, sum_range_succ, mul_sub, Polynomial.coeff_mul_X,
      Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C] <;> ring
  | succ m ih =>
    obtain ⟨first, second⟩ := ih
    rw [show m+1+2=m+2+1 by omega, extend, Polynomial.coeff_mul_X_sub_C,
      Polynomial.coeff_mul_X_sub_C, first, (top f (m+2)).1]
    simp only [sum_range_succ (n := m+2), one_mul]
    constructor
    · ring
    · linear_combination second

/-- The usual mean and second moment identities with their denominators cleared. -/
theorem moments (a d : R) (r : ℕ) :
    2 * (∑ i ∈ range r, (a + (i:R)*d)) = (r:R)*(2*a+((r:R)-1)*d) ∧
    6 * (∑ i ∈ range r, (a + (i:R)*d)^2) =
      (r:R)*(6*a^2+6*a*((r:R)-1)*d+((r:R)-1)*(2*(r:R)-1)*d^2) := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [sum_range_succ, Nat.cast_succ]
    constructor
    · linear_combination ih.1
    · linear_combination ih.2

/-- Twelve times the (unnormalized) variance reads the square of the period. -/
theorem variance (a d : R) (r : ℕ) :
    12 * ((r:R) * (∑ i ∈ range r, (a+(i:R)*d)^2) - (∑ i ∈ range r, (a+(i:R)*d))^2) =
      (r:R)^2*((r:R)^2-1)*d^2 := by
  obtain ⟨first, second⟩ := moments a d r
  linear_combination 2*(r:R)*second -
    3*(2*(∑ i ∈ range r, (a+(i:R)*d)) + (r:R)*(2*a+((r:R)-1)*d))*first

/-- For multiplicity `m+2`, these readouts use the three leading coefficients
of the observed polynomial. The multiplier on the period square is explicit. -/
theorem readout (u a d : R) (m : ℕ) :
    let r := m+2
    let F := C u * rootPolynomial (fun i => a+(i:R)*d) r
    let A := F.coeff r
    let B := F.coeff (m+1)
    let C₂ := F.coeff m
    A = u ∧ -2*B = (r:R)*A*(2*a+((r:R)-1)*d) ∧
      12*(((r:R)-1)*B^2-2*(r:R)*A*C₂) = (r:R)^2*((r:R)^2-1)*A^2*d^2 := by
  dsimp only
  obtain ⟨first, second⟩ := coefficients (fun i => a+(i:R)*d) m
  simp only [Polynomial.coeff_C_mul, (top (fun i => a+(i:R)*d) (m+2)).1, mul_one, first]
  obtain ⟨mean, _⟩ := moments a d (m+2)
  have var := variance a d (m+2)
  constructor
  · trivial
  constructor
  · linear_combination u*mean
  · linear_combination u^2*var - 12*((m+2:ℕ):R)*u^2*second

/-- The true label is `a+t*d` when its rank among the matches is `t`.
This is the signed first-coefficient equation at that rank. -/
theorem at_rank {r A B a d j t : R} (mean : -2*B = r*A*(2*a+(r-1)*d))
    (rank : j = a+t*d) : -2*B-2*r*A*j = r*A*(r-1-2*t)*d := by
  rw [mean, rank]
  ring

/-- Perturb the public target to `y(1+zX)` and the base to `g(1+X)`.
No truncation is needed to obtain the first nonzero coefficient. -/
noncomputable def directionalFactor (y g z : R) (i : ℕ) : R[X] :=
  C y + C (y*z) * X - C (g^i) * (1+X)^i

private theorem constant_linear (y g z : R) (i : ℕ) :
    (directionalFactor y g z i).coeff 0 = y-g^i ∧
    (directionalFactor y g z i).coeff 1 = y*z-g^i*(i:R) := by
  simp only [directionalFactor, coeff_sub, coeff_add, coeff_C_mul_X, coeff_C_mul,
    coeff_C, coeff_one_add_X_pow]
  simp

/-- Each specified zero contributes one factor of the perturbation parameter.
At precisely that many derivatives, every choice of higher coefficients drops out. -/
theorem first_product_coefficient {S H : Finset ℕ} (inside : H ⊆ S) (f : ℕ → R[X])
    (zero : ∀ i ∈ H, (f i).coeff 0 = 0) :
    (∀ k < H.card, (∏ i ∈ S, f i).coeff k = 0) ∧
    (∏ i ∈ S, f i).coeff H.card =
      (∏ i ∈ S \ H, (f i).coeff 0) * ∏ i ∈ H, (f i).coeff 1 := by
  have hits : (∏ i ∈ H, f i) = (∏ i ∈ H, (f i).divX) * X^H.card := by
    calc
      _ = ∏ i ∈ H, (f i).divX * X := by
        apply prod_congr rfl
        intro i hi
        simpa only [zero i hi, map_zero, add_zero] using (divX_mul_X_add (f i)).symm
      _ = _ := by rw [prod_mul_distrib, prod_const]
  have split : (∏ i ∈ S, f i) = ((∏ i ∈ S \ H, f i) * ∏ i ∈ H, (f i).divX) * X^H.card := by
    rw [← prod_sdiff (f := f) inside, hits, mul_assoc]
  constructor
  · intro k hk
    rw [split, coeff_mul_X_pow', if_neg (by omega)]
  · rw [split, coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero]
    simp only [Polynomial.eval_mul, Polynomial.eval_prod, ← Polynomial.coeff_zero_eq_eval_zero,
      coeff_divX, zero_add]

/-- The order-|H| directional coefficient as a function of `z` is a scaled
root polynomial in the actual index labels. If some other term also vanishes,
the scalar is zero. The formula is valid over an arbitrary commutative ring. -/
theorem directional_reading {S H : Finset ℕ} (inside : H ⊆ S) (y g z : R)
    (hit : ∀ i ∈ H, g^i = y) :
    (∏ i ∈ S, directionalFactor y g z i).coeff H.card =
      ((∏ i ∈ S \ H, (y-g^i)) * y^H.card) * ∏ i ∈ H, (z-(i:R)) := by
  have h := (first_product_coefficient inside (directionalFactor y g z)
    (fun i hi => by rw [(constant_linear y g z i).1, hit i hi, sub_self])).2
  rw [h]
  simp only [(constant_linear y g z _).1, (constant_linear y g z _).2]
  have each : (∏ i ∈ H, (y*z-g^i*(i:R))) = y^H.card * ∏ i ∈ H, (z-(i:R)) := by
    rw [← prod_const (s := H) y, ← prod_mul_distrib]
    apply prod_congr rfl
    intro i hi
    rw [hit i hi, mul_sub]
  rw [each, mul_assoc]

/-- With a public indeterminate `Z`, the leading directional reading is an
identity of polynomials in `Z`, even over a small finite field. The `r`
specified indices are the consecutive arithmetic progression `a+i*d`. -/
theorem progression_reading {S : Finset ℕ} {a d r : ℕ} (step : 0 < d) (y g : R)
    (inside : ∀ i < r, a+i*d ∈ S) (hit : ∀ i < r, g^(a+i*d) = y) :
    let H := (range r).image (fun i => a+i*d)
    (∏ i ∈ S, directionalFactor (C y) (C g) (X : R[X]) i).coeff r =
      C ((∏ i ∈ S \ H, (y-g^i)) * y^r) *
        rootPolynomial (fun i => (a:R)+(i:R)*(d:R)) r := by
  let H := (range r).image (fun i => a+i*d)
  have inj : Function.Injective (fun i : ℕ => a+i*d) := by
    intro i j e
    exact Nat.eq_of_mul_eq_mul_right step (Nat.add_left_cancel e)
  have card : H.card = r := by simp only [H, card_image_of_injective _ inj, card_range]
  have sub : H ⊆ S := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ht
    exact inside i (mem_range.mp hi)
  have h := directional_reading sub (C y) (C g) (X : R[X]) (by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ht
    rw [← map_pow, hit i (mem_range.mp hi)])
  rw [card] at h
  rw [h]
  have product : (∏ i ∈ H, (X - (i:R[X]))) = rootPolynomial (fun i => (a:R)+(i:R)*(d:R)) r := by
    dsimp only [H]
    rw [prod_image (fun _ _ _ _ e => inj e)]
    simp [rootPolynomial, Nat.cast_add, Nat.cast_mul]
  rw [product]
  simp only [H, map_mul, map_prod, map_sub, map_pow]

end PrimeFactors.GeometricMatchMoments
