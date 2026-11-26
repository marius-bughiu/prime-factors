import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ComputeDegree
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Prime.Defs

/-! A higher Euclidean pivot for two arithmetic-progression blocks. -/
namespace PrimeFactors.BlockSubresultantProbe

open Polynomial

/-- The reciprocal coefficient list of the monic polynomial with roots
t, t±d, ..., t±hd, beginning with its leading coefficient. -/
noncomputable def head : ℕ → ℤ → ℤ → ℤ[X]
  | 0, t, _ => 1 - X*C t
  | h+1, t, d => head h t d * ((1-X*C (t-(h+1)*d))*(1-X*C (t+(h+1)*d)))

/-- The ordinary polynomial with the same specified progression of roots. -/
noncomputable def row : ℕ → ℤ → ℤ → ℤ[X]
  | 0, t, _ => X-C t
  | h+1, t, d => row h t d * ((X-C (t-(h+1)*d))*(X-C (t+(h+1)*d)))

private theorem row_degree (h : ℕ) (t d : ℤ) : (row h t d).natDegree = 2*h+1 := by
  induction h with
  | zero => exact natDegree_X_sub_C t
  | succ h ih =>
    have nz : row h t d ≠ 0 := fun e => by rw [e, natDegree_zero] at ih; omega
    rw [row, natDegree_mul nz (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
      natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), ih]
    simp only [natDegree_X_sub_C]
    omega

private theorem rev_linear (z : ℤ) : reflect 1 (X-C z) = 1-X*C z := by
  rw [reflect_sub, reflect_one_X, reflect_C]
  simp [C_mul_X_eq_monomial, mul_comm]

theorem reciprocal (h : ℕ) (t d : ℤ) : reflect (2*h+1) (row h t d) = head h t d := by
  induction h with
  | zero => exact rev_linear t
  | succ h ih =>
    rw [row, head, show 2*(h+1)+1=(2*h+1)+(1+1) by omega]
    have bound (z : ℤ) : (X-C z).natDegree ≤ 1 := (natDegree_X_sub_C _).le
    rw [reflect_mul _ _ (row_degree h t d).le
      ((natDegree_mul_le ..).trans (Nat.add_le_add (bound _) (bound _))),
      reflect_mul _ _ (bound _) (bound _), ih, rev_linear, rev_linear]

private theorem head_succ (h : ℕ) (t d : ℤ) :
    let f := head h t d
    head (h+1) t d = f - (f*X)*C (2*t) + (f*X*X)*C (t^2-((h+1)*d)^2) := by
  dsimp only
  rw [head]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
  ring

/-- The first four actual coefficients. Multiplication by 24 avoids all division. -/
theorem coefficients (h : ℕ) (t d : ℤ) :
    let m : ℤ := 2*h+1
    let f := head h t d
    f.coeff 0 = 1 ∧ f.coeff 1 = -m*t ∧
    24*f.coeff 2 = 12*m*(m-1)*t^2-m*(m^2-1)*d^2 ∧
    24*f.coeff 3 = -4*m*(m-1)*(m-2)*t^3+(m-2)*m*(m^2-1)*d^2*t := by
  dsimp only
  induction h with
  | zero => simp [head, coeff_sub, coeff_mul_C, coeff_X, coeff_one]
  | succ h ih =>
    obtain ⟨h0,h1,h2,h3⟩ := ih
    rw [head_succ]
    simp only [coeff_add,coeff_sub,coeff_mul_C,coeff_mul_X_zero,coeff_mul_X,
      h0,h1, Nat.cast_succ]
    constructor
    · ring
    constructor
    · ring
    constructor
    · linear_combination h2
    · linear_combination h3-2*t*h2

/-- In reciprocal coordinates the two virtual eliminations make an X³
coefficient. The extra X clears the shift from a degree-m row to a degree-(m−1) row. -/
noncomputable def eliminated (f g : ℤ[X]) : ℤ[X] :=
  let u := (f-g).coeff 1
  let v := (f-g).coeff 2
  X*C (u^2)*f - (C u-X*C v)*(f-g)

private theorem elim_coeff (f g : ℤ[X]) (f0 : f.coeff 0=1) (g0 : g.coeff 0=1)
    (f1 : f.coeff 1=0) :
    let u := (f-g).coeff 1
    let v := (f-g).coeff 2
    let w := (f-g).coeff 3
    let e := eliminated f g
    e.coeff 0=0 ∧ e.coeff 1=0 ∧ e.coeff 2=0 ∧ e.coeff 3=u^2*f.coeff 2-u*w+v^2 := by
  dsimp only [eliminated]
  rw [show X*C ((f-g).coeff 1^2)*f - (C ((f-g).coeff 1)-X*C ((f-g).coeff 2))*(f-g) =
      (f*X)*C ((f-g).coeff 1^2) - (f-g)*C ((f-g).coeff 1) + ((f-g)*X)*C ((f-g).coeff 2) by ring]
  simp only [coeff_add, coeff_sub, coeff_mul_C, coeff_mul_X_zero, coeff_mul_X, f0, g0, f1]
  constructor <;> [ring; constructor <;> [ring; constructor <;> ring]]

/-- The normalized test for an m by m rectangle with fine stride 1 and coarse
stride m. Both strides and the shift are public. -/
def probe (m t : ℤ) := 48*t^4 - 24*(1+m^2)*t^2 + (m^2-1)^3

/-- An identity over the integers for the actual reciprocal elimination coefficient.
It remains valid after reduction modulo any positive integer. For m≥3 the 3-index
here is the coefficient of X^(m−2) in the ordinary pseudo-remainder. -/
theorem rectangle_pivot (h : ℕ) (t : ℤ) :
    let m : ℤ := 2*h+1
    let f := head h 0 1
    let g := head h t m
    let e := eliminated f g
    e.coeff 0=0 ∧ e.coeff 1=0 ∧ e.coeff 2=0 ∧
      576 * e.coeff 3 = m^2*(m^2-1)*probe m t := by
  dsimp only
  let m : ℤ := 2*h+1
  let f := head h 0 1
  let g := head h t m
  have a := coefficients h 0 1
  have b := coefficients h t m
  change f.coeff 0=1 ∧ f.coeff 1= -m*0 ∧ 24*f.coeff 2=_ ∧ 24*f.coeff 3=_ at a
  change g.coeff 0=1 ∧ g.coeff 1= -m*t ∧ 24*g.coeff 2=_ ∧ 24*g.coeff 3=_ at b
  obtain ⟨f0,f1,f2,f3⟩ := a
  obtain ⟨g0,g1,g2,g3⟩ := b
  change 24*f.coeff 2=12*m*(m-1)*0^2-m*(m^2-1)*1^2 at f2
  change 24*f.coeff 3= -4*m*(m-1)*(m-2)*0^3+(m-2)*m*(m^2-1)*1^2*0 at f3
  change 24*g.coeff 2=12*m*(m-1)*t^2-m*(m^2-1)*m^2 at g2
  change 24*g.coeff 3= -4*m*(m-1)*(m-2)*t^3+(m-2)*m*(m^2-1)*m^2*t at g3
  norm_num only [mul_zero, zero_pow, one_pow, mul_one, zero_sub, add_zero] at f1 f2 f3
  obtain ⟨z0,z1,z2,e⟩ := elim_coeff f g f0 g0 f1
  refine ⟨z0,z1,z2,?_⟩
  change 576*(eliminated f g).coeff 3 = m^2*(m^2-1)*probe m t
  rw [e]
  simp only [coeff_sub, f1, g1, zero_sub, neg_mul, neg_neg, probe]
  have sq := congrArg (·^2) (congrArg₂ HSub.hSub f2 g2)
  dsimp only at sq
  linear_combination sq + 24*(m*t)^2*f2 - 24*(m*t)*(f3-g3)

/-- The four rows of the (m−2)-nd principal Sylvester minor, for two monic
degree-m polynomials. Subtracting rows of equal shift gives the displayed expression. -/
theorem principal_minor {R : Type*} [CommRing R] (a b c d e f : R) :
    Matrix.det !![1,a,b,c; 0,1,a,b; 1,d,e,f; 0,1,d,e] =
      (b-e)^2-(a-d)*(c-f)-a*(a-d)*(b-e)+b*(a-d)^2 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp [Matrix.det_fin_three, Matrix.submatrix,
    show (1:Fin 4).succAbove (2:Fin 3)=3 by decide,
    show (2:Fin 4).succAbove (1:Fin 3)=1 by decide,
    show (2:Fin 4).succAbove (2:Fin 3)=3 by decide,
    show (3:Fin 4).succAbove (1:Fin 3)=1 by decide,
    show (3:Fin 4).succAbove (2:Fin 3)=2 by decide,
    show ((3:Fin 4):ℕ)=3 by decide]
  ring

/-- With leading coefficients read from the actual rows, the determinant and
the Euclidean coefficient are identical before reducing modulo a prime. -/
theorem determinant_is_pivot (f g : ℤ[X]) (f0 : f.coeff 0=1) (g0 : g.coeff 0=1)
    (f1 : f.coeff 1=0) :
    Matrix.det !![1, f.coeff 1, f.coeff 2, f.coeff 3;
      0, 1, f.coeff 1, f.coeff 2; 1, g.coeff 1, g.coeff 2, g.coeff 3;
      0, 1, g.coeff 1, g.coeff 2] = (eliminated f g).coeff 3 := by
  rw [principal_minor, (elim_coeff f g f0 g0 f1).2.2.2]
  simp only [coeff_sub, f1]
  ring

/-- In any field of characteristic different from 2 and 3 the normalized
higher-minor probe covers at most four shifts at a fixed prime and width. -/
theorem shift_count {R : Type*} [Field R] (good : (48 : R) ≠ 0) (m : R) (S : Finset R)
    (hit : ∀ t ∈ S, 48*t^4 - 24*(1+m^2)*t^2 + (m^2-1)^3 = 0) : S.card ≤ 4 := by
  let f : R[X] := C 48*X^4-C (24*(1+m^2))*X^2+C ((m^2-1)^3)
  have degree : f.natDegree = 4 := by
    dsimp [f]
    compute_degree!
  have nz : f ≠ 0 := fun h => by rw [h, natDegree_zero] at degree; contradiction
  rw [← degree]
  apply card_le_degree_of_subset_roots
  intro t ht
  apply (mem_roots nz).2
  simpa [f,IsRoot] using hit t ht

/-- The simplest instance also has the stated quadratic norm form. -/
theorem three (t : ℤ) :
    probe 3 t=16*(3*t^4-15*t^2+32) ∧
      12*(3*t^4-15*t^2+32)=(6*t^2-15)^2+159 := by
  constructor
  · unfold probe; ring
  · ring

noncomputable def nine (t : ℤ) : ℤ := ((List.range 9).map (fun i => t-4+i)).prod

/-- Every rectangle entry and the first leading coefficient are invertible;
the second leading coefficient yields a certified prime split. -/
theorem five_example :
    Int.gcd (nine 5) 153583=1 ∧ Int.gcd 15 153583=1 ∧
    Int.gcd (2*(3*5^4-15*5^2+32)) 153583=383 ∧
    Nat.Prime 383 ∧ Nat.Prime 401 ∧ 383*401=(153583:ℕ) := by decide +kernel

/-- The shift in this ordinary finite-panel example is the integer square
root of the product. Including the adjacent smaller position still misses. -/
theorem product_example :
    let n : ℕ := 157601
    let t : ℤ := n.sqrt
    t=396 ∧ Int.gcd (nine t) n=1 ∧ Int.gcd (3*t) n=1 ∧ Int.gcd (t-5) n=1 ∧
    Int.gcd (probe 3 t) n=439 ∧ Nat.Prime 359 ∧ Nat.Prime 439 ∧ 359*439=n := by
  have root : (157601:ℕ).sqrt=396 := by
    have h := Nat.sqrt_lt'.mpr (by decide : 157601 < 397^2)
    have l := Nat.le_sqrt'.mpr (by decide : 396^2 ≤ 157601)
    omega
  simp only [root]
  decide +kernel

/-- All four shifts can occur at one prime, disjointly from the original
nine-position rectangle. -/
theorem four_clean : ∀ i : Fin 43,
    (43 ∣ probe 3 i.val ↔ i.val=11 ∨ i.val=20 ∨ i.val=23 ∨ i.val=32) ∧
    (43 ∣ probe 3 i.val → Int.gcd (nine i.val) 43=1) := by decide +kernel

end PrimeFactors.BlockSubresultantProbe
