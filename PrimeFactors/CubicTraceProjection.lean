import PrimeFactors.CubicTraceSquare
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.ZMod
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The divided difference of a monic cubic gives a public trace selecting the
residue of a specified root. The matrix identities in the shifted power basis
`1, α−m, (α−m)²` hold over any commutative ring. The final results specialize
to algebraic square roots, modular gcds, and integer roots of the trace quartic. -/
namespace PrimeFactors.CubicTraceProjection

variable {R : Type*} [CommRing R]

abbrev Mat (R : Type*) := Matrix (Fin 3) (Fin 3) R

def cubic (c₀ c₁ c₂ x : R) := x^3+c₂*x^2+c₁*x+c₀
def derivative (c₁ c₂ m : R) := 3*m^2+2*c₂*m+c₁
def evaluation (x y z m : R) := x+y*m+z*m^2

/-- The polynomial used by the search contains only public coefficients. -/
def dividedDifference (c₁ c₂ m x : R) := x^2+(m+c₂)*x+(m^2+c₂*m+c₁)

theorem divided_difference (c₀ c₁ c₂ m x : R) :
    (x-m)*dividedDifference c₁ c₂ m x = cubic c₀ c₁ c₂ x-cubic c₀ c₁ c₂ m := by
  unfold dividedDifference cubic
  ring

theorem divided_shift (c₁ c₂ m h : R) :
    dividedDifference c₁ c₂ m (m+h) = h^2+(3*m+c₂)*h+derivative c₁ c₂ m := by
  unfold dividedDifference derivative
  ring

/-- If `n=f(m)`, `b=3m+c₂` and `c=f'(m)` then the defining polynomial of
`h=α−m` is `h³+b h²+c h+n`. -/
theorem shift (c₀ c₁ c₂ m h : R) :
    cubic c₀ c₁ c₂ (m+h) = h^3+(3*m+c₂)*h^2+derivative c₁ c₂ m*h+cubic c₀ c₁ c₂ m := by
  unfold cubic derivative
  ring

/-- Matrix of multiplication by `h`, in columns. -/
noncomputable def companion (b c n : R) : Mat R := !![0,0,-n; 1,0,-c; 0,1,-b]

/-- Multiplication by `x+y*h+z*h²`. -/
noncomputable def action (b c n x y z : R) : Mat R :=
  x • 1 + y • companion b c n + z • (companion b c n * companion b c n)

/-- `G=(f(X)−f(m))/(X−m)` in the shifted basis is `h²+b h+c`. -/
noncomputable def projector (b c n : R) : Mat R := !![c,-n,0; b,0,-n; 1,0,0]

private theorem action_entries (b c n x y z : R) : action b c n x y z =
    !![x,-n*z,-n*y+b*n*z; y,x-c*z,-c*y+(b*c-n)*z; z,y-b*z,x-b*y+(b^2-c)*z] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [action, companion, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

/-- The displayed projector is the actual quadratic in the companion matrix. -/
theorem projector_action (b c n : R) : projector b c n = action b c n c b 1 := by
  rw [action_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [projector] <;> ring

/-- Multiplication by the projector has norm `f(m)²`, even at a ramified prime. -/
theorem norm_projector (b c n : R) : (projector b c n).det = n^2 := by
  simp [projector, Matrix.det_fin_three]
  ring

/-- Multiplying the candidate by `G²` changes its norm by the known fourth power. -/
theorem masked_norm (b c n : R) (β : Mat R) :
    ((projector b c n)^2 * β).det = n^4 * β.det := by
  rw [Matrix.det_mul, Matrix.det_pow, norm_projector]
  ring

/-- The adjugate is divisible by `n` entry by entry. This gives a second
power of `n` in the middle characteristic coefficient after squaring `G`. -/
theorem projector_adjugate (b c n : R) :
    (projector b c n).adjugate=(-n) • companion b c n := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [projector, companion]
  ring

/-- For a 3-by-3 matrix the middle elementary symmetric coefficient is the
trace of the adjugate. -/
theorem characteristic_three (M : Mat R) : M.charpoly = Polynomial.X^3 -
    Polynomial.C M.trace * Polynomial.X^2 + Polynomial.C M.adjugate.trace * Polynomial.X -
    Polynomial.C M.det := by
  rw [Matrix.charpoly, Matrix.det_fin_three, Matrix.adjugate_fin_three, Matrix.det_fin_three M]
  simp [Matrix.trace_fin_three, Matrix.charmatrix_apply, Matrix.diagonal_apply]
  ring

theorem masked_middle (b c n : R) (β : Mat R) :
    (((projector b c n)^2 * β).adjugate).trace =
      n^2 * (β.adjugate * ((companion b c n)^2)).trace := by
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_pow, projector_adjugate]
  simp [pow_two, smul_smul]

/-- The leading elementary symmetric coefficient of the masked candidate.
The error from `f'(m)²β(m)` is visibly a multiple of `f(m)`. -/
theorem masked_trace (b c n x y z : R) :
    ((projector b c n)^2 * action b c n x y z).trace =
      c^2*x - n*(2*b*x+c*y-3*n*z) := by
  rw [action_entries, pow_two, Matrix.trace_fin_three]
  simp [projector, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- The exact integral trace for coordinates in the shifted power basis. -/
theorem shifted_trace (b c n x y z : R) :
    (projector b c n * action b c n x y z).trace = c*x-n*(3*y-b*z) := by
  rw [action_entries, Matrix.trace_fin_three]
  simp [projector, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- Clear a coordinate denominator `D`. Here `(x,y,z)` are the coefficients
of the numerator in the original unshifted power basis, `P(X)=x+yX+zX²`. -/
theorem denominator_trace (c₀ c₁ c₂ m x y z D : R) (δ : Mat R)
    (coordinates : D • δ = action (3*m+c₂) (derivative c₁ c₂ m) (cubic c₀ c₁ c₂ m)
      (evaluation x y z m) (y+2*m*z) z) :
    D*(projector (3*m+c₂) (derivative c₁ c₂ m) (cubic c₀ c₁ c₂ m)*δ).trace =
      derivative c₁ c₂ m*evaluation x y z m-cubic c₀ c₁ c₂ m*(3*y+(3*m-c₂)*z) := by
  change D • (projector _ _ _ * δ).trace = _
  rw [←Matrix.trace_smul, ←Matrix.mul_smul, coordinates, shifted_trace]
  ring

/-- At a root of `f`, multiplying by `G` retains only the constant term of
the shifted coordinates. No separability assumption is needed. -/
theorem selected_matrix (b c x y z : R) :
    projector b c 0 * action b c 0 x y z = x • projector b c 0 := by
  rw [action_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [projector, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem square_matrix (b c x y z : R) :
    (projector b c 0)^2 * action b c 0 x y z = (x*c) • projector b c 0 := by
  have id : projector b c 0 * projector b c 0 = c • projector b c 0 := by
    conv_lhs => arg 2; rw [projector_action]
    exact selected_matrix b c c b 1
  rw [pow_two, mul_assoc, selected_matrix, Matrix.mul_smul, id, smul_smul]

/-- If the selected square value times the squared derivative is nonzero,
the masked element cannot be scalar, even modulo the input. -/
theorem nonscalar (b c x y z : R) (nz : x*c^2≠0) (k : R) :
    (projector b c 0)^2 * action b c 0 x y z ≠ k • 1 := by
  rw [square_matrix]
  intro eq
  have zero := congrArg (fun (M : Mat R) => M 2 2) eq
  have main := congrArg (fun (M : Mat R) => M 0 0) eq
  simp [projector, Matrix.one_apply] at zero main
  exact nz (by rw [pow_two, ←mul_assoc, main, zero])

private theorem scaled_charpoly (b c x : R) : (x • projector b c 0).charpoly =
    Polynomial.X^2*(Polynomial.X-Polynomial.C (x*c)) := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, projector]
  ring

/-- The characteristic polynomial of multiplication by `G²β` at a residue
root, with `β(m)=z₀²`. Only the one distinguished value appears. -/
theorem square_charpoly (b c x y z z₀ : R) (squareValue : x=z₀^2) :
    ((projector b c 0)^2 * action b c 0 x y z).charpoly =
      Polynomial.X^2*(Polynomial.X-Polynomial.C (c^2*z₀^2)) := by
  rw [square_matrix, scaled_charpoly, squareValue]
  ring_nf

section BasedAlgebra

open Module
variable {S : Type*} [CommRing S] [Algebra R S]

/-- `x + y*h + z*h²`, with all coefficients in the base ring. -/
def element (h : S) (x y z : R) : S := x • 1 + y • h + z • (h*h)

/-- The companion matrix follows from the three basis columns and the given
monic cubic relation, over a field or an integral order. -/
theorem companion_of_basis (e : Basis (Fin 3) R S) (h : S) (b c n : R)
    (e₀ : e 0 = 1) (e₁ : e 1=h) (e₂ : e 2=h*h)
    (relation : h*(h*h)=(-n) • (1:S)+(-c) • h+(-b) • (h*h)) :
    Algebra.leftMulMatrix e h=companion b c n := by
  have col₀ : h*e 0=e 1 := by rw [e₀,e₁,mul_one]
  have col₁ : h*e 1=e 2 := by rw [e₁,e₂]
  have col₂ : h*e 2=(-n) • e 0+(-c) • e 1+(-b) • e 2 := by rw [e₂,e₀,e₁,relation]
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases j <;> fin_cases i <;>
    simp [col₀,col₁,col₂,companion, Finsupp.single_apply]

private theorem element_action (e : Basis (Fin 3) R S) (h : S) (b c n : R)
    (columns : Algebra.leftMulMatrix e h=companion b c n) (x y z : R) :
    Algebra.leftMulMatrix e (element h x y z)=action b c n x y z := by
  simp [element, action, columns]

/-- The actual algebra norm of the divided difference, as opposed to a
characteristic root chosen by a decoder. -/
theorem algebra_norm (e : Basis (Fin 3) R S) (h : S) (b c n : R)
    (columns : Algebra.leftMulMatrix e h=companion b c n) :
    Algebra.norm R (element h c b 1)=n^2 := by
  rw [Algebra.norm_eq_matrix_det e, element_action e h b c n columns, ←projector_action,
    norm_projector]

/-- Actual algebra trace of `G*δ`, with a cleared coordinate denominator. -/
theorem algebra_trace (e : Basis (Fin 3) R S) (h δ : S) (c₀ c₁ c₂ m x y z D : R)
    (columns : Algebra.leftMulMatrix e h=companion (3*m+c₂) (derivative c₁ c₂ m) (cubic c₀ c₁ c₂ m))
    (coords : D • δ=element h (evaluation x y z m) (y+2*m*z) z) :
    D*Algebra.trace R S (element h (derivative c₁ c₂ m) (3*m+c₂) 1*δ) =
      derivative c₁ c₂ m*evaluation x y z m-cubic c₀ c₁ c₂ m*(3*y+(3*m-c₂)*z) := by
  have act := element_action e h _ _ _ columns
  rw [Algebra.trace_eq_matrix_trace e, map_mul, act, ←projector_action]
  apply denominator_trace
  rw [←map_smul, coords, act]

end BasedAlgebra

/-- In the cubic field a nonzero projector preserves exactly which candidates
are squares, so a successful masked relation still tests the original event. -/
theorem mask_square_iff {K : Type*} [Field K] (g β : K) (ng : g≠0) :
    IsSquare (g^2*β) ↔ IsSquare β := by
  rw [isSquare_iff_exists_sq, isSquare_iff_exists_sq]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v/g, ?_⟩
    rw [div_pow, eq_div_iff (pow_ne_zero 2 ng), mul_comm]
    exact hv
  · rintro ⟨v, rfl⟩
    exact ⟨g*v, (mul_pow ..).symm⟩

/-- With unit derivative and unit denominator the projected trace gives exactly
the gcd of the direct square-root comparison, for either choice of `z`. -/
theorem projection_gcd {N : ℕ} [NeZero N] (D c : (ZMod N)ˣ) (U P z : ZMod N)
    (projected : (D : ZMod N)*U=(c : ZMod N)*P) :
    (U-(c : ZMod N)*z).val.gcd N = (P-(D : ZMod N)*z).val.gcd N := by
  rw [←maskedRelations_unit_gcd D U ((c : ZMod N)*z),
    ←maskedRelations_unit_gcd c P ((D : ZMod N)*z), projected, mul_left_comm]

/-- After reduction, `B=w=0` and the quartic becomes `(U²−(c z)²)²`.
On squarefree inputs a root is necessarily a square root of `(c z)²`,
including when no usable denominator is known for the direct readout. -/
theorem quartic_mod_squarefree {N : ℕ} (sqf : Squarefree N) (U c z : ZMod N)
    (root : CubicTraceSquare.quartic ((c*z)^2) 0 0 U=0) : U^2=(c*z)^2 := by
  letI : Fact (Squarefree N) := ⟨sqf⟩
  apply sub_eq_zero.mp
  apply (IsReduced.pow_eq_zero_iff (by decide : 2 ≠ 0)).mp
  simpa [CubicTraceSquare.quartic] using root

/-- A projected trace with neither global sign gives a proper gcd; no
factorization, inversion or knowledge of the three conjugates is required. -/
theorem quartic_split {N : ℕ} [NeZero N] (sqf : Squarefree N) (U c z : ZMod N)
    (root : CubicTraceSquare.quartic ((c*z)^2) 0 0 U=0)
    (plus : U≠c*z) (minus : U≠-(c*z)) :
    1 < (U-c*z).val.gcd N ∧ (U-c*z).val.gcd N < N :=
  maskedRelations_split (quartic_mod_squarefree sqf U c z root) plus minus

/-- Integer roots of the actual masked quartic give the projected square
congruence even for nonsquarefree moduli. This uses the stronger `n²`
divisibility of both `w′` and the middle coefficient. -/
theorem integer_quartic (b c n x y z w U : ℤ)
    (root : let M := (projector b c n)^2 * action b c n x y z
      CubicTraceSquare.quartic M.trace M.adjugate.trace (n^2*w) U=0) :
    n ∣ U^2-c^2*x := by
  dsimp only at root
  rw [masked_middle, CubicTraceSquare.quartic] at root
  have dv : n ∣ U^2-((projector b c n)^2 * action b c n x y z).trace := by
    apply (Int.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    refine ⟨8*w*U+4*((action b c n x y z).adjugate * (companion b c n)^2).trace, ?_⟩
    linear_combination root
  rw [masked_trace] at dv
  obtain ⟨k, hk⟩ := dv
  refine ⟨k-(2*b*x+c*y-3*n*z), ?_⟩
  linear_combination hk

/-- The sampled cubic may evaluate to *any* multiple `n` of the factoring
input `N`. A rational square congruence is enough at the selected place. -/
theorem integer_projection_congruence (b c n N x y z w U z₀ : ℤ) (base : N ∣ n)
    (value : N ∣ x-z₀^2) (root : let M := (projector b c n)^2 * action b c n x y z
      CubicTraceSquare.quartic M.trace M.adjugate.trace (n^2*w) U=0) :
    N ∣ U^2-(c*z₀)^2 := by
  obtain ⟨j, hj⟩ := base.trans (integer_quartic b c n x y z w U root)
  obtain ⟨k, hk⟩ := value
  refine ⟨j+c^2*k, ?_⟩
  linear_combination hj + c^2*hk

/-- Concrete trace for the previously checked square root `7−2α` with
`α³=11`, `m=10`, and rational square root `56` from the three row product. -/
theorem projected_989 :
    (projector (30:ℤ) 300 989 * action 30 300 989 (-13) (-2) 0).trace=2034 ∧
    (2034-300*56:ℤ).natAbs.gcd 989=23 ∧ (2034+300*56:ℤ).natAbs.gcd 989=43 := by
  rw [shifted_trace]
  decide +kernel

end PrimeFactors.CubicTraceProjection
