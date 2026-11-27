import PrimeFactors.ToySumIsolation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.ComputeDegree

/-! Applying the same polynomial to both local factors maps every admissible
pair to a new admissible pair. The transformed test may therefore be redundant
or weaker at that same modulus. -/
namespace PrimeFactors.PolynomialSumFilters

open Polynomial
variable {R : Type*} [CommRing R]

/-- Both factors are roots of this monic polynomial over the residue ring. -/
noncomputable def quadratic (n s : R) : R[X] := X^2 - (C s*X - C n)

private theorem low_degree (n s : R) : (C s*X-C n).degree < (2 : WithBot ℕ) := by
  have low : (C s*X-C n).degree ≤ (1 : WithBot ℕ) := by compute_degree
  exact low.trans_lt (by decide : (1 : WithBot ℕ) < 2)

private theorem monic_quadratic (n s : R) : (quadratic n s).Monic := by
  exact monic_X_pow_sub (low_degree n s)

/-- Coefficients of the canonical remainder, in slope and constant order. -/
noncomputable def reduced (n s : R) (f : R[X]) : R × R :=
  let r := f %ₘ quadratic n s
  (r.coeff 1, r.coeff 0)

theorem remainder (n s : R) (f : R[X]) :
    f %ₘ quadratic n s = C (reduced n s f).1*X + C (reduced n s f).2 := by
  have dg : (quadratic n s).degree ≤ (2:ℕ) := by unfold quadratic; compute_degree; decide
  have h := sum_modByMonic_coeff (p:=f) (monic_quadratic n s) dg
  simpa [Fin.sum_univ_two, reduced, ← C_mul_X_pow_eq_monomial, add_comm] using h.symm

/-- Evaluating at either root uses only the affine remainder. -/
theorem eval_root {n s x : R} (f : R[X]) (root : x^2-s*x+n=0) :
    f.eval x = (reduced n s f).1*x+(reduced n s f).2 := by
  have zero : (quadratic n s).eval x = 0 := by
    simp only [quadratic, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
    linear_combination root
  have eq := congrArg (Polynomial.eval x) (f.modByMonic_add_div (monic_quadratic n s))
  simpa only [eval_add, eval_mul, zero, zero_mul, add_zero, remainder, eval_C, eval_X] using eq.symm

def imageSum (s u v : R) := u*s+2*v
def imageProduct (n s u v : R) := u^2*n+u*v*s+v^2

/-- Public trace and product of the two transformed roots. -/
theorem transformed_pair {n s x y : R} (f : R[X]) (prod : x*y=n) (sum : x+y=s) :
    f.eval x + f.eval y = imageSum s (reduced n s f).1 (reduced n s f).2 ∧
    f.eval x * f.eval y = imageProduct n s (reduced n s f).1 (reduced n s f).2 := by
  subst n s
  rw [eval_root f (show x^2-(x+y)*x+x*y=0 by ring),
    eval_root f (show y^2-(x+y)*y+x*y=0 by ring)]
  constructor <;> simp only [imageSum, imageProduct] <;> ring

theorem discriminant (n s u v : R) :
    (imageSum s u v)^2-4*imageProduct n s u v = u^2*(s^2-4*n) := by
  unfold imageSum imageProduct
  ring

/-- Every original witness survives the transformed test over the very
same modulus. This holds for even and composite moduli as well. -/
theorem polynomial_preserves {m : ℕ} {n s : ZMod m} (f : (ZMod m)[X]) (ok : AdmissibleSum n s) :
    AdmissibleSum (imageProduct n s (reduced n s f).1 (reduced n s f).2)
      (imageSum s (reduced n s f).1 (reduced n s f).2) := by
  obtain ⟨x,y,prod,sum⟩ := ok
  obtain ⟨a,b⟩ := transformed_pair f prod sum
  exact ⟨f.eval x, f.eval y, b, a⟩

/-- Inverting the affine map on both factors proves equivalence when its
slope is a unit. The proof never divides by two or assumes a field. -/
theorem affine_iff {m : ℕ} {n s u v : ZMod m} (unit : IsUnit u) :
    AdmissibleSum (imageProduct n s u v) (imageSum s u v) ↔ AdmissibleSum n s := by
  obtain ⟨t,rfl⟩ := unit
  constructor
  · rintro ⟨a,b,prod,sum⟩
    let x := (↑(t⁻¹) : ZMod m)*(a-v)
    let y := (↑(t⁻¹) : ZMod m)*(b-v)
    have ha : (t : ZMod m)*x = a-v := by simp [x, ← mul_assoc]
    have hb : (t : ZMod m)*y = b-v := by simp [y, ← mul_assoc]
    refine ⟨x,y,(t.isUnit.pow 2).mul_left_cancel ?_,t.isUnit.mul_left_cancel ?_⟩
    · calc
        (t : ZMod m)^2*(x*y) = ((t : ZMod m)*x)*((t : ZMod m)*y) := by ring
        _ = (a-v)*(b-v) := by rw [ha,hb]
        _ = (t : ZMod m)^2*n := by
          unfold imageProduct at prod
          unfold imageSum at sum
          linear_combination prod - v*sum
    · rw [mul_add, ha, hb]
      unfold imageSum at sum
      linear_combination sum
  · rintro ⟨x,y,rfl,rfl⟩
    refine ⟨(t : ZMod m)*x+v,(t : ZMod m)*y+v,?_,?_⟩
    · unfold imageProduct; ring
    · unfold imageSum; ring

theorem polynomial_iff_of_unit {m : ℕ} (n s : ZMod m) (f : (ZMod m)[X])
    (unit : IsUnit (reduced n s f).1) :
    AdmissibleSum (imageProduct n s (reduced n s f).1 (reduced n s f).2)
      (imageSum s (reduced n s f).1 (reduced n s f).2) ↔ AdmissibleSum n s := affine_iff unit

/-- Squaring the factors gives slope s and constant -n. -/
theorem reduced_square (n s : R) : reduced n s (X^2) = (s,-n) := by
  nontriviality R
  have deg : (quadratic n s).degree = 2 := by
    have dx : (X^2 : R[X]).degree = 2 := by simp
    unfold quadratic
    rw [degree_sub_eq_left_of_degree_lt (by simpa only [dx] using low_degree n s), dx]
  have rep : (X^2 : R[X]) %ₘ quadratic n s = C s*X-C n := by
    apply (div_modByMonic_unique 1 (C s*X-C n) (monic_quadratic n s) ?_).2
    constructor
    · unfold quadratic; ring
    · rw [deg]; exact low_degree n s
  simp [reduced, rep, coeff_X]

/-- 402 is an allowed candidate in the 8-bit window for 40309. It fails
the original modulus 9 test. Squaring both proposed factors erases the
failure: the transformed residues 2 and 2 realize the new product and sum. -/
theorem nonunit_example :
    402 ∈ ToySumIsolation.menu 40309 128 ∧
    ¬IsUnit ((402 : ℕ) : ZMod 9) ∧ ¬AdmissibleSum (40309 : ZMod 9) 402 ∧
    let n : ZMod 9 := 40309
    let s : ZMod 9 := 402
    let z := reduced n s (X^2)
    (2 : ZMod 9)*2 = imageProduct n s z.1 z.2 ∧ 2+2 = imageSum s z.1 z.2 ∧
      AdmissibleSum (imageProduct n s z.1 z.2) (imageSum s z.1 z.2) := by
  refine ⟨by decide +kernel, (ZMod.isUnit_iff_coprime 402 9).not.mpr (by decide),
    by unfold AdmissibleSum; decide +kernel, ?_⟩
  dsimp only
  rw [reduced_square]
  refine ⟨by decide, by decide, ⟨2,2,by decide,by decide⟩⟩

end PrimeFactors.PolynomialSumFilters
