import PrimeFactors.RootIntervalSlope
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors.GroupedOffsetRows

/-- Discriminant of the public-offset test, homogeneous in (j,k). -/
def form (T h j k : ℤ) := j^2+4*k*(T*j-h*k)

theorem coordinates {A B C D : ℤ} (det : B*D-A*C=1) (j k : ℤ) :
    let r := D*j-C*k
    let t := B*k-A*j
    B*r+C*t=j ∧ A*r+D*t=k := by
  dsimp only
  constructor
  · linear_combination j*det
  · linear_combination k*det

theorem primitive_change {A B C D : ℤ} (det : B*D-A*C=1) (r t : ℤ) :
    IsCoprime (B*r+C*t) (A*r+D*t) ↔ IsCoprime r t := by
  constructor
  · rintro ⟨x,y,h⟩
    exact ⟨x*B+y*A,x*C+y*D, by linear_combination h⟩
  · rintro ⟨x,y,h⟩
    refine ⟨x*D-y*A,y*B-x*C,?_⟩
    linear_combination (x*r+y*t)*det + h

theorem bilinear (T h A B C D r t : ℤ) :
    form T h (B*r+C*t) (A*r+D*t) = r^2*form T h B A +
      r*t*(2*B*C+4*T*(A*C+B*D)-8*h*A*D) + t^2*form T h C D := by
  unfold form
  ring

/-- Every primitive square hit forces the pivot discriminant to be a square
modulo the entire row index, including index zero (where equality is exact). -/
private theorem row_square {T h A B C D r t z : ℤ} (cop : IsCoprime r t)
    (hit : z^2=form T h (B*r+C*t) (A*r+D*t)) :
    ∃ x : ℤ, x^2 ≡ form T h B A [ZMOD t] := by
  obtain ⟨a,b,bez⟩ := cop
  refine ⟨a*z,Int.modEq_iff_dvd.mpr ?_⟩
  rw [mul_pow, hit, bilinear]
  refine ⟨b*(a*r+1)*form T h B A -
    a^2*(r*(2*B*C+4*T*(A*C+B*D)-8*h*A*D)+t*form T h C D),?_⟩
  linear_combination -(a*r+1)*form T h B A*bez

/-- Both axes give necessary square conditions, with no limit on the
powers of any primes dividing the coordinates. -/
theorem both_squares {T h A B C D r t z : ℤ}
    (cop : IsCoprime (B*r+C*t) (A*r+D*t)) (det : B*D-A*C=1)
    (hit : z^2=form T h (B*r+C*t) (A*r+D*t)) :
    (∃ x : ℤ, x^2 ≡ form T h B A [ZMOD t]) ∧
    (∃ x : ℤ, x^2 ≡ form T h C D [ZMOD r]) := by
  have prim := (primitive_change det r t).mp cop
  refine ⟨row_square prim hit, row_square (C:=B) (D:=A) (z:=z) prim.symm ?_⟩
  simpa only [add_comm (C*t) (B*r), add_comm (D*t) (A*r)] using hit

/-- The same linear bounds describe all integer parameters in one row. -/
theorem row_window (T h A B C D r t : ℤ) :
    T*(B*r+C*t)-h*(A*r+D*t)=(B*T-h*A)*r+(C*T-h*D)*t := by ring

theorem row_identity (T h A B j k : ℤ) :
    h*(B*k-A*j)=(B*T-h*A)*j-B*(T*j-h*k) := by ring

/-- The projected row indices of any two top choices are close. Combined
with Dirichlet's bounded slope lemma this gives O(sqrt J) possible rows. -/
theorem row_span {T h A B J j k l m : ℤ} (hp : 0<h) (bp : 0<B)
    (first : 1≤j ∧ j≤J ∧ 1≤T*j-h*k ∧ T*j-h*k≤h)
    (last : 1≤l ∧ l≤J ∧ 1≤T*l-h*m ∧ T*l-h*m≤h) :
    h * |(B*k-A*j)-(B*m-A*l)| ≤ |B*T-h*A| * (J-1)+B*(h-1) := by
  have dx : |j-l| ≤ J-1 := abs_le.mpr ⟨by omega, by omega⟩
  have dy : |(T*j-h*k)-(T*l-h*m)| ≤ h-1 := abs_le.mpr ⟨by omega, by omega⟩
  have pair : h*((B*k-A*j)-(B*m-A*l)) =
       (B*T-h*A)*(j-l)-B*((T*j-h*k)-(T*l-h*m)) := by ring
  rw [← abs_of_pos hp, ← abs_mul, pair]
  calc
    _ ≤ |(B*T-h*A)*(j-l)|+|B*((T*j-h*k)-(T*l-h*m))| := abs_sub ..
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_pos bp, abs_of_pos hp]
      exact add_le_add (mul_le_mul_of_nonneg_left dx (abs_nonneg _))
        (mul_le_mul_of_nonneg_left dy bp.le)

end PrimeFactors.GroupedOffsetRows
