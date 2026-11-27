import PrimeFactors.QuotientSearch
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.RingTheory.Coprime.Basic

namespace PrimeFactors.SecantQuotientCells

/-- The secant through two consecutive abscissas of a wheel class represents the
reciprocal at double the squared wheel modulus. For an even coprime wheel, the
two anchor abscissas are units at this precision. -/
theorem secant_lift {a m i j t x y N : ℤ}
    (inverse : a*(a+m)*i = 1+2*m^2*j) (residue : x=a+m*t) (product : N=x*y) :
    2*m^2 ∣ y - N*i*(2*a+m-x) := by
  obtain ⟨k, hk⟩ := (Int.even_mul_pred_self t).two_dvd
  refine ⟨y*(i*k-j), ?_⟩
  subst x N
  linear_combination -y*inverse + y*i*m^2*hk

/-- The determinant of three points in the lifted class is a multiple of
twice the cube of the wheel. -/
theorem secant_determinant (a c d m u₁ u₂ u₃ v₁ v₂ v₃ : ℤ) :
    let x := fun u => a+m*u
    let y := fun u v => c+d*(x u)+2*m^2*v
    (x u₂-x u₁)*(y u₃ v₃-y u₁ v₁)-(x u₃-x u₁)*(y u₂ v₂-y u₁ v₁) =
      (2*m^3)*((u₂-u₁)*(v₃-v₁)-(u₃-u₁)*(v₂-v₁)) := by
  dsimp
  ring

/-- Any affine formula fitting three consecutive modular reciprocal values at
unit product N has vertical modulus dividing twice the squared wheel. -/
theorem three_consecutive_ordinates {T N a m y₀ y₁ y₂ : ℤ}
    (coprime : IsCoprime T N)
    (first : T ∣ a*y₀-N) (second : T ∣ (a+m)*y₁-N)
    (third : T ∣ (a+2*m)*y₂-N) (affine : T ∣ y₀-2*y₁+y₂) :
    T ∣ 2*m^2 := by
  apply coprime.dvd_of_dvd_mul_left
  obtain ⟨u₀, h₀⟩ := first
  obtain ⟨u₁, h₁⟩ := second
  obtain ⟨u₂, h₂⟩ := third
  obtain ⟨v, hv⟩ := affine
  refine ⟨a*(a+m)*(a+2*m)*v - (a+m)*(a+2*m)*u₀ +
    2*a*(a+2*m)*u₁ - a*(a+m)*u₂, ?_⟩
  linear_combination a*(a+m)*(a+2*m)*hv - (a+m)*(a+2*m)*h₀ +
    2*a*(a+2*m)*h₁ - a*(a+m)*h₂

/-- Scaled vertical distance below the chord joining the endpoint ordinates. -/
def depth (A B N x y : ℤ) : ℤ := 4*A*(N*(A+B-x)-A*B*y)

/-- A true divisor point lies between two parallel rational lines. -/
theorem factor_in_strip {A B N x y : ℤ} (left : A ≤ x) (right : x ≤ B)
    (base : 0 ≤ A) (ordinate : 0 ≤ y) (product : N=x*y) :
    0 ≤ depth A B N x y ∧ depth A B N x y ≤ N*(B-A)^2 := by
  subst N
  unfold depth
  constructor
  · nlinarith [mul_nonneg (mul_nonneg base ordinate)
      (mul_nonneg (sub_nonneg.mpr left) (sub_nonneg.mpr right))]
  · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr left) ordinate) (sq_nonneg (B-A)),
      mul_nonneg (mul_nonneg base ordinate) (sq_nonneg (2*x-A-B))]

/-- Every triple of points in a cell is collinear when the exact chord width
and the doubled lattice index give the strict volume bound. -/
theorem collinear {A B N m x₁ x₂ x₃ y₁ y₂ y₃ k : ℤ}
    (base : 0 < A) (wheel : 0 < m)
    (left : A ≤ x₁) (h₁ : x₁ ≤ x₂) (h₂ : x₂ ≤ x₃) (right : x₃ ≤ B)
    (p₁ : 0 ≤ depth A B N x₁ y₁ ∧ depth A B N x₁ y₁ ≤ N*(B-A)^2)
    (p₂ : 0 ≤ depth A B N x₂ y₂ ∧ depth A B N x₂ y₂ ≤ N*(B-A)^2)
    (p₃ : 0 ≤ depth A B N x₃ y₃ ∧ depth A B N x₃ y₃ ≤ N*(B-A)^2)
    (multiple : (x₂-x₁)*(y₃-y₁)-(x₃-x₁)*(y₂-y₁) = (2*m^3)*k)
    (small : N*(B-A)^3 < 8*m^3*A^2*B) :
    (x₂-x₁)*(y₃-y₁)-(x₃-x₁)*(y₂-y₁) = 0 := by
  obtain ⟨low, high⟩ := quotient_rectangle_det h₁ h₂
    (show x₃-x₁ ≤ B-A by omega) p₁.1 p₂.1 p₃.1 p₁.2 p₂.2 p₃.2
  have scaled :
      (x₂-x₁)*(depth A B N x₃ y₃-depth A B N x₁ y₁) -
      (x₃-x₁)*(depth A B N x₂ y₂-depth A B N x₁ y₁) =
      -(8*m^3*A^2*B)*k := by
    unfold depth
    linear_combination -(4*A^2*B)*multiple
  rw [scaled] at low high
  have positive : 0 < 8*m^3*A^2*B := by
    have : 0 < B := by omega
    positivity
  have zero : k=0 := by
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt | gt
    · have := mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) positive.le
      nlinarith
    · have := mul_le_mul_of_nonneg_left (show 1 ≤ k by omega) positive.le
      nlinarith
  simp [multiple, zero]

end PrimeFactors.SecantQuotientCells
