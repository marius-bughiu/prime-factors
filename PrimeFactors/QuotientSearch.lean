import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors

/-- The tangent at A and the chord from A to B enclose every factor pair.
All inequalities have their denominators cleared. -/
theorem quotient_strip_contains {A B x y N : ℤ} (left : A ≤ x) (right : x ≤ B)
    (hy : 0 ≤ y) (product : x*y = N) :
    N*(2*A-x) ≤ y*A^2 ∧ y*A*B ≤ N*(A+B-x) := by
  subst N
  constructor
  · nlinarith [mul_nonneg hy (sq_nonneg (x-A))]
  · nlinarith [mul_nonneg hy (mul_nonneg (sub_nonneg.mpr left) (sub_nonneg.mpr right))]

/-- Integer product errors for all points in the rational strip. -/
theorem quotient_strip_error {A B x y N : ℤ} (hx : 0 ≤ x)
    (lower : N*(2*A-x) ≤ y*A^2) (upper : y*A*B ≤ N*(A+B-x)) :
    (N-x*y)*A^2 ≤ N*(x-A)^2 ∧ (x*y-N)*(A*B) ≤ N*(x-A)*(B-x) := by
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left lower hx]
  · nlinarith [mul_le_mul_of_nonneg_left upper hx]

/-- If any product error is zero, omitting it strengthens Cauchy's inequality. -/
theorem quotient_zero_moment_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (e : ι → ℤ) {z : ι} (hz : z ∈ s) (zero : e z = 0) :
    (∑ i ∈ s, e i)^2 ≤ ((s.card:ℤ)-1) * ∑ i ∈ s, (e i)^2 := by
  have bound := Finset.sum_mul_sq_le_sq_mul_sq (s.erase z) (fun _ => (1:ℤ)) e
  have card : ((s.erase z).card : ℤ) = (s.card : ℤ)-1 := by
    have eq := Finset.card_erase_add_one hz
    omega
  have h₁ := Finset.sum_erase_add s e hz
  have h₂ := Finset.sum_erase_add s (fun i => (e i)^2) hz
  simp only [zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h₁ h₂
  simpa [h₁, h₂, card] using bound

/-- Two errors admit an exact zero decision from their first two power sums. -/
theorem quotient_two_moments (a b : ℤ) :
    (a+b)^2 = a^2+b^2 ↔ a=0 ∨ b=0 := by
  rw [← mul_eq_zero]
  constructor <;> intro h <;> nlinarith

/-- Three errors admit an exact zero decision from their first three power sums. -/
theorem quotient_three_moments (a b c : ℤ) :
    (a+b+c)^3 - 3*(a+b+c)*(a^2+b^2+c^2) + 2*(a^3+b^3+c^3) = 0 ↔
      a=0 ∨ b=0 ∨ c=0 := by
  rw [show (a+b+c)^3 - 3*(a+b+c)*(a^2+b^2+c^2) + 2*(a^3+b^3+c^3) =
    6*(a*(b*c)) by ring]
  simp

/-- An annihilating weight leaves only the first coordinate of the true point.
A polynomial weight can be evaluated from mixed moments. -/
theorem quotient_isolate_coordinate {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x e w : ι → ℤ) {z : ι} (hz : z ∈ s)
    (unique : ∀ i ∈ s, e i = 0 → i = z) (annihilate : ∀ i ∈ s, e i ≠ 0 → w i = 0) :
    ∑ i ∈ s, x i*w i = x z*w z := by
  apply Finset.sum_eq_single z
  · intro i hi ne
    have err : e i ≠ 0 := fun he => ne (unique i hi he)
    simp [annihilate i hi err]
  · exact fun no => (no hz).elim

/-- A determinant of a triangle in a W by H rectangle has absolute value
at most W*H. The first coordinates are given in sorted order. -/
theorem quotient_rectangle_det {x₁ x₂ x₃ y₁ y₂ y₃ W H : ℤ}
    (h₁ : x₁ ≤ x₂) (h₂ : x₂ ≤ x₃) (span : x₃-x₁ ≤ W)
    (a₁ : 0 ≤ y₁) (a₂ : 0 ≤ y₂) (a₃ : 0 ≤ y₃)
    (b₁ : y₁ ≤ H) (b₂ : y₂ ≤ H) (b₃ : y₃ ≤ H) :
    let D := (x₂-x₁)*(y₃-y₁) - (x₃-x₁)*(y₂-y₁);
    -(W*H) ≤ D ∧ D ≤ W*H := by
  dsimp
  have u := sub_nonneg.mpr h₁
  have v := sub_nonneg.mpr h₂
  have w := sub_nonneg.mpr (h₁.trans h₂)
  have h := mul_le_mul_of_nonneg_right span (a₁.trans b₁)
  constructor
  · nlinarith [mul_nonneg u a₃, mul_nonneg v a₁, mul_le_mul_of_nonneg_left b₂ w]
  · nlinarith [mul_le_mul_of_nonneg_left b₃ u, mul_le_mul_of_nonneg_left b₁ v,
               mul_nonneg w a₂]

/-- Subtract the tangent and scale vertically to an integral rectangle. -/
theorem quotient_shear_bounds {A B x y N : ℤ} (a : 0 < A) (left : A ≤ x)
    (right : x ≤ B) (n : 0 ≤ N) (lower : N*(2*A-x) ≤ y*A^2)
    (upper : y*A*B ≤ N*(A+B-x)) :
    0 ≤ A^2*B*y - B*N*(2*A-x) ∧
      A^2*B*y - B*N*(2*A-x) ≤ N*(B-A)^2 := by
  have b : 0 ≤ B := le_trans (le_of_lt a) (left.trans right)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left lower b]
  · nlinarith [mul_le_mul_of_nonneg_left upper (le_of_lt a),
      mul_nonneg (mul_nonneg n (sub_nonneg.mpr (left.trans right))) (sub_nonneg.mpr right)]

/-- The ordinate shear preserves the integer determinant up to a scale.
A strip strictly below that scale forces the determinant to vanish. -/
theorem quotient_small_sheared_det {x₁ x₂ x₃ y₁ y₂ y₃ s u v W H : ℤ}
    (h₁ : x₁ ≤ x₂) (h₂ : x₂ ≤ x₃) (span : x₃-x₁ ≤ W)
    (a₁ : 0 ≤ s*y₁+u*x₁+v) (a₂ : 0 ≤ s*y₂+u*x₂+v) (a₃ : 0 ≤ s*y₃+u*x₃+v)
    (b₁ : s*y₁+u*x₁+v ≤ H) (b₂ : s*y₂+u*x₂+v ≤ H) (b₃ : s*y₃+u*x₃+v ≤ H)
    (small : W*H < s) (positive : 0 < s) :
    (x₂-x₁)*(y₃-y₁)-(x₃-x₁)*(y₂-y₁) = 0 := by
  obtain ⟨lo, hi⟩ := quotient_rectangle_det h₁ h₂ span a₁ a₂ a₃ b₁ b₂ b₃
  let D := (x₂-x₁)*(y₃-y₁)-(x₃-x₁)*(y₂-y₁)
  change D = 0
  have det : (x₂-x₁)*(s*y₃+u*x₃+v-(s*y₁+u*x₁+v)) -
      (x₃-x₁)*(s*y₂+u*x₂+v-(s*y₁+u*x₁+v)) = s*D := by dsimp [D]; ring
  rw [det] at hi lo
  by_contra ne
  rcases lt_or_gt_of_ne ne with neg | pos
  · have h := mul_le_mul_of_nonneg_left (show D ≤ -1 by omega) positive.le
    nlinarith
  · have h := mul_le_mul_of_nonneg_left (show 1 ≤ D by omega) positive.le
    nlinarith

/-- Rank one of the Gram matrix gives a line through every centered point. -/
theorem quotient_covariance_line {ι : Type*} (s : Finset ι) (f g : ι → ℤ)
    {A B C : ℤ} (xx : ∑ i ∈ s, (f i)^2 = A) (xy : ∑ i ∈ s, f i*g i = B)
    (yy : ∑ i ∈ s, (g i)^2 = C) (det : A*C = B^2) {i : ι} (hi : i ∈ s) :
    A*g i = B*f i := by
  have total : ∑ i ∈ s, (A*g i-B*f i)^2 = 0 := by
    calc
      _ = ∑ i ∈ s, (A^2*(g i)^2 + B^2*(f i)^2 - (2*A*B)*(f i*g i)) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = A^2*C+B^2*A-(2*A*B)*B := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, xx, xy, yy]
      _ = 0 := by linear_combination A*det
  have single := Finset.single_le_sum (s := s) (fun j _ => sq_nonneg (A*g j-B*f j)) hi
  rw [total] at single
  nlinarith [sq_nonneg (A*g i-B*f i)]

/-- Linearizing the reciprocal at one residue a modulo m gives an ordinate
congruence modulo m squared. An inverse of a is taken at the full precision. -/
theorem quotient_wheel_lift {a i m j u x y N : ℤ}
    (inverse : a*i = 1+m^2*j) (residue : x=a+m*u) (product : N=x*y) :
    m^2 ∣ y-(N*i-N*i^2*(x-a)) := by
  refine ⟨y*(-j+i*j*m*u+i^2*u^2), ?_⟩
  subst N x
  linear_combination -y*(1-i*m*u)*inverse

/-- The lattice used for one wheel class has determinant m cubed.
This is also the divisor of each signed area determinant in that class. -/
theorem quotient_wheel_determinant (a b d m u₁ u₂ u₃ v₁ v₂ v₃ : ℤ) :
    let x := fun u => a+m*u
    let y := fun u v => b+d*(x u)+m^2*v
    (x u₂-x u₁)*(y u₃ v₃-y u₁ v₁)-(x u₃-x u₁)*(y u₂ v₂-y u₁ v₁) =
      m^3*((u₂-u₁)*(v₃-v₁)-(u₃-u₁)*(v₂-v₁)) := by
  dsimp
  ring

/-- A strip determinant in a wheel class is a multiple of its index. -/
theorem quotient_wheel_area_zero {D k m S T : ℤ} (multiple : D=m^3*k)
    (low : -T ≤ S*D) (high : S*D ≤ T) (small : T < S*m^3)
    (sm : 0 < S) (mm : 0 < m) : D = 0 := by
  have pos : 0 < S*m^3 := mul_pos sm (pow_pos mm _)
  rw [multiple, ← mul_assoc] at low high
  have eq : k = 0 := by
    by_contra ne
    rcases lt_or_gt_of_ne ne with neg | hp
    · have h := mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) pos.le
      nlinarith
    · have h := mul_le_mul_of_nonneg_left (show 1 ≤ k by omega) pos.le
      nlinarith
  simp [multiple, eq]

/-- A certified line reduces all enclosed factors to one quadratic equation. -/
theorem quotient_line_quadratic {a b c x y N : ℤ} (product : x*y=N) (line : c*y=a*x+b) :
    a*x^2+b*x=c*N := by
  rw [← product]
  linear_combination -x*line

/-- A closed interval of span at least two steps contains two consecutive
members of any shifted integer progression. -/
theorem quotient_two_grid_levels {L U s : ℤ} (start : ℤ) (pos : 0 < s)
    (span : 2*s ≤ U-L) :
    ∃ j : ℤ, L ≤ start+s*j ∧ start+s*(j+1) ≤ U := by
  let j := (U-start)/s
  have decomp := Int.emod_add_ediv (U-start) s
  have lo := Int.emod_nonneg (U-start) pos.ne'
  have hi := Int.emod_lt_of_pos (U-start) pos
  refine ⟨j-1, ?_, ?_⟩
  · rw [mul_sub, mul_one]
    dsimp [j]
    omega
  · simp only [sub_add_cancel]
    dsimp [j]
    omega

/-- On a span of at least four column steps, every residue has two columns
in the right half, including at the endpoint of the equality case. -/
theorem quotient_two_right_columns {A B m : ℤ} (a : ℤ) (pos : 0 < m)
    (span : 4*m ≤ B-A) :
    ∃ u : ℤ, A+B ≤ 2*(a+m*u) ∧ a+m*(u+1) ≤ B := by
  obtain ⟨u, lo, hi⟩ := quotient_two_grid_levels (L:=A+B) (U:=2*B) (2*a)
    (show 0 < 2*m by omega) (by omega)
  have rhs : 2*a+2*m*(u+1) = 2*(a+m*(u+1)) := by ring
  rw [rhs] at hi
  exact ⟨u, by linear_combination lo, by omega⟩

/-- The fully integral width condition forces two consecutive admissible
ordinates in each column on the right half of the tangent-to-chord strip.
Both bounds are expressed with the common denominator A squared times B. -/
theorem quotient_two_right_heights {A B N x m : ℤ} (c : ℤ) (a : 0 < A)
    (ab : A ≤ B) (n : 0 ≤ N) (pos : 0 < m) (right : A+B ≤ 2*x)
    (wide : 4*m^2*(A^2*B) ≤ N*(B-A)^2) :
    ∃ v : ℤ, B*N*(2*A-x) ≤ A^2*B*(c+m^2*v) ∧
      A^2*B*(c+m^2*(v+1)) ≤ A*N*(A+B-x) := by
  have b := a.trans_le ab
  have long : 2*(A^2*B*m^2) ≤ A*N*(A+B-x)-B*N*(2*A-x) := by
    nlinarith only [wide, mul_nonneg (mul_nonneg n (sub_nonneg.mpr ab))
      (show 0 ≤ 2*x-(A+B) by omega)]
  obtain ⟨v, lo, hi⟩ := quotient_two_grid_levels (A^2*B*c)
    (show 0 < A^2*B*m^2 by positivity) long
  exact ⟨v, by linear_combination lo, by linear_combination hi⟩

/-- Two consecutive heights in one wheel column and one point in the
next form a triangle of determinant minus m cubed, regardless of that
third ordinate. In particular these points cannot pass the line test. -/
theorem quotient_adjacent_triangle {m : ℤ} (x y z : ℤ) (pos : 0 < m) :
    (x-x)*(z-y)-((x+m)-x)*((y+m^2)-y) = -m^3 ∧ -m^3 ≠ 0 := by
  constructor
  · ring
  · exact neg_ne_zero.mpr (pow_ne_zero _ pos.ne')

end PrimeFactors
