import PrimeFactors.SquareRootPhasePopulation
import Mathlib.Data.Real.Irrational

/-! Two simultaneous square-root readings on the balanced prime population.
The Fourier and bilinear estimates are analytic inputs. The tensor
inequalities, dyadic normalization, essential endpoint check and conclusion
about every pair of 177-bit readings are finite consequences. -/
namespace PrimeFactors.JointSquareRootPhase

open Finset
set_option exponentiation.threshold 8192

/-- Tensor two majorants and minorants, allowing the minorants to be negative. -/
theorem tensor_bounds {x y A B C D : ℝ} (x0 : 0≤x) (y0 : 0≤y)
    (xb : B≤x) (xa : x≤A) (yd : D≤y) (yc : y≤C) :
    B*C+A*D-A*C ≤ x*y ∧ x*y ≤ A*C := by
  have a0 := x0.trans xa
  have c0 := y0.trans yc
  constructor
  · nlinarith only [mul_nonneg (sub_nonneg.mpr xa) (sub_nonneg.mpr yc),
      mul_le_mul_of_nonneg_right xb c0, mul_le_mul_of_nonneg_left yd a0]
  · exact mul_le_mul xa yc y0 a0

/-- Products of trigonometric polynomials in separate variables have
constant coefficient equal to the product of their constant coefficients. -/
theorem constant_terms (d e : ℝ) :
    (d-e)*(d+e)+(d+e)*(d-e)-(d+e)^2=d^2-2*d*e-3*e^2 ∧
    (d+e)^2=d^2+2*d*e+e^2 := by constructor <;> ring

/-- The conjugate frequency controls small divisors even when h and k
have opposite signs. -/
theorem frequency_norm (h k : ℤ) (hk : k≠0) :
    1 ≤ |(h:ℝ)+Real.sqrt 2*k| * (|(h:ℝ)| + Real.sqrt 2 * |(k:ℝ)|) := by
  have irr := irrational_sqrt_two.mul_intCast hk
  have left := (irr.intCast_add h).ne_zero
  have right := (irr.intCast_sub h).ne_zero
  have same : ((h:ℝ)+Real.sqrt 2*k)*(h-Real.sqrt 2*k)=(h:ℝ)^2-2*k^2 := by
    calc _ = (h:ℝ)^2-(Real.sqrt 2)^2*k^2 := by ring
         _ = _ := by rw [Real.sq_sqrt (by norm_num)]
  have nz : (h^2-2*k^2 : ℤ)≠0 := by
    exact_mod_cast (show (h:ℝ)^2-2*k^2≠0 by rw [←same]; exact mul_ne_zero left right)
  have unit : 1≤|(h:ℝ)^2-2*k^2| := by exact_mod_cast Int.one_le_abs nz
  rw [←same,abs_mul] at unit
  have tri := abs_sub (h:ℝ) (Real.sqrt 2*k)
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at tri
  exact unit.trans (mul_le_mul_of_nonneg_left tri (abs_nonneg _))

/-- Price the three Fourier products in the lower estimate and the single
product in the upper estimate. The input S is the error for one product. -/
theorem region_error {n d e S c upper lower₁ lower₂ : ℝ}
    (n0 : 0≤n) (s0 : 0≤S)
    (u : |upper-(d+e)^2*n|≤S)
    (v : |lower₁-(d-e)*(d+e)*n|≤S)
    (w : |lower₂-(d+e)*(d-e)*n|≤S)
    (bracket : lower₁+lower₂-upper≤c ∧ c≤upper) :
    |c-d^2*n| ≤ (2*d*e+3*e^2)*n+3*S := by
  obtain ⟨u1,u2⟩ := abs_le.mp u
  obtain ⟨v1,_⟩ := abs_le.mp v
  obtain ⟨w1,_⟩ := abs_le.mp w
  apply abs_le.mpr
  constructor
  · nlinarith only [bracket.1,v1,w1,u2]
  · nlinarith only [bracket.2,u2,mul_nonneg (sq_nonneg e) n0,s0]

/-- The separable sum used to bound all frequencies outside the narrow
resonance strip. The axes are included. -/
theorem tensor_moment {ι : Type*} (F : Finset ι) (a f : ι→ℝ) :
    (∑ i∈F, ∑ j∈F, a i*a j*(f i+6/5*f j+152)) =
    (∑ i∈F, a i*f i)*(∑ j∈F, a j) +
    (6/5)*(∑ i∈F, a i)*(∑ j∈F, a j*f j) + 152*(∑ i∈F, a i)^2 := by
  have expand (i j : ι) : a i*a j*(f i+6/5*f j+152) =
      (a i*f i)*a j+(6/5*a i)*(a j*f j)+(152*a i)*a j := by ring
  simp_rw [expand, Finset.sum_add_distrib, ←Finset.mul_sum]
  simp only [←Finset.sum_mul, pow_two, ←Finset.mul_sum]
  ring

/-- At the 177-bit setting each envelope has mass below 20, weighted mass
at most (10/3)√H. The near-resonant strip costs at most 15000 extra units. -/
theorem moment_budget {A F r : ℝ} (rp : 0≤r) (ap : 0≤A)
    (mass : A≤20) (first : F≤(10/3)*r) :
    F*A+(6/5)*A*F+152*A^2+15000 ≤ 148*r+80000 := by
  have joint := mul_le_mul first mass ap (by positivity)
  have sq : A^2≤20^2 := by gcongr
  nlinarith only [joint,sq,rp]

/-- A region's count error as a fraction of (cell area × eligible count). -/
noncomputable def budget : ℝ :=
  2/(2:ℝ)^31+3/(2:ℝ)^62+
    3*41056*(148*(2:ℝ)^104+80000)*(2:ℝ)^354/(2:ℝ)^511

theorem budget_bound : budget < 295514/10^14 ∧ budget<1/(2:ℝ)^28 := by
  norm_num [budget]

/-- Convert the tensor discrepancy into the relative error used by the
conditional count bound. Here P√X/T ≤ 41056/2^511. -/
theorem normalize {n T c S e : ℝ} (n0 : 0≤n) (part : n≤T)
    (e0 : 0≤e) (eH : e≤1/(2:ℝ)^208)
    (freq : S≤(148*(2:ℝ)^104+80000)*41056/(2:ℝ)^511*T)
    (reg : |c-(1/(2:ℝ)^177)^2*n|≤(2*(1/(2:ℝ)^177)*e+3*e^2)*n+3*S) :
    |c-(1/(2:ℝ)^354)*n|≤budget*((1/(2:ℝ)^354)*T) := by
  have size : 2*(1/(2:ℝ)^177)*e+3*e^2 ≤
      2*(1/(2:ℝ)^177)*(1/(2:ℝ)^208)+3*(1/(2:ℝ)^208)^2 := by gcongr
  have product := mul_le_mul size part n0 (by positivity)
  have cube : (1/(2:ℝ)^177)^2=1/(2:ℝ)^354 := by norm_num
  rw [cube] at reg
  unfold budget
  linarith only [reg,product,freq]

/-- Both 177-bit words are observed. Under the two region discrepancies
and the global upper bound, every cell is nonempty and strictly favors the
outer window. G and J count the inner and outer eligible prime pairs. -/
theorem joint_177 {g j G J : ℕ} (pop : 0<(G:ℝ)+J)
    (global : (G:ℝ)/(G+J)≤49999999383/10^11)
    (good : |(g:ℝ)-(1/(2:ℝ)^354)*G|≤budget*((1/(2:ℝ)^354)*(G+J)))
    (outer : |(j:ℝ)-(1/(2:ℝ)^354)*J|≤budget*((1/(2:ℝ)^354)*(G+J))) :
    0<g+j ∧ |(g:ℝ)/(g+j)-(G:ℝ)/(G+J)|<1/(2:ℝ)^28 ∧ g<j := by
  have total : 0<(1/(2:ℝ)^354)*((G:ℝ)+J) := by positivity
  have small : 2*budget<1 := by linarith only [budget_bound.2]
  have enough : 2*(budget*((1/(2:ℝ)^354)*(G+J))) <
      (1/(2:ℝ)^354)*((G:ℝ)+J) := by
    simpa only [mul_assoc,one_mul] using mul_lt_mul_of_pos_right small total
  obtain ⟨positive,change⟩ := SquareRootPhasePopulation.cell_transfer (by positivity) pop
    good outer enough
  rw [mul_div_cancel_right₀ _ (ne_of_gt total)] at change
  have strict := change.trans_lt budget_bound.2
  have toHalf : (g:ℝ)/(g+j)<1/2 := by linarith only [(abs_lt.mp strict).2,global]
  have less := (div_lt_iff₀ positive).mp toHalf
  exact ⟨by exact_mod_cast positive,strict,by exact_mod_cast (show (g:ℝ)<j by linarith only [less])⟩

private theorem no_square_single_prime {p m : ℕ} (prime : p.Prime) (nd : ¬p∣m) :
    ¬IsSquare (p*m) := by
  rintro ⟨s,hs⟩
  have div : p∣s*s := hs ▸ dvd_mul_right p m
  obtain ⟨k,rfl⟩ := (prime.dvd_mul.mp div).elim id id
  have equal : p*m=p*(p*(k*k)) := by rw [hs]; ring
  exact nd ⟨k*k,Nat.eq_of_mul_eq_mul_left prime.pos equal⟩

/-- Subtracting either integer part leaves an irrational number, so rational
dyadic endpoints cannot occur in either coordinate. -/
theorem irrational_phases {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (neq : p≠q) (odd : p≠2) (a b : ℤ) :
    Irrational (Real.sqrt (↑(p*q:ℕ):ℝ)-a) ∧
    Irrational (Real.sqrt (↑(2*(p*q):ℕ):ℝ)-b) := by
  have pq : ¬p∣q := fun h => neq ((Nat.prime_dvd_prime_iff_eq pp qp).mp h)
  have p2 : ¬p∣2 := fun h => odd ((Nat.prime_dvd_prime_iff_eq pp Nat.prime_two).mp h)
  have pq2 : ¬p∣2*q := fun h => (pp.dvd_mul.mp h).elim p2 pq
  refine ⟨(irrational_sqrt_natCast_iff.mpr (no_square_single_prime pp pq)).sub_intCast _, ?_⟩
  rw [show 2*(p*q)=p*(2*q) by ring]
  exact (irrational_sqrt_natCast_iff.mpr (no_square_single_prime pp pq2)).sub_intCast _

end PrimeFactors.JointSquareRootPhase
