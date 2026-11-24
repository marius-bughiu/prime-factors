import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- Three real readings start the recurrence on any arithmetic progression. -/
theorem phaseEval_cosine_step (a d : ℝ) :
    Real.cos (a+2*d) = 2*Real.cos d*Real.cos (a+d) - Real.cos a := by
  have sum := Real.cos_add_cos ((a+d)+d) ((a+d)-d)
  rw [show ((a+d)+d + ((a+d)-d))/2 = a+d by ring,
    show ((a+d)+d - ((a+d)-d))/2 = d by ring,
    show (a+d)-d = a by ring, show (a+d)+d = a+2*d by ring] at sum
  linarith

private theorem phaseEval_sine_multiple (j : ℕ) (x : ℝ) :
    |Real.sin ((j:ℝ)*x)| ≤ j*|Real.sin x| := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
    apply (abs_add_le ..).trans
    rw [abs_mul, abs_mul]
    have left := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (abs_nonneg (Real.sin ((j:ℝ)*x)))
    have right := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one ((j:ℝ)*x)) (abs_nonneg (Real.sin x))
    linarith

/-- One uncertain elementary cosine determines an integer multiple with a uniform
quadratic loss, without needing to choose a sign for the angle. -/
theorem phaseEval_multiple_lipschitz (j : ℕ) (a b : ℝ) :
    |Real.cos ((j:ℝ)*a)-Real.cos ((j:ℝ)*b)| ≤ (j:ℝ)^2 * |Real.cos a-Real.cos b| := by
  rw [Real.cos_sub_cos, Real.cos_sub_cos, show ((j:ℝ)*a+j*b)/2 = j*((a+b)/2) by ring,
    show ((j:ℝ)*a-j*b)/2 = j*((a-b)/2) by ring]
  simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have first := phaseEval_sine_multiple j ((a+b)/2)
  have last := phaseEval_sine_multiple j ((a-b)/2)
  have bound := mul_le_mul first last (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg j) (abs_nonneg _))
  linarith

/-- A small perturbation in the sampled recurrence coefficient and rounding the next
value contribute additively to its local defect. The true outputs are bounded by one. -/
theorem phaseEval_local_error {c x a₀ a₁ a₂ b₀ b₁ b₂ ε ρ : ℝ} (exactStep : a₂=2*c*a₁-a₀)
    (bounded : |a₁| ≤ 1) (coeff : |x-c| ≤ ε) (rounding : |b₂-(2*x*b₁-b₀)| ≤ ρ) :
    |(b₂-a₂) - 2*x*(b₁-a₁) + (b₀-a₀)| ≤ 2*ε+ρ := by
  rw [exactStep]
  have eq : (b₂-(2*c*a₁-a₀)) - 2*x*(b₁-a₁) + (b₀-a₀) =
      2*(x-c)*a₁ + (b₂-(2*x*b₁-b₀)) := by ring
  rw [eq]
  apply (abs_add_le ..).trans
  apply add_le_add _ rounding
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc
    _ ≤ (2 * |x-c|) * 1 := mul_le_mul_of_nonneg_left bounded (by positivity)
    _ ≤ _ := by linarith

/-- For a second-order recurrence with two unit-circle characteristic roots, errors
grow at most quadratically in the number of steps, including the repeated-root case. -/
theorem phaseEval_stability (e : ℕ → ℂ) {z w : ℂ}
    (roots : z*w=1) (zUnit : ‖z‖=1) (wUnit : ‖w‖=1)
    {ε τ : ℝ} (first : ‖e 0‖ ≤ ε) (second : ‖e 1‖ ≤ ε)
    (step : ∀ i, ‖e (i+2)-(z+w)*e (i+1)+e i‖ ≤ τ) (j : ℕ) :
    ‖e (j+1)‖ ≤ (2*(j:ℝ)+1)*ε + (j:ℝ)*(j+1)/2*τ := by
  let d (i : ℕ) := e (i+1)-z*e i
  have slope (i : ℕ) : ‖d i‖ ≤ 2*ε+i*τ := by
    induction i with
    | zero =>
      dsimp [d]
      have start := norm_sub_le (e 1) (z*e 0)
      rw [norm_mul, zUnit, one_mul] at start
      norm_num
      linarith
    | succ i ih =>
      have eq : d (i+1) = w*d i + (e (i+2)-(z+w)*e (i+1)+e i) := by
        dsimp [d]
        linear_combination e i * roots
      rw [eq]
      have bound := norm_add_le (w*d i) (e (i+2)-(z+w)*e (i+1)+e i)
      rw [norm_mul, wUnit, one_mul] at bound
      push_cast
      linarith [step i]
  induction j with
  | zero => simpa using second
  | succ j ih =>
    have eq : e (j+2) = d (j+1)+z*e (j+1) := by dsimp [d]; ring
    change ‖e (j+2)‖ ≤ _
    rw [eq]
    have bound := norm_add_le (d (j+1)) (z*e (j+1))
    rw [norm_mul, zUnit, one_mul] at bound
    have sl := slope (j+1)
    push_cast at sl ⊢
    linarith

/-- The product trace equation can be tested via a discriminant even over rings with
zero divisors, provided two is invertible. -/
theorem phaseEval_trace_fibre {R : Type*} [CommRing R] (two : Rˣ) (twoVal : (two:R) = 2)
    (s : R) : (∃ x : R, x^2+1=s*x) ↔ ∃ y : R, y^2=s^2-4 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨2*x-s, by linear_combination 4*hx⟩
  · rintro ⟨y, hy⟩
    let x := (↑(two⁻¹) : R)*(s+y)
    have hx : 2*x = s+y := by
      change 2*((↑(two⁻¹) : R)*(s+y)) = _
      rw [← twoVal, ← mul_assoc, Units.mul_inv, one_mul]
    refine ⟨x, (two^2).isUnit.mul_left_cancel ?_⟩
    simp only [Units.val_pow_eq_pow_val, twoVal]
    linear_combination hy + (2*x+y-s)*hx

/-- The public fractional-linear change of variable turns an arbitrary square-class
query into a trace discriminant, multiplied by a known unit square. -/
theorem phaseEval_discriminant {R : Type*} [CommRing R] {a s : R}
    (relation : (a-1)*s=2*(a+1)) : (a-1)^2*(s^2-4)=16*a := by
  linear_combination ((a-1)*s+2*(a+1))*relation


private theorem phaseEval_move_square {R : Type*} [CommRing R] (u v : Rˣ) {a b : R}
    (eq : (u:R)^2*a=(v:R)^2*b) (root : ∃ x : R, x^2=a) : ∃ y : R, y^2=b := by
  obtain ⟨x, hx⟩ := root
  let y := (↑(v⁻¹) : R)*((u:R)*x)
  have prod : (v:R)*y=(u:R)*x := by dsimp [y]; rw [← mul_assoc, Units.mul_inv, one_mul]
  refine ⟨y, (v^2).isUnit.mul_left_cancel ?_⟩
  simp only [Units.val_pow_eq_pow_val]
  rw [← mul_pow, prod, mul_pow, hx, eq]

/-- Over a composite modulus as well as a field, the transformed trace fibre is nonempty
exactly when the original unit is a square. -/
theorem phaseEval_residuosity {R : Type*} [CommRing R] (two denom : Rˣ) {a s : R}
    (twoVal : (two:R)=2) (denomVal : (denom:R)=a-1) (relation : (a-1)*s=2*(a+1)) :
    (∃ x : R, x^2+1=s*x) ↔ ∃ y : R, y^2=a := by
  rw [phaseEval_trace_fibre two twoVal]
  have eq : (denom:R)^2*(s^2-4)=((↑(two^2) : R))^2*a := by
    rw [denomVal, phaseEval_discriminant relation, Units.val_pow_eq_pow_val, twoVal]
    ring
  exact ⟨phaseEval_move_square denom (two^2) eq, phaseEval_move_square (two^2) denom eq.symm⟩

/-- Both the inverse of a trace preimage and its common Jacobi weight follow from
its quadratic equation. -/
theorem phaseEval_fibre_identities {R : Type*} [CommRing R] {x s : R} (trace : x^2+1=s*x) :
    x*(s-x)=1 ∧ (x-1)^2=(s-2)*x := by
  constructor
  · linear_combination -trace
  · linear_combination trace


/-- Two distinct positions on a random affine progression are jointly uniform whenever
 their difference is a unit: this is the explicit bijection on starting points and steps. -/
noncomputable def phaseEval_pairEquiv {R : Type*} [CommRing R] (i : R) (u : Rˣ) : R × R ≃ R × R where
  toFun a := (a.1+i*a.2, a.1+(i+(u:R))*a.2)
  invFun v := (v.1 - i*((↑(u⁻¹):R)*(v.2-v.1)), (↑(u⁻¹):R)*(v.2-v.1))
  left_inv a := by
    obtain ⟨T, D⟩ := a
    dsimp only
    rw [show T+(i+(u:R))*D-(T+i*D) = (u:R)*D by ring, ← mul_assoc (↑(u⁻¹):R), Units.inv_mul, one_mul]
    simp
  right_inv v := by
    obtain ⟨v, w⟩ := v
    dsimp only
    apply Prod.ext
    · dsimp only; ring
    · dsimp only
      have unit : (u:R)*(↑(u⁻¹):R) = 1 := Units.mul_inv u
      linear_combination (w-v)*unit

/-- Short signed multiple indices for inverse, pairwise coprime moduli must all encode
one integer divisible by the full product. -/
theorem phaseEval_inverse_divides {ι : Type*} (s : Finset ι) (m k : ι → ℤ)
    {N label C : ℤ} (pos : 0 < N) (size : 2*C < N)
    (coprime : (s : Set ι).Pairwise (fun i j => IsCoprime (m i) (m j)))
    (short : ∀ i ∈ s, |m i*k i| ≤ C) (labels : ∀ i ∈ s, m i*k i ≡ label [ZMOD N])
    {j : ι} (hj : j ∈ s) : (∏ i ∈ s, m i) ∣ m j*k j := by
  apply Finset.prod_dvd_of_coprime coprime
  intro i hi
  have same := (labels i hi).trans (labels j hj).symm
  obtain ⟨v, hv⟩ := Int.modEq_iff_dvd.mp same
  have spanI := abs_le.mp (short i hi)
  have spanJ := abs_le.mp (short j hj)
  have zero : v = 0 := by
    rcases lt_trichotomy v 0 with neg | eq | plus
    · have bd := mul_le_mul_of_nonneg_left (show v ≤ -1 by omega) pos.le
      linarith
    · exact eq
    · have bd := mul_le_mul_of_nonneg_left (show 1 ≤ v by omega) pos.le
      linarith
  rw [zero, mul_zero] at hv
  rw [show m j*k j = m i*k i by linarith]
  exact dvd_mul_right _ _

/-- Two regular trace bins with Jacobi-one discriminants, one occupied and one empty. -/
example : (∃ x : ZMod 77, x^2+1=29*x) ∧ ¬(∃ x : ZMod 77, x^2+1=49*x) := by decide +kernel

end PrimeFactors
