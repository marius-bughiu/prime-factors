import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.GCD.Basic

namespace PrimeFactors

private theorem foldedSquare_ordered {x y : ℝ} (hy : 0 ≤ y) (ord : y ≤ x)
    (hx : x ≤ 1/4) :
    8*|x^2-y^2| ≤ |Real.cos (2*Real.pi*x) - Real.cos (2*Real.pi*y)| := by
  have jordan (t : ℝ) (h₁ : 0 ≤ t) (h₂ : t ≤ 1/2) :
      2*t ≤ Real.sin (Real.pi*t) := by
    have h := Real.le_sin_mul (x := 2*t) (by linarith) (by linarith)
    rwa [show Real.pi/2*(2*t) = Real.pi*t by ring] at h
  have sum := jordan (x+y) (by linarith) (by linarith)
  have diff := jordan (x-y) (by linarith) (by linarith)
  have h := mul_le_mul sum diff (by linarith) (by linarith)
  rw [Real.cos_sub_cos, abs_mul, abs_mul,
    show (2*Real.pi*x+2*Real.pi*y)/2 = Real.pi*(x+y) by ring,
    show (2*Real.pi*x-2*Real.pi*y)/2 = Real.pi*(x-y) by ring,
    abs_of_nonneg (show 0 ≤ Real.sin (Real.pi*(x+y)) by linarith),
    abs_of_nonneg (show 0 ≤ Real.sin (Real.pi*(x-y)) by linarith),
    abs_of_nonneg (sub_nonneg.mpr (sq_le_sq' (by linarith) ord))]
  norm_num
  nlinarith only [h]

/-- On the first quarter of a turn the observed cosine controls the
difference of the squares of the phases, uniformly even near phase zero. -/
theorem foldedSquare_cosine {x y : ℝ} (hx : x ∈ Set.Icc 0 (1/4:ℝ))
    (hy : y ∈ Set.Icc 0 (1/4:ℝ)) :
    8*|x^2-y^2| ≤ |Real.cos (2*Real.pi*x)-Real.cos (2*Real.pi*y)| := by
  rcases le_total y x with h | h
  · exact foldedSquare_ordered hy.1 h hx.2
  · rw [abs_sub_comm (x^2), abs_sub_comm (Real.cos _)]
    exact foldedSquare_ordered hx.1 h hy.2

/-- The inferred first-quarter phase after clipping a signed cosine estimate. -/
noncomputable def foldedSquarePhase (d : ℝ) : ℝ :=
  Real.arccos (max 0 (min 1 d)) / (2*Real.pi)

theorem foldedSquare_inverse {x d : ℝ} (hx : x ∈ Set.Icc 0 (1/4:ℝ)) :
    8*|(foldedSquarePhase d)^2-x^2| ≤ |d-Real.cos (2*Real.pi*x)| := by
  let c := max 0 (min 1 d)
  have c₀ : 0 ≤ c := le_max_left _ _
  have c₁ : c ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have p := Real.pi_pos
  have angle : 2*Real.pi*foldedSquarePhase d = Real.arccos c := by
    dsimp [foldedSquarePhase, c]
    field_simp
  have yh : foldedSquarePhase d ∈ Set.Icc 0 (1/4:ℝ) := by
    refine ⟨div_nonneg (Real.arccos_nonneg _) (by positivity), ?_⟩
    change Real.arccos c/(2*Real.pi) ≤ 1/4
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [Real.arccos_le_pi_div_two.mpr c₀]
  have est := foldedSquare_cosine yh hx
  rw [angle, Real.cos_arccos (by linarith) c₁] at est
  apply est.trans
  let t := Real.cos (2*Real.pi*x)
  have lo : 0 ≤ t := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith [mul_nonneg p.le hx.1]
    · nlinarith [mul_le_mul_of_nonneg_left hx.2 p.le]
  have hi : t ≤ 1 := Real.cos_le_one _
  change |max 0 (min 1 d)-t| ≤ |d-t|
  rcases le_or_gt d 0 with hd | hd
  · rw [min_eq_right (by linarith), max_eq_left hd, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith
  · rcases le_or_gt d 1 with hp | hp
    · rw [min_eq_right hp, max_eq_right hd.le]
    · rw [min_eq_left hp.le, max_eq_right (by norm_num), abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      linarith

/-- If the signed hidden cosine has error at most 1/(2N), the magnitude of
the error in the reconstructed integer quotient is at most one quarter. -/
theorem foldedSquare_quotient_error {N b x d : ℝ} {k : ℤ} (n : 0 < N)
    (bsmall : b^2 ≤ 4) (hx : x ∈ Set.Icc 0 (1/4:ℝ))
    (quotient : b^2*N*x^2-b^2/N = (k:ℝ))
    (err : |d-Real.cos (2*Real.pi*x)| ≤ 1/(2*N)) :
    |b^2*N*(foldedSquarePhase d)^2-b^2/N-(k:ℝ)| ≤ 1/4 := by
  have h := (foldedSquare_inverse hx).trans err
  have scaled := (le_div_iff₀ (by positivity : 0 < 2*N)).mp h
  rw [← quotient, show b^2*N*(foldedSquarePhase d)^2-b^2/N-(b^2*N*x^2-b^2/N) =
    b^2*N*((foldedSquarePhase d)^2-x^2) by ring, abs_mul,
    abs_of_nonneg (mul_nonneg (sq_nonneg b) n.le)]
  have lim := mul_le_mul_of_nonneg_right bsmall
    (mul_nonneg n.le (abs_nonneg ((foldedSquarePhase d)^2-x^2)))
  nlinarith only [scaled, lim]

/-- The arithmetic quarter-unit margin permits an additional error strictly
below one quarter when evaluating the final real score. -/
theorem foldedSquare_round {score exactScore : ℝ} {k : ℤ}
    (scoreError : |exactScore-(k:ℝ)| ≤ 1/4) (evaluation : |score-exactScore| < 1/4) :
    ⌊score+1/2⌋ = k := by
  have h := abs_le.mp scoreError
  have e := abs_lt.mp evaluation
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith

/-- The reflected choice has the negated cosine and a doubled numerator. -/
theorem foldedSquare_reflection {N H : ℝ} (n : N ≠ 0) :
    (N-2*H)/(2*N) = 1/2-H/N ∧
    Real.cos (2*Real.pi*(1/2-H/N)) = -Real.cos (2*Real.pi*(H/N)) := by
  constructor
  · field_simp
  · rw [show 2*Real.pi*(1/2-H/N) = Real.pi-2*Real.pi*(H/N) by ring,
      Real.cos_pi_sub]

/-- Dividing the rounded sample by two and subtracting the public cosine
leaves enough accuracy on the hidden term. -/
theorem foldedSquare_sample_error {N F W C c P : ℝ} (pos : 0 < N)
    (sample : F = 2*C+2*c) (quantized : |W-F| ≤ 1/(2*N))
    (public : |P-C| ≤ 1/(4*N)) : |W/2-P-c| ≤ 1/(2*N) := by
  have adjustment : 1/(2*N) = 2*(1/(4*N)) := by field_simp; ring
  have a := abs_le.mp quantized
  have b := abs_le.mp public
  apply abs_le.mpr
  constructor <;> linarith

private theorem foldedSquare_score {N a b x k : ℝ} (n : N ≠ 0)
    (rep : a = b*N*x) (square : a^2 = b^2+k*N) :
    b^2*N*x^2-b^2/N=k := by
  rw [rep] at square
  field_simp
  nlinarith only [square]

private theorem foldedSquare_round_exact {score : ℝ} {k : ℤ}
    (bound : |score-(k:ℝ)| ≤ 1/4) : ⌊score+1/2⌋=k :=
  foldedSquare_round (exactScore := score) bound (by norm_num)

/-- From a noisy hidden cosine, one of the two explicitly computable rounded
scores is the quotient of the square of the corresponding mixed numerator. -/
theorem foldedSquare_one_reading {N H k : ℤ} (pos : 0 < N) (nonneg : 0 ≤ H)
    (folded : 2*H ≤ N) (root : H^2 = 1+k*N) {d : ℝ}
    (err : |d-Real.cos (2*Real.pi*((H:ℝ)/N))| ≤ 1/(2*(N:ℝ))) :
    ⌊(N:ℝ)*(foldedSquarePhase d)^2-1/N+1/2⌋ = k ∨
      ⌊4*(N:ℝ)*(foldedSquarePhase (-d))^2-4/N+1/2⌋ = N-4*H+4*k := by
  have n : 0 < (N:ℝ) := by exact_mod_cast pos
  have h : 0 ≤ (H:ℝ) := by exact_mod_cast nonneg
  have pair : 2*(H:ℝ) ≤ N := by exact_mod_cast folded
  have eq : (H:ℝ)^2 = 1+k*(N:ℝ) := by exact_mod_cast root
  let u := (H:ℝ)/N
  have u₀ : 0 ≤ u := div_nonneg h n.le
  have u₁ : u ≤ 1/2 := (div_le_iff₀ n).mpr (by linarith)
  by_cases near : u ≤ 1/4
  · left
    have e := foldedSquare_score (b:=1) (x:=u) n.ne'
      (show (H:ℝ) = 1*N*u by dsimp [u]; field_simp)
      (show (H:ℝ)^2 = (1:ℝ)^2 + k*N by simpa using eq)
    have bound := foldedSquare_quotient_error n (by norm_num : (1:ℝ)^2 ≤ 4) ⟨u₀, near⟩ e err
    apply foldedSquare_round_exact
    simpa using bound
  · right
    let z := 1/2-u
    have hz : z ∈ Set.Icc 0 (1/4:ℝ) := ⟨by dsimp [z]; linarith, by dsimp [z]; linarith⟩
    have reflect := (foldedSquare_reflection (H:=(H:ℝ)) n.ne').2
    have sign : |-d-Real.cos (2*Real.pi*z)| ≤ 1/(2*(N:ℝ)) := by
      dsimp [z, u]
      rw [reflect, neg_sub_neg, abs_sub_comm]
      exact err
    have e := foldedSquare_score (b:=2) (x:=z) n.ne'
      (show (N:ℝ)-2*H = 2*N*z by dsimp [z, u]; field_simp)
      (show ((N:ℝ)-2*H)^2 = (2:ℝ)^2 + ((N-4*H+4*k:ℤ):ℝ)*N by
        push_cast
        nlinarith only [eq])
    have bound := foldedSquare_quotient_error n (by norm_num : (2:ℝ)^2 ≤ 4) hz e sign
    apply foldedSquare_round_exact
    simpa only [show (2:ℝ)^2=4 by norm_num] using bound

/-- The rational phase enclosure obtained from the ten-bit reading already
determines the integral quotient of the reflected candidate for 667. -/
theorem foldedSquare_667_bracket {y : ℝ} (lo : 629/4096 ≤ y) (hi : y ≤ 630/4096) :
    ⌊4*667*y^2-4/667+1/2⌋ = 63 := by
  have low := sq_le_sq' (show -y ≤ 629/4096 by linarith) lo
  have high := sq_le_sq' (show -(630/4096:ℝ) ≤ y by linarith) hi
  apply Int.floor_eq_iff.mpr
  norm_num at low high ⊢
  constructor <;> nlinarith only [low, high]

/-- Final integer operations after rounding the second branch of the sample for 667. -/
theorem foldedSquare_667 :
    667*63+4=205^2 ∧ (205*334)%667=436 ∧ 436^2%667=1 ∧
    Nat.gcd 435 667=29 ∧ Nat.gcd 437 667=23 ∧ 23*29=667 ∧
    167^2<667*42+1 ∧ 667*42+1<168^2 := by decide +kernel

end PrimeFactors
