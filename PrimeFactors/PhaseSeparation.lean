import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PrimeFactors

open Finset

/-- The unnormalized Fejér kernel on a finite set of integer frequencies.
The pair index counts the triangular weights on a consecutive set. -/
noncomputable def phaseFejer (s : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ u ∈ s, ∑ v ∈ s, Real.cos (((u : ℝ) - v) * x)

private theorem phaseFejer_cartesian (s : Finset ℕ) (x : ℝ) :
    phaseFejer s x = (∑ u ∈ s, Real.cos (u*x))^2 + (∑ u ∈ s, Real.sin (u*x))^2 := by
  have expand (u v : ℕ) : Real.cos (((u : ℝ) - v) * x) =
      Real.cos (u*x) * Real.cos (v*x) + Real.sin (u*x) * Real.sin (v*x) := by
    rw [sub_mul, Real.cos_sub]
  unfold phaseFejer
  simp_rw [expand, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The kernel is a sum of two squares, for arbitrary finite frequency sets. -/
theorem phaseFejer_nonneg (s : Finset ℕ) (x : ℝ) : 0 ≤ phaseFejer s x := by
  rw [phaseFejer_cartesian]
  positivity

/-- The finite geometric sum gives the exact off-center kernel, including
the values where the usual quotient formula would divide by zero. -/
theorem phaseFejer_geometric (L : ℕ) (x : ℝ) :
    phaseFejer (range L) x * Real.sin (x/2)^2 = Real.sin ((L:ℝ)*x/2)^2 := by
  let z := Complex.exp ((x:ℂ)*Complex.I)
  have power (i : ℕ) : z^i = Complex.exp (((((i:ℝ)*x):ℝ):ℂ)*Complex.I) := by
    dsimp [z]
    rw [← Complex.exp_nat_mul]
    push_cast
    rw [mul_assoc]
  have normKernel : Complex.normSq (∑ i ∈ range L, z^i) = phaseFejer (range L) x := by
    rw [Complex.normSq_apply, phaseFejer_cartesian]
    simp only [Complex.re_sum, Complex.im_sum, power, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, sq]
  have chord (t : ℝ) :
      Complex.normSq (Complex.exp ((t:ℂ)*Complex.I)-1) = 4*Real.sin (t/2)^2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have double := Real.cos_two_mul (t/2)
    rw [show 2*(t/2)=t by ring] at double
    nlinarith only [Real.cos_sq_add_sin_sq t, Real.cos_sq_add_sin_sq (t/2), double]
  have identity := congrArg Complex.normSq (geom_sum_mul z L)
  rw [map_mul, normKernel, power, chord, chord] at identity
  linarith

/-- Kernel bound when the angular half-sine is at least 4/L in magnitude. -/
theorem phaseFejer_offCenter {L : ℕ} {x : ℝ} (away : 4 ≤ L*|Real.sin (x/2)|) :
    phaseFejer (range L) x ≤ (L:ℝ)^2/16 := by
  have squared := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 4) away
  have awaySq : 16 ≤ (L:ℝ)^2 * Real.sin (x/2)^2 := by
    simpa only [← sq, mul_pow, sq_abs, show (4:ℝ)^2=16 by norm_num] using squared
  have estimate := mul_le_mul_of_nonneg_right awaySq (phaseFejer_nonneg (range L) x)
  have kernel := phaseFejer_geometric L x
  have bound := mul_le_mul_of_nonneg_left (Real.sin_sq_le_one ((L:ℝ)*x/2))
    (sq_nonneg (L:ℝ))
  nlinarith only [estimate, bound, congrArg (fun t : ℝ => (L:ℝ)^2*t) kernel]

/-- A lower second moment for distinguishing two folded phases. Only the
kernels on their sum and difference need off-center upper bounds. -/
theorem phaseFejer_separation (s : Finset ℕ) (x y : ℝ)
    (difference : phaseFejer s (x-y) ≤ (s.card : ℝ)^2/16)
    (addition : phaseFejer s (x+y) ≤ (s.card : ℝ)^2/16) :
    7/8 * (s.card : ℝ)^2 ≤ ∑ u ∈ s, ∑ v ∈ s,
      (Real.cos (((u : ℝ)-v)*x) - Real.cos (((u : ℝ)-v)*y))^2 := by
  have identity (a b : ℝ) : 2*(Real.cos a - Real.cos b)^2 =
      2 + Real.cos (2*a) + Real.cos (2*b) - 2*Real.cos (a-b) - 2*Real.cos (a+b) := by
    rw [Real.cos_two_mul, Real.cos_two_mul, Real.cos_sub, Real.cos_add]
    ring
  have expanded (u v : ℕ) := identity (((u : ℝ)-v)*x) (((u : ℝ)-v)*y)
  simp_rw [← mul_sub, ← mul_add, show ∀ a b : ℝ, 2*(a*b) = a*(2*b) by intros; ring] at expanded
  have totals := Finset.sum_congr (rfl : s = s) (fun u _ =>
    Finset.sum_congr (rfl : s = s) (fun v _ => expanded u v))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul] at totals
  have posX := phaseFejer_nonneg s (2*x)
  have posY := phaseFejer_nonneg s (2*y)
  unfold phaseFejer at difference addition posX posY
  linarith

/-- If a real score has second moment at least 7/8 and magnitude at most
two, at least a sixth of all choices have magnitude at least a half. -/
theorem phase_sixth_separated {α : Type*} (s : Finset α) (value : α → ℝ)
    (bounded : ∀ j ∈ s, |value j| ≤ 2)
    (moment : 7/8*(s.card : ℝ) ≤ ∑ j ∈ s, (value j)^2) :
    s.card ≤ 6*(s.filter (fun j => (1:ℝ)/2 ≤ |value j|)).card := by
  classical
  let good (j : α) := (1:ℝ)/2 ≤ |value j|
  have upper (j) (hj : j ∈ s) :
      (value j)^2 ≤ 1/4 + (if good j then (15:ℝ)/4 else 0) := by
    by_cases g : good j
    · simp only [g, if_true]
      nlinarith [sq_abs (value j), abs_nonneg (value j), bounded j hj,
        mul_self_le_mul_self (abs_nonneg (value j)) (bounded j hj)]
    · simp only [g, if_false, add_zero]
      have h : |value j| ≤ 1/2 := le_of_lt (lt_of_not_ge g)
      nlinarith [sq_abs (value j), mul_self_le_mul_self (abs_nonneg (value j)) h]
  have total := Finset.sum_le_sum upper
  rw [Finset.sum_add_distrib, ← Finset.sum_filter] at total
  simp only [Finset.sum_const, nsmul_eq_mul] at total
  have res : (s.card : ℝ) ≤ 6*((s.filter good).card : ℝ) := by linarith
  exact_mod_cast res

private theorem phase_sine_floor {u d : ℝ} (hd : 0 ≤ d) (left : d ≤ u)
    (right : d ≤ 1-u) : 2*d ≤ |Real.sin (Real.pi*u)| := by
  have half (v : ℝ) (hv : 0 ≤ v) (hv' : v ≤ 1/2) : 2*v ≤ Real.sin (Real.pi*v) := by
    have h := Real.le_sin_mul (x := 2*v) (by linarith) (by linarith)
    rwa [show Real.pi/2*(2*v) = Real.pi*v by ring] at h
  by_cases h : u ≤ 1/2
  · exact (by linarith : 2*d ≤ 2*u) |>.trans ((half u (hd.trans left) h).trans (le_abs_self _))
  · rw [show Real.pi*u = Real.pi-Real.pi*(1-u) by ring, Real.sin_pi_sub]
    exact (by linarith : 2*d ≤ 2*(1-u)) |>.trans
      ((half (1-u) (hd.trans right) (by linarith)).trans (le_abs_self _))

/-- Two ordered phases in [0,1/2] separated by at least 2/L turns have
a clipped-score separation on at least one sixth of the L² frequency choices.
Taking L = 16*l corresponds to separation 1/(8*l). -/
theorem phase_folded_sixth {L : ℕ} {x y : ℝ} (hy : 0 ≤ y) (ordered : y ≤ x)
    (hx : x ≤ 1/2) (far : 2 ≤ L*(x-y)) :
    L*L ≤ 6*(((Finset.range L) ×ˢ (Finset.range L)).filter (fun uv =>
      (1:ℝ)/2 ≤ |Real.cos (((uv.1:ℝ)-uv.2)*(2*Real.pi*x)) -
        Real.cos (((uv.1:ℝ)-uv.2)*(2*Real.pi*y))|)).card := by
  classical
  have off (u : ℝ) (left : x-y ≤ u) (right : x-y ≤ 1-u) :
      phaseFejer (range L) (2*Real.pi*u) ≤ (L:ℝ)^2/16 := by
    apply phaseFejer_offCenter
    rw [show 2*Real.pi*u/2=Real.pi*u by ring]
    have b := mul_le_mul_of_nonneg_left (phase_sine_floor (sub_nonneg.mpr ordered) left right)
      (Nat.cast_nonneg L : (0:ℝ) ≤ L)
    linarith
  have moment := phaseFejer_separation (range L) (2*Real.pi*x) (2*Real.pi*y)
    (by rw [← mul_sub, Finset.card_range]; apply off <;> linarith)
    (by rw [← mul_add, Finset.card_range]; apply off <;> linarith)
  rw [Finset.card_range] at moment
  let score (uv : ℕ × ℕ) := Real.cos (((uv.1:ℝ)-uv.2)*(2*Real.pi*x)) -
    Real.cos (((uv.1:ℝ)-uv.2)*(2*Real.pi*y))
  have bound (uv : ℕ × ℕ) : |score uv| ≤ 2 := by
    apply abs_le.mpr
    dsimp [score]
    constructor <;> linarith [Real.neg_one_le_cos (((uv.1:ℝ)-uv.2)*(2*Real.pi*x)),
      Real.cos_le_one (((uv.1:ℝ)-uv.2)*(2*Real.pi*x)),
      Real.neg_one_le_cos (((uv.1:ℝ)-uv.2)*(2*Real.pi*y)),
      Real.cos_le_one (((uv.1:ℝ)-uv.2)*(2*Real.pi*y))]
  have pairMoment : 7/8 * (((range L ×ˢ range L).card : ℕ):ℝ) ≤
      ∑ j ∈ range L ×ˢ range L, score j^2 := by
    simpa only [Finset.card_product, Finset.card_range, Nat.cast_mul, Nat.cast_pow, ← sq,
      Finset.sum_product, score] using moment
  simpa only [Finset.card_product, Finset.card_range, score] using
    phase_sixth_separated (range L ×ˢ range L) score (fun j _ => bound j) pairMoment

/-- Double counting chooses one frequency separating at least a sixth of
any remaining collection of pairs, including repeated frequency choices
represented by different elements of the index set. -/
theorem phase_greedy_sixth {α β : Type*} (choices : Finset α) (pairs : Finset β)
    (nonempty : choices.Nonempty) (separates : α → β → Bool)
    (coverage : ∀ p ∈ pairs, choices.card ≤ 6*(choices.filter (fun j => separates j p)).card) :
    ∃ j ∈ choices, pairs.card ≤ 6*(pairs.filter (fun p => separates j p)).card := by
  classical
  have counted : ∑ p ∈ pairs, (choices.filter (fun j => separates j p)).card =
        ∑ j ∈ choices, (pairs.filter (fun p => separates j p)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  by_contra! none
  have lower := Finset.sum_le_sum coverage
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, counted] at lower
  have upper := Finset.sum_lt_sum_of_nonempty nonempty none
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at upper
  rw [Nat.mul_comm pairs.card] at lower
  omega

/-- Pairs still unidentified after a finite set of measurement choices. -/
noncomputable def phaseUncovered {α β : Type*} (queries : Finset α) (pairs : Finset β)
    (separates : α → β → Bool) : Finset β := by
  classical
  exact pairs.filter (fun p => ∀ j ∈ queries, separates j p = false)

/-- Repeating the double-counting choice k times leaves at most (5/6)^k of
the original pairs. The selected queries depend only on the separation table. -/
theorem phase_greedy_iterations {α β : Type*} (choices : Finset α) (pairs : Finset β)
    (nonempty : choices.Nonempty) (separates : α → β → Bool)
    (coverage : ∀ p ∈ pairs, choices.card ≤ 6*(choices.filter (fun j => separates j p)).card)
    (k : ℕ) : ∃ selected ⊆ choices, selected.card ≤ k ∧
      6^k*(phaseUncovered selected pairs separates).card ≤ 5^k*pairs.card := by
  classical
  induction k with
  | zero => exact ⟨∅, by simp, by simp, by simp [phaseUncovered]⟩
  | succ k ih =>
    obtain ⟨selected, subset, size, shrink⟩ := ih
    let remaining := phaseUncovered selected pairs separates
    have inPairs : remaining ⊆ pairs := Finset.filter_subset _ _
    obtain ⟨j, hj, hits⟩ := phase_greedy_sixth choices remaining nonempty separates
      (fun p hp => coverage p (inPairs hp))
    let misses := remaining.filter (fun p => ¬separates j p)
    have partition := Finset.filter_card_add_filter_neg_card_eq_card
      (s := remaining) (fun p => (separates j p : Prop))
    have oneStep : 6*misses.card ≤ 5*remaining.card := by
      dsimp [misses]
      omega
    have update : phaseUncovered (insert j selected) pairs separates = misses := by
      ext p
      simp [phaseUncovered, misses, remaining, and_assoc, and_left_comm, and_comm]
    refine ⟨insert j selected, Finset.insert_subset hj subset,
      (Finset.card_insert_le _ _).trans (Nat.succ_le_succ size), ?_⟩
    rw [update, pow_succ, pow_succ]
    calc
      6^k*6*misses.card = 6^k*(6*misses.card) := by ring
      _ ≤ 6^k*(5*remaining.card) := Nat.mul_le_mul_left _ oneStep
      _ = 5*(6^k*remaining.card) := by ring
      _ ≤ 5*(5^k*pairs.card) := Nat.mul_le_mul_left _ shrink
      _ = 5^k*5*pairs.card := by ring

/-- Fewer than 2^a pairs can all be separated by at most 4a queries, since
(6/5)^4 > 2. This set is fixed before any observations are taken. -/
theorem phase_greedy_log_cover {α β : Type*} (choices : Finset α) (pairs : Finset β)
    (nonempty : choices.Nonempty) (separates : α → β → Bool)
    (coverage : ∀ p ∈ pairs, choices.card ≤ 6*(choices.filter (fun j => separates j p)).card)
    {a : ℕ} (few : pairs.card < 2^a) :
    ∃ selected ⊆ choices, selected.card ≤ 4*a ∧
      ∀ p ∈ pairs, ∃ j ∈ selected, separates j p = true := by
  classical
  obtain ⟨found, subset, size, shrink⟩ :=
    phase_greedy_iterations choices pairs nonempty separates coverage (4*a)
  refine ⟨found, subset, size, ?_⟩
  have power : 5^(4*a)*2^a ≤ 6^(4*a) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by decide) _
  have strict := (Nat.mul_lt_mul_of_pos_left few (by positivity : 0 < 5^(4*a))).trans_le power
  intro p hp
  by_contra! missed
  have mem : p ∈ phaseUncovered found pairs separates := by
    simpa [phaseUncovered, hp] using missed
  have positive := Finset.card_pos.mpr ⟨p, mem⟩
  have lower := Nat.mul_le_mul_left (6^(4*a)) positive
  rw [Nat.mul_one] at lower
  omega

/-- Two grid points that both fit the same observations cannot be a pair
separated by the chosen measurements. -/
theorem phase_grid_localization {α β : Type*} (queries : Finset α) (location : β → ℝ)
    (table : α → β → ℝ) (observed : α → ℝ) (radius error gap : ℝ)
    (separated : ∀ a b, radius ≤ |location a - location b| →
      ∃ j ∈ queries, gap ≤ |table j a - table j b|)
    (slack : 2*error < gap) {a b : β}
    (fitA : ∀ j ∈ queries, |table j a - observed j| ≤ error)
    (fitB : ∀ j ∈ queries, |table j b - observed j| ≤ error) :
    |location a - location b| < radius := by
  by_contra! far
  obtain ⟨j, hj, sep⟩ := separated a b far
  have tri := abs_sub_le (table j a) (observed j) (table j b)
  rw [abs_sub_comm (observed j) (table j b)] at tri
  linarith [fitA j hj, fitB j hj]

end PrimeFactors
