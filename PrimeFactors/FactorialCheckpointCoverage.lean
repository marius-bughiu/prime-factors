import PrimeFactors.FoldedFactorial
import PrimeFactors.ShortPascalRow
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Positivity

/-! Coverage of the penultimate checkpoint in the 210-wheel factorial search. -/
namespace PrimeFactors.FactorialCheckpointCoverage

/-- Number of whole wheel cycles in a complete checkpoint of block width h. -/
def footprint (h : ℕ) : ℕ := h * (48 * h + 1)

/-- The real feasible interval and the rounded, wheel-aligned integer grid. -/
structure Grid (l s a : ℝ) (C : ℕ) : Prop where
  base_lower : l - 1 ≤ a
  base_upper : a ≤ l + 212
  end_lower : s - 212 ≤ a + 210 * C
  end_upper : a + 210 * C ≤ s

/-- Rounding the first integer to the next wheel boundary and retaining all complete cycles
meets the error bounds in Grid. -/
theorem aligned_grid {l s : ℝ} {first upper : ℕ} (hf : 0 < first)
    (fl : l ≤ first) (fu : (first : ℝ) ≤ l + 3)
    (ul : (upper : ℝ) ≤ s) (uu : s < (upper : ℝ) + 1)
    (fits : ((first - 1 + 209) / 210) * 210 ≤ upper) :
    let a := ((first - 1 + 209) / 210) * 210
    Grid l s a ((upper - a) / 210) := by
  let a := ((first - 1 + 209) / 210) * 210
  let C := (upper - a) / 210
  change Grid l s a C
  have ha : first ≤ a + 1 ∧ a ≤ first + 208 := by dsimp [a]; omega
  have he : upper ≤ a + 210 * C + 209 ∧ a + 210 * C ≤ upper := by
    change a ≤ upper at fits
    dsimp only [C]
    omega
  have al : (first : ℝ) ≤ a + 1 := by exact_mod_cast ha.1
  have au : (a : ℝ) ≤ first + 208 := by exact_mod_cast ha.2
  have el : (upper : ℝ) ≤ a + 210 * C + 209 := by exact_mod_cast he.1
  have eu : (a : ℝ) + 210 * C ≤ upper := by exact_mod_cast he.2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The executable's equal-width endpoints give a grid directly from the public product.
The product band here is the full-product-bit-width band. -/
theorem product_grid {n B : ℕ} (bp : 2 ≤ B) (band : 2*B^2 ≤ n) (top : n < 4*B^2)
    (width : (2 : ℝ)^40 ≤ Real.sqrt n - n / (2*(B : ℝ))) :
    let f := ShortPascalRow.lower n B
    let a := ((f-1+209) / 210) * 210
    Grid (n / (2*(B : ℝ))) (Real.sqrt n) a ((n.sqrt-a)/210) := by
  let d := 2*B-1
  let q := (n-1)/d
  let f := max B (q+1)
  let a := ((f-1+209)/210)*210
  change Grid _ _ a ((n.sqrt-a)/210)
  have dp : 0 < d := by dsimp [d]; omega
  have dd : d+1=2*B := by dsimp [d]; omega
  have bb : B ≤ d := by dsimp [d]; omega
  have np : 0<n := by nlinarith only [bp, band, Nat.zero_le ((B-1)^2)]
  have qbound : q < 4*B := by
    apply (Nat.div_lt_iff_lt_mul dp).2
    have room := Nat.mul_le_mul_left (4*B) bb
    nlinarith only [top, room, Nat.sub_le n 1]
  have qlo := Nat.div_mul_le_self (n-1) d
  have qhi := Nat.lt_mul_div_succ (n-1) dp
  change q*d ≤ n-1 at qlo
  change n-1 < d*(q+1) at qhi
  have times := congrArg (fun x => x*q) dd
  dsimp at times
  have nsub := Nat.sub_add_cancel np
  have flu : n ≤ (2*B)*f := by
    have t := Nat.mul_le_mul (by omega : d ≤ 2*B) (le_max_right B (q+1))
    change d*(q+1) ≤ (2*B)*f at t
    omega
  have fuu : (2*B)*f ≤ n+6*B := by
    rcases le_total B (q+1) with h | h
    · rw [show f=q+1 from max_eq_right h]
      nlinarith only [qbound, qlo, times, nsub]
    · rw [show f=B from max_eq_left h]
      nlinarith only [band, Nat.zero_le B]
  have pos : (0:ℝ) < 2*(B:ℝ) := by positivity
  have fl : n/(2*(B:ℝ)) ≤ f := (div_le_iff₀ pos).mpr (by
    have h : (n:ℝ) ≤ 2*(B:ℝ)*f := by exact_mod_cast flu
    linarith)
  have fu : (f:ℝ) ≤ n/(2*(B:ℝ))+3 := by
    have h : 2*(B:ℝ)*f ≤ n+6*(B:ℝ) := by exact_mod_cast fuu
    have h' : (f:ℝ)-3 ≤ n/(2*(B:ℝ)) := (le_div_iff₀ pos).mpr (by linarith)
    linarith
  have ul : (n.sqrt:ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' n)
  have uu : Real.sqrt n < (n.sqrt:ℝ)+1 := (Real.sqrt_lt' (by positivity)).mpr
    (by exact_mod_cast Nat.lt_succ_sqrt' n)
  have fpos : 0<f := by dsimp [f]; omega
  have amax : a ≤ f+208 := by dsimp [a]; omega
  have fits : a ≤ n.sqrt := by
    have h : (a:ℝ) ≤ f+208 := by exact_mod_cast amax
    norm_num at width
    exact_mod_cast (show (a:ℝ) ≤ n.sqrt by linarith only [h, fu, uu, width])
  exact aligned_grid fpos fl fu ul uu fits

private theorem cap_of_footprint {j h cap : ℕ} (jp : 0 < j) (jh : j ≤ h)
    (fits : footprint h ≤ cap) : min (48 * j + 1) (cap / j) = 48 * j + 1 := by
  apply min_eq_left
  apply (Nat.le_div_iff_mul_le jp).2
  rw [Nat.mul_comm]
  exact (Nat.mul_le_mul jh (by omega : 48 * j + 1 ≤ 48 * h + 1)).trans fits

/-- The floor in the forward sample count permits the complete interpolation grid at
every width through the penultimate width h. -/
theorem forward_sample_cap {h C j : ℕ} (lower : 96 * h ^ 2 < C)
    (jp : 0 < j) (jh : j ≤ h) : min (48 * j + 1) (C / j) = 48 * j + 1 := by
  apply cap_of_footprint jp jh
  unfold footprint
  have aux : h ≤ h * h := Nat.le_mul_of_pos_right h (by omega)
  nlinarith only [lower, aux]

/-- The folded center and hence the sample cap is clipped to a multiple of the
terminal block width, as in the complete search. -/
theorem folded_sample_cap {h C j : ℕ} (lower : 96 * (2 * h) ^ 2 < C)
    (jp : 0 < j) (jh : j ≤ h) :
    min (48 * j + 1) ((2 * h * (C / (4 * h))) / j) = 48 * j + 1 := by
  apply cap_of_footprint jp jh
  have hp : 0 < h := by omega
  have slots : 96 * h ≤ C / (4 * h) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).2
    nlinarith only [lower]
  unfold footprint
  have aux := Nat.mul_le_mul_left (2 * h) slots
  have hh : h ≤ h * h := Nat.le_mul_of_pos_right h hp
  nlinarith only [aux, hh]

private theorem real_footprint (h : ℕ) :
    (footprint h : ℝ) = (h : ℝ) * (48 * h + 1) := by
  unfold footprint
  push_cast
  rfl

/-- The forward checkpoint contains the entire indicated rank interval. The lower
boundary is open to match the evaluator's positive wheel offsets. -/
theorem forward_rank {l s a R : ℝ} {C h : ℕ} (grid : Grid l s a C)
    (width : (2 : ℝ)^40 ≤ s - l) (upper : C ≤ 96 * (2*h)^2)
    (rl : 1 / 100 ≤ R) (ru : R ≤ 11 / 100) :
    a < l + R * (s-l) ∧ l + R * (s-l) ≤ a + 210 * (footprint h : ℝ) := by
  obtain ⟨al, au, el, _⟩ := grid
  norm_num at width
  have Dp : 0 ≤ s-l := by linarith
  have plo := mul_le_mul_of_nonneg_right rl Dp
  have phi := mul_le_mul_of_nonneg_right ru Dp
  have cu : (C : ℝ) ≤ 96 * (2*(h : ℝ))^2 := by exact_mod_cast upper
  have hn : 0 ≤ (h : ℝ) := by positivity
  rw [real_footprint]
  constructor
  · linarith only [au, width, plo]
  · nlinarith only [al, au, el, width, phi, cu, hn]

/-- The folded checkpoint straddles the *implemented* midpoint, including the
effect of flooring the number of terminal blocks. -/
theorem folded_rank {l s a R : ℝ} {C h : ℕ} (grid : Grid l s a C)
    (width : (2 : ℝ)^40 ≤ s-l) (hp : 0 < h)
    (lower : 96 * (2*h)^2 < C) (upper : C ≤ 96 * (4*h)^2)
    (rl : 48 / 100 ≤ R) (ru : R ≤ 52 / 100) :
    let center := a + 210 * (2 * h * (C / (4*h)) : ℕ)
    center - 210 * (footprint h : ℝ) < l + R * (s-l) ∧
      l + R * (s-l) ≤ center + 210 * (footprint h : ℝ) := by
  obtain ⟨al, au, el, eu⟩ := grid
  let E := 4 * h * (C / (4*h))
  have dp : 0 < 4*h := by positivity
  have hrem := Nat.mod_add_div C (4*h)
  have hmod := Nat.mod_lt C dp
  have e0 : E ≤ C := by dsimp [E]; omega
  have e1 : C < E + 4*h := by dsimp [E]; omega
  have e0r : (E : ℝ) ≤ C := by exact_mod_cast e0
  have e1r : (C : ℝ) < E + 4*(h : ℝ) := by exact_mod_cast e1
  have center_eq : 210 * ((2 * h * (C / (4*h)) : ℕ) : ℝ) = 105 * (E : ℝ) := by
    dsimp only [E]
    push_cast
    ring
  dsimp only
  rw [center_eq, real_footprint]
  norm_num at width
  have Dp : 0 ≤ s-l := by linarith
  have plo := mul_le_mul_of_nonneg_right rl Dp
  have phi := mul_le_mul_of_nonneg_right ru Dp
  have cu : (C : ℝ) ≤ 96 * (4*(h : ℝ))^2 := by exact_mod_cast upper
  have cl : 96 * (2*(h : ℝ))^2 < C := by exact_mod_cast lower
  have hn : 0 ≤ (h : ℝ) := by positivity
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hp
  have hh := mul_nonneg hn (sub_nonneg.mpr h1)
  have rad : (s-l-424)/32 ≤ 210 * (h : ℝ) * (48*h+1) := by
    nlinarith only [cu, au, el, hn]
  have shift : 420 * (h : ℝ) ≤ (s-l+1)/192 := by
    nlinarith only [cl, eu, al, hh]
  have midlo : (s+l)/2 - 107 - 420*(h : ℝ) < a + 105 * E := by
    linarith only [al, el, e1r]
  have midhi : a + 105 * E ≤ (s+l)/2 + 106 := by
    linarith only [au, eu, e0r]
  constructor
  · linarith only [rad, plo, midhi, width]
  · linarith only [rad, phi, midlo, width, shift]

/-- At the stated feasible width the stopping rule first succeeds at some V=4·2^k.
The strict lower inequality tests the immediately preceding dyadic width. -/
theorem terminal_width {l s a : ℝ} {C : ℕ} (grid : Grid l s a C)
    (width : (2 : ℝ)^40 ≤ s-l) :
    ∃ k : ℕ, 96*(2*2^k)^2 < C ∧ C ≤ 96*(4*2^k)^2 := by
  have large : 384 < C := by
    have hu := grid.base_upper
    have hl := grid.end_lower
    norm_num at width
    exact_mod_cast (show (384:ℝ)<C by linarith)
  have exists_width : ∃ k : ℕ, C ≤ 96*(4*2^k)^2 := by
    have h : C ≤ 2^C := Nat.le_of_lt Nat.lt_two_pow_self
    have d : 2^C ≤ (2^C)*(2^C) := Nat.le_mul_of_pos_right _ (by positivity)
    exact ⟨C, by nlinarith only [h,d]⟩
  let k := Nat.find exists_width
  have hk : C ≤ 96*(4*2^k)^2 := Nat.find_spec exists_width
  refine ⟨k, ?_, hk⟩
  cases eq : k with
  | zero => simpa using large
  | succ j =>
    have before : j < Nat.find exists_width := by change j < k; omega
    have hm := Nat.find_min exists_width before
    change ¬C ≤ 96*(4*2^j)^2 at hm
    rw [pow_succ 2 j, show 2*(2^j*2) = 4*2^j by ring]
    exact lt_of_not_ge hm

/-- A terminal dyadic width V=4·2^k has at least 24V terminal values, even
after flooring. -/
theorem terminal_slots (k C : ℕ) (lower : 96 * (2 * 2^k)^2 < C) :
    24 * (4 * 2^k) ≤ C / (4 * 2^k) := by
  apply (Nat.le_div_iff_mul_le (by positivity)).2
  nlinarith only [lower]

private theorem stage_sum (a b k : ℕ) :
    (∑ i ∈ Finset.range k, (a*2^i+b)) ≤ (a+b)*2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hb : b ≤ b * 2^k := Nat.le_mul_of_pos_right b (by positivity)
    nlinarith only [ih, hb]

/-- Share of submitted input coefficients in the final ordinary convolution. -/
theorem ordinary_share (k g : ℕ) (slots : 24 * (4*2^k) ≤ g) :
    37 * FoldedFactorial.ordinaryInputs 48 g k ≤ 100 * (48*2^(k+1) + 2*g) := by
  have bound := stage_sum 240 2 (k+1)
  unfold FoldedFactorial.ordinaryInputs
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at bound ⊢
  simp only [pow_succ] at bound ⊢
  omega

/-- Share of submitted input coefficients in the final folded convolution. -/
theorem folded_share (k g : ℕ) (slots : 24 * (4*2^k) ≤ g) :
    49 * FoldedFactorial.foldedInputs 48 g k ≤ 100 * (3*48*2^k + 2*g + 2) := by
  have bound := stage_sum 336 4 k
  unfold FoldedFactorial.foldedInputs
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at bound ⊢
  omega

end PrimeFactors.FactorialCheckpointCoverage
