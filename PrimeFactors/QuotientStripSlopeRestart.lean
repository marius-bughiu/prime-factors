import PrimeFactors.QuotientStripSlopeAlignment

namespace PrimeFactors.QuotientStripSlopeRestart
open QuotientStripScheduleCost QuotientStripWideSlopeGeometry

set_option exponentiation.threshold 4096

noncomputable def startAt (n origin j : ℕ) : ℕ := origin + j*width n
noncomputable def stopAt (n origin j : ℕ) : ℕ := startAt n origin j + width n - 1

/-- Inclusive public lower endpoint when both factors have 1,024 bits and the
partner is at most D. For positive N, the integer quotient here is ceil(N/D). -/
def clippedStart (n : ℕ) (D : ℕ := 2^1024) : ℕ :=
  max (first n) (max ((n-1)/D+1) (2^1023))

/-- Move the schedule origin without changing any stationary-band endpoint estimates. -/
theorem aligned_from {n : ℕ} {u v t L : ℝ}
    (G : Band (Real.sqrt n) (roundedSixth n) u v t L) (origin : ℕ) (origin_bound : (origin:ℝ) ≤ t-L) :
    ∃ i0 k : ℕ,
      (startAt n origin i0 : ℝ) ≤ t-L+2*(roundedSixth n : ℝ) ∧
      t-4*(roundedSixth n : ℝ) ≤ (stopAt n origin (i0+k) : ℝ) ∧
      ∀ j ≤ k, t-L ≤ (startAt n origin (i0+j) : ℝ) ∧
        (stopAt n origin (i0+j) : ℝ) ≤ t ∧ stopAt n origin (i0+j) ≤ n.sqrt := by
  have wpos : 0<(width n : ℝ) := by
    simp only [width, Nat.cast_mul, Nat.cast_ofNat]
    linarith [G.rp]
  have wn : 0 < width n := by exact_mod_cast wpos
  have w : (width n : ℝ) = 2*(roundedSixth n : ℝ) := by simp [width]
  have start (j : ℕ) : (startAt n origin j : ℝ) = (origin:ℝ)+(j:ℝ)*(width n:ℝ) := by
    simp [startAt]
  have stop (j : ℕ) : (stopAt n origin j : ℝ) = (origin:ℝ)+(j:ℝ)*(width n:ℝ)+(width n:ℝ)-1 := by
    rw [stopAt, Nat.cast_sub (by omega : 1 ≤ startAt n origin j + width n)]
    simp [start]
  obtain ⟨i,k,hstart,hstop,hall⟩ := QuotientStripSlopeAlignment.align_grid wpos origin_bound
    (show 2*(width n : ℝ) ≤ L by rw [w]; linarith [G.span_bounds.2,G.rp])
  refine ⟨i,k,?_,?_,?_⟩
  · rw [start, ← w]
    exact hstart
  · rw [stop]
    linarith only [hstop,w]
  · intro j hj
    obtain ⟨a,b⟩ := hall j hj
    have bt : (stopAt n origin (i+j) : ℝ) ≤ t := by rwa [stop]
    refine ⟨by rwa [start],bt,Nat.le_sqrt'.mpr ?_⟩
    have bs : (stopAt n origin (i+j) : ℝ) ≤ Real.sqrt n := by linarith [G.center.2,G.tp]
    have sq := pow_le_pow_left₀ (by positivity) bs 2
    rw [Real.sq_sqrt (by positivity)] at sq
    exact_mod_cast sq


/-- Every stationary run starts at or beyond this uniform fraction of the real square root. -/
theorem stationary_fits {s r u v t L : ℝ} (G : Band s r u v t L) :
    17*s/20 ≤ t-L := by
  linarith only [G.near_center,G.span_bounds.1,G.basic.2.2.2.2.le]

private theorem sqrt_lower {n : ℕ} (lo : 2^2047 ≤ n) :
    11*(2:ℝ)^1020 ≤ Real.sqrt n := by
  apply Real.le_sqrt_of_sq_le
  exact_mod_cast (show (11*2^1020)^2 ≤ 2^2047 by decide +kernel).trans lo

/-- The ordinary balanced interval always starts early enough on a full-width input. -/
theorem original_fits {n : ℕ} (lo : 2^2047 ≤ n) :
    (first n : ℝ) ≤ 17 * Real.sqrt n / 20 := by
  let a := ((n-1)/2).sqrt
  have ha : a^2 ≤ (n-1)/2 := Nat.sqrt_le' _
  have half : 2*((n-1)/2) ≤ n := by omega
  have bound : 2*(a:ℝ)^2 ≤ n := by exact_mod_cast (Nat.mul_le_mul_left 2 ha).trans half
  have sq := Real.sq_sqrt (by positivity : 0≤(n:ℝ))
  have estimate : 4*(a:ℝ) ≤ 3*Real.sqrt n := by
    by_contra! bad
    have h := mul_self_lt_mul_self (by positivity : (0:ℝ) ≤ 3*Real.sqrt n) bad
    nlinarith only [h,bound,sq,Nat.cast_nonneg (α:=ℝ) n]
  have start : (first n : ℝ) = (a:ℝ)+1 := by simp [first,a]
  rw [start]
  linarith only [estimate,sqrt_lower lo]

/-- Natural-number product bounds, with three partner units of room for rounding. -/
theorem product_root_bound {n : ℕ} (cut : 400*n ≤ 289*(2^1024-4)^2) :
    20*Real.sqrt n ≤ 17*((2:ℝ)^1024-4) := by
  have cast : (400:ℝ)*n ≤ 289*((2:ℝ)^1024-4)^2 := by
    have four : 4 ≤ (2:ℕ)^1024 := by decide +kernel
    exact_mod_cast cut
  by_contra! bad
  have pos : (0:ℝ) ≤ 17*((2:ℝ)^1024-4) := by norm_num
  have h := mul_self_lt_mul_self pos bad
  nlinarith only [h,cast,Real.sq_sqrt (by positivity : 0≤(n:ℝ))]

/-- Includes both the requested partner bound 2^1024 and the sharper 2^1024−1. -/
theorem clipped_fits {n D : ℕ} (lo : 2^2047 ≤ n)
    (cut : 400*n ≤ 289*(2^1024-4)^2) (partner : 2^1024-1 ≤ D) :
    (clippedStart n D : ℝ) ≤ 17 * Real.sqrt n / 20 := by
  let s := Real.sqrt (n:ℝ)
  let B := (2:ℝ)^1024
  have sLow : 11*(2:ℝ)^1020 ≤ s := sqrt_lower lo
  have half : B ≤ 2*s := by dsimp [B]; linarith only [sLow]
  have sPos : 0 ≤ s := Real.sqrt_nonneg _
  have sq : s^2 = n := Real.sq_sqrt (by positivity)
  have range : 20*s ≤ 17*(B-4) := product_root_bound cut
  have minD : B-1 ≤ (D:ℝ) := by
    have one : 1 ≤ (2:ℕ)^1024 := by decide +kernel
    dsimp only [B]
    exact_mod_cast partner
  have pos : 0 < (D:ℝ) := by
    dsimp [B] at minD
    linarith only [minD]
  have slope : 0 ≤ 17*s-20 := by linarith only [sLow]
  have base : 20*(n:ℝ) ≤ (17*s-20)*(B-1) := by
    nlinarith only [mul_le_mul_of_nonneg_right range sPos, sq, half, sLow]
  have budget := base.trans (mul_le_mul_of_nonneg_left minD slope)
  let q := (n-1)/D
  have prod : (q:ℝ)*D ≤ n := by
    exact_mod_cast (Nat.div_mul_le_self (n-1) D).trans (Nat.sub_le _ _)
  have cap : 20*((q:ℝ)+1) ≤ 17*s := by
    apply le_of_mul_le_mul_right (a := (D:ℝ)) _ pos
    nlinarith only [prod,budget]
  change ((max (first n) (max (q+1) (2^1023)) : ℕ) : ℝ) ≤ 17*s/20
  push_cast
  exact max_le (original_fits lo) (max_le (by linarith only [cap]) (by linarith only [sLow]))

end PrimeFactors.QuotientStripSlopeRestart
