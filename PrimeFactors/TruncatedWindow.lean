import PrimeFactors.Multiplier

namespace PrimeFactors

/-- The public window on a weighted sum, with relative squared-gap parameter `K`. -/
def weightedProductWindow (K a b N s : ℕ) : Prop :=
  4 * a * b * N ≤ s ^ 2 ∧ K * s ^ 2 ≤ (4 * K + 1) * a * b * N

/-- Both endpoints can be computed before the candidate sum is known. -/
theorem weightedProductWindow_iff_interval {K a b N s : ℕ} (hK : 0 < K) :
    weightedProductWindow K a b N s ↔
      ceilSqrt (4 * a * b * N) ≤ s ∧ s ≤ Nat.sqrt (((4*K+1)*a*b*N) / K) := by
  rw [ceilSqrt_le_iff, Nat.le_sqrt, Nat.le_div_iff_mul_le hK]
  simp only [weightedProductWindow, pow_two, mul_comm K]

/-- A short scaled-factor gap puts the true product inside its own sum window. -/
theorem weightedProductWindow_of_gap {K a b x y : ℕ}
    (gap : K * (Nat.dist (a*x) (b*y))^2 ≤ a*b*(x*y)) :
    weightedProductWindow K a b (x*y) (a*x+b*y) := by
  have id := multiplier_sum_square x y a b
  constructor
  · omega
  · nlinarith only [gap, congrArg (fun z : ℕ => K*z) id]

private theorem compare_window {K a b m N s : ℕ} (ab : 0 < a*b)
    (hm : weightedProductWindow K a b m s) (hn : weightedProductWindow K a b N s) :
    4*K*m ≤ (4*K+1)*N := by
  apply Nat.le_of_mul_le_mul_left (c := a*b) _ ab
  calc
    _ = K*(4*a*b*m) := by ring
    _ ≤ K*s^2 := Nat.mul_le_mul_left _ hm.1
    _ ≤ (4*K+1)*a*b*N := hn.2
    _ = _ := by ring

/-- Agreement of two sum windows bounds the absolute product error. -/
theorem product_error_of_weighted_windows {K a b m N s : ℕ} (ab : 0 < a*b)
    (hm : weightedProductWindow K a b m s) (hn : weightedProductWindow K a b N s) :
    4*K*(Nat.dist m N) ≤ N := by
  rcases le_total m N with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.mul_sub_left_distrib]
    have bound := compare_window ab hn hm
    rw [Nat.add_mul, Nat.one_mul] at bound
    omega
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.mul_sub_left_distrib]
    have bound := compare_window ab hm hn
    rw [Nat.add_mul, Nat.one_mul] at bound
    omega

/-- A truncated product check becomes exact once its period exceeds the error. -/
theorem eq_of_window_modEq {K a b m N M s : ℕ} (ab : 0 < a*b)
    (hm : weightedProductWindow K a b m s) (hn : weightedProductWindow K a b N s)
    (short : N < 4*K*M) (low : m ≡ N [MOD M]) : m = N := by
  have err := product_error_of_weighted_windows ab hm hn
  have dist : Nat.dist m N < M := by
    by_contra! bad
    have := Nat.mul_le_mul_left (4*K) bad
    omega
  rcases le_total m N with h | h
  · rw [Nat.dist_eq_sub_of_le h] at dist
    exact le_antisymm h (low.symm.le_of_lt_add (by omega))
  · rw [Nat.dist_eq_sub_of_le_right h] at dist
    exact le_antisymm (low.le_of_lt_add (by omega)) h

/-- Two linear comparisons select the unique floor numerator. -/
def floorSlopeStrip (a R x y : ℕ) : Prop := a*x ≤ R*y ∧ R*y < (a+1)*x

theorem floorSlopeStrip_iff {a R x y : ℕ} (hx : 0 < x) :
    floorSlopeStrip a R x y ↔ a = R*y/x := by
  unfold floorSlopeStrip
  rw [← Nat.le_div_iff_mul_le hx, ← Nat.div_lt_iff_lt_mul hx]
  omega

private theorem floor_in_range {R x y : ℕ} (hx : 0 < x) (ord : x ≤ y) (bal : y ≤ 2*x) :
    R ≤ R*y/x ∧ R*y/x ≤ 2*R := by
  refine ⟨(Nat.le_div_iff_mul_le hx).mpr (Nat.mul_le_mul_left R ord), ?_⟩
  apply Nat.le_of_mul_le_mul_right _ hx
  calc R*y/x*x ≤ R*y := Nat.div_mul_le_self _ _
    _ ≤ R*(2*x) := Nat.mul_le_mul_left R bal
    _ = _ := by ring

private theorem gap_from_scaled_dist {L a R x y : ℕ}
    (lo : L*Nat.dist (a*x) (R*y) ≤ a*x) (hi : L*Nat.dist (a*x) (R*y) ≤ R*y) :
    L^2*(Nat.dist (a*x) (R*y))^2 ≤ a*R*(x*y) := calc
  _ = (L*Nat.dist (a*x) (R*y)) * (L*Nat.dist (a*x) (R*y)) := by ring
  _ ≤ (a*x)*(R*y) := Nat.mul_le_mul lo hi
  _ = _ := by ring

private theorem floor_gap {a R x y : ℕ} (ra : R ≤ a) (strip : floorSlopeStrip a R x y) :
    R^2*(Nat.dist (a*x) (R*y))^2 ≤ a*R*(x*y) := by
  obtain ⟨hlo,hhi⟩ := strip
  rw [Nat.add_mul, Nat.one_mul] at hhi
  have d : Nat.dist (a*x) (R*y) ≤ x := by rw [Nat.dist_eq_sub_of_le hlo]; omega
  have close := (Nat.mul_le_mul_left R d).trans (Nat.mul_le_mul_right x ra)
  exact gap_from_scaled_dist close (close.trans hlo)

/-- All balanced positive pairs satisfy the fixed-denominator floor construction.
The right side uses the low product and one of `R+1` public linear windows. -/
theorem eq_iff_floor_window {R x y N M : ℕ} (hR : 0 < R) (hx : 0 < x)
    (ord : x ≤ y) (bal : y ≤ 2*x) (short : N < 4*R^2*M) :
    x*y = N ↔ x*y ≡ N [MOD M] ∧ ∃ a, R ≤ a ∧ a ≤ 2*R ∧
      floorSlopeStrip a R x y ∧ weightedProductWindow (R^2) a R N (a*x+R*y) := by
  constructor
  · rintro rfl
    obtain ⟨lo,hi⟩ := floor_in_range (R := R) hx ord bal
    have strip := (floorSlopeStrip_iff (a := R*y/x) hx).mpr rfl
    exact ⟨Nat.ModEq.refl _, R*y/x, lo, hi, strip,
      weightedProductWindow_of_gap (floor_gap lo strip)⟩
  · rintro ⟨low,a,lo,_,strip,win⟩
    exact eq_of_window_modEq (Nat.mul_pos (hR.trans_le lo) hR)
      (weightedProductWindow_of_gap (floor_gap lo strip)) win short low

/-- Both inequalities are linear in the candidate wires `x,y` at each public slope. -/
def nearestSlopeStrip (a R x y : ℕ) : Prop :=
  2*(a*x) ≤ 2*(R*y)+x ∧ 2*(R*y) ≤ 2*(a*x)+x

private theorem nearest_in_range {R x y : ℕ} (hx : 0 < x) (ord : x ≤ y) (bal : y ≤ 2*x) :
    ∃ a, R ≤ a ∧ a ≤ 2*R ∧ nearestSlopeStrip a R x y := by
  let f := R*y/x
  obtain ⟨lo,hi⟩ := floor_in_range (R := R) hx ord bal
  change R ≤ f at lo
  change f ≤ 2*R at hi
  obtain ⟨hlo,hhi⟩ := (floorSlopeStrip_iff (a := f) hx).mpr rfl
  rw [Nat.add_mul, Nat.one_mul] at hhi
  by_cases below : 2*(R*y) ≤ 2*(f*x)+x
  · exact ⟨f,lo,hi,by unfold nearestSlopeStrip; omega⟩
  · have strict : f < 2*R := by
      have endpoint : R*y ≤ (2*R)*x := by
        calc R*y ≤ R*(2*x) := Nat.mul_le_mul_left R bal
          _ = _ := by ring
      by_contra! h
      have eq : f = 2*R := by omega
      rw [← eq] at endpoint
      omega
    refine ⟨f+1,by omega,by omega,?_⟩
    unfold nearestSlopeStrip
    rw [Nat.add_mul, Nat.one_mul]
    omega

private theorem nearest_gap {a R x y : ℕ} (ra : R ≤ a) (ord : x ≤ y)
    (strip : nearestSlopeStrip a R x y) :
    (2*R)^2*(Nat.dist (a*x) (R*y))^2 ≤ a*R*(x*y) := by
  obtain ⟨left,right⟩ := strip
  have d : 2*Nat.dist (a*x) (R*y) ≤ x := by
    rcases le_total (a*x) (R*y) with h | h
    · rw [Nat.dist_eq_sub_of_le h]; omega
    · rw [Nat.dist_eq_sub_of_le_right h]; omega
  have close : (2*R)*Nat.dist (a*x) (R*y) ≤ R*x := calc
    _ = R*(2*Nat.dist (a*x) (R*y)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left R d
  exact gap_from_scaled_dist (close.trans (Nat.mul_le_mul_right x ra))
    (close.trans (Nat.mul_le_mul_left R ord))

/-- Nearest-numerator rounding gains two further omitted bits with the same
`R+1` windows. Either slope may be used at a tie. -/
theorem eq_iff_nearest_window {R x y N M : ℕ} (hR : 0 < R) (hx : 0 < x)
    (ord : x ≤ y) (bal : y ≤ 2*x) (short : N < 16*R^2*M) :
    x*y = N ↔ x*y ≡ N [MOD M] ∧ ∃ a, R ≤ a ∧ a ≤ 2*R ∧
      nearestSlopeStrip a R x y ∧ weightedProductWindow ((2*R)^2) a R N (a*x+R*y) := by
  constructor
  · rintro rfl
    obtain ⟨a,lo,hi,strip⟩ := nearest_in_range (R := R) hx ord bal
    exact ⟨Nat.ModEq.refl _,a,lo,hi,strip,
      weightedProductWindow_of_gap (nearest_gap lo ord strip)⟩
  · rintro ⟨low,a,lo,_,strip,win⟩
    exact eq_of_window_modEq (Nat.mul_pos (hR.trans_le lo) hR)
      (weightedProductWindow_of_gap (nearest_gap lo ord strip)) win (by nlinarith only [short]) low

private theorem dyadic_truncation_bound (t c n : ℕ) :
    2^n ≤ 2^c*(2^t)^2*2^(n-(2*t+c)) := calc
  _ ≤ 2^(t*2+c + (n-(2*t+c))) := Nat.pow_le_pow_right (by decide) (by omega)
  _ = _ := by rw [pow_add, pow_add, pow_mul]; ring

/-- With `R=2^t`, nearest rounding retains just `n-(2t+4)` low bits. Natural
subtraction also covers small inputs for which the retained width is zero. -/
theorem dyadic_nearest_window {n t N x y : ℕ} (small : N < 2^n) (hx : 0 < x)
    (ord : x ≤ y) (bal : y ≤ 2*x) :
    x*y = N ↔ x*y ≡ N [MOD 2^(n-(2*t+4))] ∧
      ∃ a, 2^t ≤ a ∧ a ≤ 2*2^t ∧ nearestSlopeStrip a (2^t) x y ∧
        weightedProductWindow ((2*2^t)^2) a (2^t) N (a*x+2^t*y) :=
  eq_iff_nearest_window (by positivity) hx ord bal (small.trans_le (dyadic_truncation_bound t 4 n))

/-- The floor-slope variant retains `n-(2t+2)` low bits. -/
theorem dyadic_floor_window {n t N x y : ℕ} (small : N < 2^n) (hx : 0 < x)
    (ord : x ≤ y) (bal : y ≤ 2*x) :
    x*y = N ↔ x*y ≡ N [MOD 2^(n-(2*t+2))] ∧
      ∃ a, 2^t ≤ a ∧ a ≤ 2*2^t ∧ floorSlopeStrip a (2^t) x y ∧
        weightedProductWindow ((2^t)^2) a (2^t) N (a*x+2^t*y) :=
  eq_iff_floor_window (by positivity) hx ord bal (small.trans_le (dyadic_truncation_bound t 2 n))

/-- A single unweighted sum window suffices when the low-product period is
greater than one eighth of the target. -/
theorem eq_iff_one_balanced_window {x y N M : ℕ} (ord : x ≤ y) (bal : y ≤ 2*x)
    (short : N < 8*M) :
    x*y = N ↔ x*y ≡ N [MOD M] ∧ weightedProductWindow 2 1 1 N (x+y) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le ord
  have dd : d ≤ x := by omega
  have bound : 2*d^2 ≤ x*(x+d) := by
    nlinarith only [Nat.mul_le_mul_right (x+2*d) dd]
  have gap : 2*(Nat.dist (1*x) (1*(x+d)))^2 ≤ 1*1*(x*(x+d)) := by
    simpa [Nat.dist_eq_sub_of_le (Nat.le_add_right x d)] using bound
  have win := weightedProductWindow_of_gap gap
  simp only [one_mul] at win
  constructor
  · rintro rfl
    exact ⟨Nat.ModEq.refl _,win⟩
  · rintro ⟨low,check⟩
    exact eq_of_window_modEq (by decide) win check short low

/-- Centering a *single* public window at the rational slope `17/12`
retains only `n-5` low bits for all balanced inputs. This window needs
no slope strip. -/
theorem eq_iff_centered_balanced_window {x y N M : ℕ} (ord : x ≤ y) (bal : y ≤ 2*x)
    (short : N < 32*M) :
    x*y = N ↔ x*y ≡ N [MOD M] ∧ weightedProductWindow 8 17 12 N (17*x+12*y) := by
  have win : weightedProductWindow 8 17 12 (x*y) (17*x+12*y) := by
    constructor
    · have id := multiplier_sum_square x y 17 12
      omega
    · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le ord
      obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le (show d ≤ x by omega)
      rw [he]
      ring_nf
      omega
  constructor
  · rintro rfl
    exact ⟨Nat.ModEq.refl _,win⟩
  · rintro ⟨low,check⟩
    exact eq_of_window_modEq (by decide) win check short low

end PrimeFactors
