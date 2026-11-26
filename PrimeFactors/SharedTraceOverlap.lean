import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Public rational comparisons for simultaneous weighted Fermat intervals.
In scaled coordinates z=a*x the two endpoints are the same for every
allocation of a common multiplier. -/

namespace PrimeFactors.SharedTraceOverlap

/-- Both endpoints of an open interval scale by 1/a. -/
def Band (t h a x : ℝ) : Prop := (a*x)^2+t < h*(a*x)

theorem weighted_iff {a b n k h x : ℝ} (ap : 0<a) (ab : a*b=k) :
    a*x^2+b*n < h*x ↔ Band (k*n) h a x := by
  rw [←ab]
  unfold Band
  constructor
  · intro lt
    nlinarith only [mul_lt_mul_of_pos_left lt ap]
  · intro lt
    apply (mul_lt_mul_iff_of_pos_left ap).mp
    nlinarith only [lt]

private theorem roots {t h a x : ℝ} (D : 0≤h^2-4*t) :
    Band t h a x ↔ h-Real.sqrt (h^2-4*t)<2*a*x ∧ 2*a*x<h+Real.sqrt (h^2-4*t) := by
  have sq := Real.sq_sqrt D
  have eq : Band t h a x ↔ (2*a*x-h)^2 < (Real.sqrt (h^2-4*t))^2 := by
    unfold Band
    constructor <;> intro lt <;> nlinarith only [sq,lt]
  rw [eq,sq_lt_sq,abs_of_nonneg (Real.sqrt_nonneg _),abs_lt]
  constructor <;> rintro ⟨lo,hi⟩ <;> constructor <;> linarith only [lo,hi]

/-- Two ordered allocations have overlapping open real bands exactly when
this integer-coefficient inequality holds. Touching only at an endpoint
fails the strict comparison. -/
theorem overlap_iff {t h a c : ℝ} (tp : 0<t) (hp : 0<h) (ap : 0<a) (ac : a≤c) :
    (∃ x : ℝ, Band t h a x ∧ Band t h c x) ↔ t*(a+c)^2 < h^2*a*c := by
  have cp : 0<c := ap.trans_le ac
  by_cases D : 0≤h^2-4*t
  · let d := Real.sqrt (h^2-4*t)
    have dpos : 0≤d := Real.sqrt_nonneg _
    have dsq : d^2=h^2-4*t := Real.sq_sqrt D
    have dh : d<h := by nlinarith only [dsq,tp,hp,dpos]
    have basic : (∃ x : ℝ, Band t h a x ∧ Band t h c x) ↔ c*(h-d)<a*(h+d) := by
      constructor
      · rintro ⟨x,ax,cx⟩
        have lo := (roots D |>.mp ax).1
        have hi := (roots D |>.mp cx).2
        change h-d<2*a*x at lo
        change 2*c*x<h+d at hi
        nlinarith only [mul_lt_mul_of_pos_left lo cp,mul_lt_mul_of_pos_left hi ap]
      · intro lt
        have denA : 0<2*a := by linarith
        have denC : 0<2*c := by linarith
        have gap : (h-d)/(2*a)<(h+d)/(2*c) := by
          apply (div_lt_div_iff₀ denA denC).mpr
          linarith only [lt]
        obtain ⟨x,lo,hi⟩ := exists_between gap
        have lo' := (div_lt_iff₀ denA).mp lo
        have hi' := (lt_div_iff₀ denC).mp hi
        have xp : 0<x := lt_trans (div_pos (by linarith) denA) lo
        have scale := mul_le_mul_of_nonneg_right ac xp.le
        refine ⟨x,(roots D).mpr ?_,(roots D).mpr ?_⟩ <;>
          change h-d<_ ∧ _<h+d <;> constructor <;> linarith only [lo',hi',scale]
    rw [basic]
    have nonL : 0≤(c-a)*h := mul_nonneg (sub_nonneg.mpr ac) hp.le
    have nonR : 0≤(a+c)*d := mul_nonneg (by linarith) dpos
    have same : c*(h-d)<a*(h+d) ↔ (c-a)*h<(a+c)*d := by constructor <;> intro lt <;> linarith only [lt]
    rw [same,←sq_lt_sq₀ nonL nonR,mul_pow,mul_pow,dsq]
    constructor <;> intro lt <;> nlinarith only [lt]
  · constructor
    · rintro ⟨x,ax,_⟩
      unfold Band at ax
      nlinarith only [ax,sq_nonneg (2*a*x-h),D]
    · intro lt
      have spread := mul_nonneg tp.le (sq_nonneg (a-c))
      have neg := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge D) (mul_nonneg ap.le cp.le)
      nlinarith only [spread,neg,lt]

/-- All assignments of a common multiplier are disjoint on x≥L once
the squared discriminant is small enough. A value x in both bands would
place the two scaled integers a*x and c*x less than x apart. -/
theorem disjoint_above {t h L x : ℝ} {a c : ℕ} (xp : 0≤x) (lx : L≤x) (lp : 0≤L)
    (order : a<c) (small : h^2-4*t≤L^2) (ax : Band t h a x) :
    ¬Band t h c x := by
  intro cx
  have D : 0≤h^2-4*t := by
    unfold Band at ax
    nlinarith only [ax,sq_nonneg (2*(a:ℝ)*x-h)]
  have dL := Real.sqrt_le_iff.mpr ⟨lp,small⟩
  have lo := (roots D |>.mp ax).1
  have hi := (roots D |>.mp cx).2
  have gap : (a:ℝ)+1 ≤ c := by exact_mod_cast order
  have mul := mul_le_mul_of_nonneg_right gap xp
  nlinarith only [lo,hi,dL,lx,mul]


/-- Moving between two allocations scales every point by the same positive
factor, so the intervals have the same length in logarithmic coordinates. -/
theorem rescale {t h a c x : ℝ} (cp : c≠0) :
    Band t h a x ↔ Band t h c (a*x/c) := by
  unfold Band
  rw [mul_div_cancel₀ _ cp]

set_option exponentiation.threshold 4096

private theorem full_size_disc {n k : ℕ} {h : ℝ} (top : n≤2^2048) (small : k≤2^1974)
    (hpos : 0≤h) (height : h≤2*Real.sqrt ((k:ℝ)*n)+(2^32+1)) :
    h^2-4*((k:ℝ)*n) ≤ ((2:ℝ)^1023)^2 := by
  let d := Real.sqrt ((k:ℝ)*n)
  have dk : d^2=(k:ℝ)*n := Real.sq_sqrt (by positivity)
  have cap : d ≤ 2^2011 := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity,?_⟩
    calc
      _ ≤ (2:ℝ)^1974*2^2048 := by exact_mod_cast Nat.mul_le_mul small top
      _ = _ := by rw [←pow_add,←pow_mul]
  have diff : h^2≤(2*d+(2^32+1))^2 := pow_le_pow_left₀ hpos height 2
  have bound := mul_le_mul_of_nonneg_right cap (by positivity : (0:ℝ)≤4*(2^32+1))
  have room : (2:ℝ)^2011*(4*(2^32+1))+(2^32+1)^2≤(2^1023)^2 := by norm_num
  nlinarith only [diff,bound,room,dk]

/-- Count all rows by addition with no overlap correction. Applies on the
entire 1,024-bit factor range and to arbitrarily selected subsets of each row. -/
theorem full_size_exact_union {n k : ℕ} {h : ℝ} (top : n≤2^2048) (small : k≤2^1974)
    (hpos : 0≤h) (height : h≤2*Real.sqrt ((k:ℝ)*n)+(2^32+1))
    (weights : Finset ℕ) (row : ℕ → Finset ℕ)
    (mem : ∀ a∈weights, ∀ x∈row a, 2^1023≤x ∧ Band ((k:ℝ)*n) h a x) :
    (weights.biUnion row).card = ∑ a∈weights, (row a).card := by
  apply Finset.card_biUnion
  intro a ha c hc ne
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨lx,ax⟩ := mem a ha x hx
  obtain ⟨_,cx⟩ := mem c hc x hy
  have lower : (2:ℝ)^1023≤x := by exact_mod_cast lx
  have bound := full_size_disc top small hpos height
  rcases lt_or_gt_of_ne ne with ac|ca
  · exact disjoint_above (Nat.cast_nonneg _) lower (by positivity) ac bound ax cx
  · exact disjoint_above (Nat.cast_nonneg _) lower (by positivity) ca bound cx ax

end PrimeFactors.SharedTraceOverlap
