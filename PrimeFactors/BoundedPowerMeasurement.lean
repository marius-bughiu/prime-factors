import PrimeFactors.ConvexIntegerReadout
import Mathlib.Algebra.Order.Ring.Pow

/-! How much absolute accuracy is needed to identify a bounded natural
exponent from a power of a rational strictly between zero and one. -/
namespace PrimeFactors.BoundedPowerMeasurement

open Finset ConvexIntegerReadout

noncomputable def base (B : ℕ) : ℚ := 1-1/(8*B)
noncomputable def tolerance (B : ℕ) : ℚ := 1/(128*B)

theorem bounds {B : ℕ} (pos : 0<B) : 0≤base B ∧ base B≤1 := by
  have hp : (1:ℚ)≤B := by exact_mod_cast pos
  unfold base
  constructor
  · apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  · have : (0:ℚ)≤1/(8*B) := by positivity
    linarith

/-- Every power in the admissible interval remains at least one half. -/
theorem half_le {B s : ℕ} (pos : 0<B) (cap : s≤4*B) : (1:ℚ)/2≤(base B)^s := by
  have hp : (0:ℚ)<B := by exact_mod_cast pos
  have hs : (s:ℚ)≤4*B := by exact_mod_cast cap
  have bern := one_add_mul_sub_le_pow (a:=base B) (by linarith [(bounds pos).1]) s
  apply le_trans _ bern
  unfold base
  rw [show 1+(s:ℚ)*(1-1/(8*B)-1)=(8*B-s)/(8*B) by field_simp; ring]
  apply (le_div_iff₀ (by positivity)).mpr
  linarith

/-- Any two distinct exponents in the window have separated readings. -/
theorem separated {B s t : ℕ} (pos : 0<B) (cap : s≤4*B) (lt : s<t) :
    1/(16*(B:ℚ)) ≤ (base B)^s-(base B)^t := by
  have hp : (0:ℚ)<B := by exact_mod_cast pos
  have mono : base B^t≤base B^(s+1) := pow_le_pow_of_le_one (bounds pos).1 (bounds pos).2 lt
  have step : (base B)^s-(base B)^(s+1)=(base B)^s/(8*B) := by
    rw [pow_succ]; unfold base; ring
  have small : 1/(16*(B:ℚ))≤(base B)^s/(8*B) := by
    calc
      _ = ((1:ℚ)/2)/(8*B) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (half_le pos cap) (by positivity)
  rw [←step] at small
  linarith

/-- If the supplied value and the evaluation at each trial exponent both
have bounded error, the noisy comparison still changes at the true exponent. -/
theorem comparison {B s j : ℕ} (pos : 0<B) (small : s≤4*B)
    (y a : ℚ) (ey : |y-base B^s|≤tolerance B) (ea : |a-base B^j|≤tolerance B) :
    a≤y+2*tolerance B ↔ s≤j := by
  obtain ⟨yl,yu⟩ := abs_le.mp ey
  obtain ⟨al,au⟩ := abs_le.mp ea
  constructor
  · intro hit
    by_contra! early
    have gap := separated pos (early.le.trans small) early
    have h : 4*tolerance B<1/(16*(B:ℚ)) := by
      have bp : (0:ℚ)<B := by exact_mod_cast pos
      calc
        _ = ((1:ℚ)/32)/B := by unfold tolerance; ring
        _ < ((1:ℚ)/16)/B := div_lt_div_of_pos_right (by norm_num) bp
        _ = _ := by ring
    linarith
  · intro late
    have h := pow_le_pow_of_le_one (bounds pos).1 (bounds pos).2 late
    linarith

noncomputable def read (B fuel : ℕ) (y : ℚ) (approx : ℕ→ℚ) : ℕ×ℕ :=
  boundary (fun j => approx j≤y+2*tolerance B) fuel 0 (4*B)

theorem read_spec {B s fuel : ℕ} (pos : 0<B) (small : s<4*B) (room : 4*B<2^fuel)
    (y : ℚ) (approx : ℕ→ℚ) (ey : |y-base B^s|≤tolerance B)
    (ea : ∀ j, j<4*B → |approx j-base B^j|≤tolerance B) :
    (read B fuel y approx).1=s ∧ (read B fuel y approx).2≤fuel := by
  let P (j : ℕ) := approx j≤y+2*tolerance B
  have at_j (j : ℕ) (hj : j<4*B) : P j ↔ s≤j :=
    comparison pos small.le y (approx j) ey (ea j hj)
  have spec := boundary_spec P fuel 0 (4*B) room (by
    intro i j _ ij high pi
    apply (at_j j (by omega)).mpr
    exact ((at_j i (by omega)).mp pi).trans ij)
  let cut := (boundary P fuel 0 (4*B)).1
  obtain ⟨⟨_,upper,before,after⟩,cost⟩ := spec
  have eq : cut=s := by
    rcases lt_trichotomy cut s with less|same|more
    · exact False.elim (Nat.not_le_of_lt less ((at_j cut (by omega)).mp (after cut le_rfl (by omega))))
    · exact same
    · exact False.elim (before s (Nat.zero_le s) more ((at_j s small).mpr le_rfl))
  exact ⟨eq,cost⟩

/-- Every choice of a real evaluation point between zero and one has
limited separation between neighboring powers, uniformly in the point. -/
theorem separation_ceiling {x : ℚ} (lo : 0≤x) (hi : x≤1) (s : ℕ) :
    x^s-x^(s+1) ≤ 1/((s:ℚ)+1) := by
  have each (i : ℕ) (mem : i∈range (s+1)) : x^s≤x^i :=
    pow_le_pow_of_le_one lo hi (by simpa only [mem_range,Nat.lt_succ_iff] using mem)
  have total := sum_le_sum each
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at total
  have geo := geom_sum_mul x (s+1)
  have paid := mul_le_mul_of_nonneg_right total (sub_nonneg.mpr hi)
  apply (le_div_iff₀ (by positivity)).mpr
  rw [pow_succ] at geo ⊢
  nlinarith [pow_nonneg lo s]

end PrimeFactors.BoundedPowerMeasurement
