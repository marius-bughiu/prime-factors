import PrimeFactors.Fermat
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp

namespace PrimeFactors.FareyWork

open Finset

/-- These coprime offsets (x,b) give distinct scheduled slopes (b+x)/b.
The extra endpoint 1/1 is not needed for the lower bound. -/
noncomputable def primitiveOffsets (K : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 K) ×ˢ (Icc 1 K)).filter (fun z => z.1 ≤ z.2 ∧ z.1.Coprime z.2)

/-- Each counted offset passes the coprimality test in the slope loop. -/
theorem primitive_slope {K x b : ℕ} (h : (x,b) ∈ primitiveOffsets K) :
    1 ≤ b ∧ b ≤ K ∧ b ≤ b+x ∧ b+x ≤ 2*b ∧ (b+x).Coprime b := by
  obtain ⟨square,xb,cop⟩ := mem_filter.mp h
  obtain ⟨bpos,bK⟩ := mem_Icc.mp (mem_product.mp square).2
  exact ⟨bpos,bK,by omega,by omega,Nat.coprime_self_add_left.mpr cop⟩

theorem slope_pair_injective : Function.Injective (fun z : ℕ × ℕ => (z.2+z.1,z.2)) := by
  rintro ⟨x,b⟩ ⟨y,c⟩ eq
  obtain ⟨sides,den⟩ := Prod.mk.inj eq
  exact Prod.ext (by omega) den

private noncomputable def multiples (K d : ℕ) : Finset (ℕ × ℕ) :=
  (((Icc 1 (K/d)) : Finset ℕ) ×ˢ (Icc 1 (K/d))).image (fun z => (z.1*d,z.2*d))

private theorem multiple_count (K d : ℕ) : (multiples K d).card ≤ (K/d)^2 := by
  exact card_image_le.trans_eq (by simp [card_product, sq])

private theorem square_cover (K : ℕ) :
    K^2 ≤ 2*(primitiveOffsets K).card + ∑ i ∈ range K, (K/(i+2))^2 := by
  let T := primitiveOffsets K
  let B := (Icc 1 K) ×ˢ (Icc 1 K)
  let D := (range K).biUnion (fun i => multiples K (i+2))
  have cover : B ⊆ (T ∪ T.image Prod.swap) ∪ D := by
    rintro ⟨x,y⟩ mem
    obtain ⟨xm,ym⟩ := mem_product.mp mem
    obtain ⟨xpos,xK⟩ := mem_Icc.mp xm
    obtain ⟨ypos,_⟩ := mem_Icc.mp ym
    by_cases cop : x.Coprime y
    · apply mem_union_left
      rcases le_total x y with xy | yx
      · exact mem_union_left _ (mem_filter.mpr ⟨mem,xy,cop⟩)
      · apply mem_union_right
        exact mem_image.mpr ⟨(y,x), mem_filter.mpr ⟨mem_product.mpr ⟨ym,xm⟩,yx,cop.symm⟩,rfl⟩
    · apply mem_union_right
      let d := x.gcd y
      have dp : 0 < d := Nat.gcd_pos_of_pos_left _ xpos
      have ne : d ≠ 1 := cop
      have le : d ≤ K := (Nat.gcd_le_left _ xpos).trans xK
      have dx := Nat.gcd_dvd_left x y
      have dy := Nat.gcd_dvd_right x y
      apply mem_biUnion.mpr
      refine ⟨d-2, mem_range.mpr (by omega), ?_⟩
      rw [show d-2+2 = d by omega]
      apply mem_image.mpr
      refine ⟨(x/d,y/d), mem_product.mpr ⟨mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd xpos dx) dp,
        Nat.div_le_div_right xK⟩,mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd ypos dy) dp,
        Nat.div_le_div_right (mem_Icc.mp ym).2⟩⟩, ?_⟩
      exact Prod.ext (Nat.div_mul_cancel dx) (Nat.div_mul_cancel dy)
  have ht : (T ∪ T.image Prod.swap).card ≤ T.card + T.card := (card_union_le _ _).trans
    (Nat.add_le_add_left card_image_le _)
  have hd : D.card ≤ ∑ i ∈ range K, (K/(i+2))^2 := card_biUnion_le.trans
    (sum_le_sum (fun i _ => multiple_count K (i+2)))
  simpa [B, T, sq, two_mul] using (card_le_card cover).trans
    ((card_union_le _ _).trans (Nat.add_le_add ht hd))

private theorem reciprocal_tail (k : ℕ) :
    ∑ i ∈ range k, 1/((i:ℝ)+3)^2 ≤ 1/2-1/((k:ℝ)+2) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ]
    push_cast
    have h : 1 / ((k:ℝ)+3)^2 ≤ 1/((k:ℝ)+2)-1/((k:ℝ)+1+2) := by
      rw [show (k:ℝ)+1+2 = k+3 by ring]
      calc
        _ ≤ 1/(((k:ℝ)+2)*(k+3)) := one_div_le_one_div_of_le (by positivity) (by nlinarith)
        _ = _ := by field_simp; ring
    linarith

private theorem reciprocal_bound (K : ℕ) : ∑ i ∈ range K, 1/((i:ℝ)+2)^2 ≤ 3/4 := by
  cases K with
  | zero => norm_num
  | succ k =>
    rw [sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, add_assoc]
    norm_num
    have h := reciprocal_tail k
    have pos : 0 ≤ 1/((k:ℝ)+2) := by positivity
    simp only [one_div] at h pos
    linarith

/-- An explicit elementary count, valid for every cutoff including small ones. -/
theorem primitive_count (K : ℕ) : K^2 ≤ 8*(primitiveOffsets K).card := by
  have cap : (∑ i ∈ range K, ((K/(i+2) : ℕ) : ℝ)^2) ≤ (K:ℝ)^2*(3/4) := by
    calc
      _ ≤ ∑ i ∈ range K, (K:ℝ)^2*(1/((i:ℝ)+2)^2) := by
        apply sum_le_sum
        intro i _
        have dd : (0:ℝ) < i+2 := by positivity
        have h : ((K/(i+2) : ℕ) : ℝ)*((i:ℝ)+2) ≤ K := by exact_mod_cast Nat.div_mul_le_self K (i+2)
        have t := pow_le_pow_left₀ (show 0≤((K/(i+2):ℕ):ℝ)*((i:ℝ)+2) by positivity) h 2
        rw [mul_pow] at t
        rw [← mul_div_assoc, mul_one]
        exact (le_div_iff₀ (sq_pos_of_pos dd)).mpr t
      _ = (K:ℝ)^2 * ∑ i ∈ range K, 1/((i:ℝ)+2)^2 := by rw [← mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_bound K) (sq_nonneg _)
  have h := square_cover K
  have bound : (K:ℝ)^2 ≤ 2*((primitiveOffsets K).card:ℝ) +
      ∑ i ∈ range K, ((K/(i+2) : ℕ) : ℝ)^2 := by exact_mod_cast h
  exact_mod_cast (show (K:ℝ)^2 ≤ 8*((primitiveOffsets K).card:ℝ) by linarith)

set_option maxHeartbeats 1600000 in
/-- A uniform count of consecutive labels, prior to taking an arithmetic progression.
The denominator of either available Farey side is at most h(ha+1). -/
theorem window_length {N K a b h den gain : ℕ} (large : 16 ≤ N.sqrt)
    (hk : 1 ≤ K) (hb : 1 ≤ b) (bk : b ≤ K) (ab : a ≤ 2*b) (hs : h ≤ 2*K)
    (dp : 0 < den) (db : den ≤ h*(h*a+1)) (side : b*N/den ≤ gain) :
    ceilSqrt (4*a*b*N) + N.sqrt/(64*K^3) ≤ (4*a*b*N+gain).sqrt+1 := by
  let s := N.sqrt
  let A := 4*a*b*N
  let y := A.sqrt
  let j := s/(64*K^3)
  have s16 : 16 ≤ s := large
  have n1 : N < (s+1)^2 := Nat.lt_succ_sqrt' N
  have n2 : s^2 ≤ N := Nat.sqrt_le' N
  have n9 : 8*N ≤ 9*s^2 := by
    have x := Nat.mul_le_mul_right s s16
    nlinarith
  have ak : a ≤ 2*K := ab.trans (by omega)
  have sqA : A ≤ 8*K^2*N := by
    have c := Nat.mul_le_mul_right (4*N) (Nat.mul_le_mul ak bk)
    dsimp [A]
    nlinarith
  have y3 : y ≤ 3*K*s := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    calc
      _ ≤ A := Nat.sqrt_le' A
      _ ≤ 8*K^2*N := sqA
      _ ≤ (3*K*s)^2 := by nlinarith [Nat.mul_le_mul_left (K^2) n9]
  have j64 : 64*K^3*j ≤ s := Nat.mul_div_le s _
  have kK : 1 ≤ K^3 := Nat.pow_pos hk
  have ks : s ≤ K*s := Nat.le_mul_of_pos_left _ hk
  have j4 : 10*j ≤ 4*K*s := by
    have t := Nat.mul_le_mul_right j (show 10 ≤ 64*K^3 by omega)
    nlinarith only [t, j64, ks]
  have c20 : 20*y+10*j ≤ 64*K*s := by nlinarith only [y3, j4]
  have inc : (2*y*j+j^2)*(10*K^2) ≤ N := by
    calc
      _ = (j*K^2)*(20*y+10*j) := by ring
      _ ≤ (j*K^2)*(64*K*s) := Nat.mul_le_mul_left _ c20
      _ = (64*K^3*j)*s := by ring
      _ ≤ s*s := Nat.mul_le_mul_right _ j64
      _ ≤ N := by simpa [sq] using n2
  have kb : 1 ≤ K*b := Nat.mul_pos hk hb
  have ha : h*a+1 ≤ 5*K*b := by nlinarith only [Nat.mul_le_mul hs ab,kb]
  have den10 : den ≤ 10*b*K^2 := db.trans (by nlinarith only [Nat.mul_le_mul hs ha])
  have delta : 2*y*j+j^2 ≤ gain := by
    apply le_trans _ side
    apply (Nat.le_div_iff_mul_le dp).mpr
    calc
      _ ≤ (2*y*j+j^2)*(10*b*K^2) := Nat.mul_le_mul_left _ den10
      _ = b*((2*y*j+j^2)*(10*K^2)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ inc
  have ysq : y^2 ≤ A := Nat.sqrt_le' A
  have up : y+j ≤ (A+gain).sqrt := Nat.le_sqrt'.mpr (by nlinarith only [ysq,delta])
  have low : ceilSqrt A ≤ y+1 := ceilSqrt_le_iff.mpr (Nat.lt_succ_sqrt' A).le
  change ceilSqrt A + j ≤ (A+gain).sqrt + 1
  omega

/-- Record count for a single row after applying its stride, matching the two
integer divisions in the implementation.  The offset is selected modulo step. -/
def rowGiants (lo hi offset step m : ℕ) : ℕ :=
  if lo+offset ≤ hi then ((hi-(lo+offset))/step+1+m-1)/m else 0

theorem row_capacity {lo hi offset step m : ℕ} (ds : offset < step)
    (bound : step ≤ 24) (hm : 1 ≤ m) :
    hi+1 ≤ lo + 24*(1+m*rowGiants lo hi offset step m) := by
  unfold rowGiants
  split_ifs with yes
  · let d := hi-(lo+offset)
    have part := Nat.lt_mul_div_succ d (by omega : 0 < step)
    have blocks := Nat.lt_mul_div_succ (d/step+1+m-1) hm
    have len : d/step+1 ≤ m*((d/step+1+m-1)/m) := by
      rw [Nat.mul_add] at blocks
      omega
    have gaps := Nat.mul_le_mul bound len
    change hi+1 ≤ lo+24*(1+m*((d/step+1+m-1)/m))
    have endp : hi = lo+offset+d := by dsimp [d]; omega
    omega
  · simp
    omega

/-- Sum-of-capacities estimate for any choice of offset and stride at most 24. -/
theorem row_work {N K lo hi offset step m : ℕ} (hk : 1 ≤ K)
    (length : lo + N.sqrt/(64*K^3) ≤ hi+1) (ds : offset < step)
    (bound : step ≤ 24) (hm : 1 ≤ m) :
    N.sqrt+1 ≤ 1600*K^3*(1+m*rowGiants lo hi offset step m) := by
  have j := Nat.lt_mul_div_succ N.sqrt (by positivity : 0 < 64*K^3)
  have cap := row_capacity ds bound hm (lo := lo) (hi := hi)
  let g := rowGiants lo hi offset step m
  have le : N.sqrt/(64*K^3)+1 ≤ 25*(1+m*g) := by dsimp [g]; omega
  have t := Nat.mul_le_mul_left (64*K^3) le
  change N.sqrt+1 ≤ 1600*K^3*(1+m*g)
  nlinarith

/-- Aggregate capacity across any finite collection of rows. -/
theorem total_capacity {ι : Type*} (T : Finset ι) (g : ι → ℕ) {s K m : ℕ}
    (each : ∀ i ∈ T, s+1 ≤ 1600*K^3*(1+m*g i)) :
    (s+1)*T.card ≤ 1600*K^3*(T.card+m*∑ i ∈ T, g i) := by
  calc
    _ = ∑ _i ∈ T, (s+1) := by simp [mul_comm]
    _ ≤ _ := sum_le_sum each
    _ = _ := by rw [← mul_sum, sum_add_distrib, ← mul_sum]; simp

/-- This bound concerns the full allocation. It makes no claim about early discovery. -/
theorem full_work {N K R G m : ℕ} (hk : 1 ≤ K) (hm : 1 ≤ m) (many : K^2 ≤ 8*R)
    (total : (N.sqrt+1)*R ≤ 1600*K^3*(R+m*G)) :
    N < 81920000*(R+G+m)^5 := by
  let W := R+G+m
  have kpos : 0 < K^2 := Nat.pow_pos hk
  have cap : (N.sqrt+1)*K^2 ≤ (12800*K*(R+m*G))*K^2 := by
    calc
      _ ≤ (N.sqrt+1)*(8*R) := Nat.mul_le_mul_left _ many
      _ = 8*((N.sqrt+1)*R) := by ring
      _ ≤ 8*(1600*K^3*(R+m*G)) := Nat.mul_le_mul_left _ total
      _ = _ := by ring
  have one : N.sqrt+1 ≤ 12800*K*(R+m*G) := Nat.le_of_mul_le_mul_right cap kpos
  have rr : R ≤ m*R := Nat.le_mul_of_pos_left _ hm
  have sqsum : 4*m*(R+G) ≤ W^2 := by
    dsimp [W]
    have hx := sq_nonneg (((R:ℤ)+(G:ℤ))-m)
    zify
    nlinarith only [hx]
  have pair : 4*(R+m*G) ≤ W^2 := by nlinarith only [sqsum,rr]
  have stride : N.sqrt+1 ≤ 3200*K*W^2 := by
    calc
      _ ≤ _ := one
      _ = (3200*K)*(4*(R+m*G)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ pair
  have kw : K^2 ≤ 8*W := many.trans (Nat.mul_le_mul_left _ (by dsimp [W]; omega))
  calc
    N < (N.sqrt+1)^2 := Nat.lt_succ_sqrt' N
    _ ≤ (3200*K*W^2)^2 := Nat.pow_le_pow_left stride _
    _ = 10240000*K^2*W^4 := by ring
    _ ≤ 10240000*(8*W)*W^4 := by gcongr
    _ = _ := by dsimp [W]; ring

/-- At 2048 bits every full allocation exceeds 2^404 counted records. -/
theorem work_2048 {N K R G m : ℕ} (large : 2^2047 ≤ N) (hk : 1 ≤ K)
    (hm : 1 ≤ m) (many : K^2 ≤ 8*R) (total : (N.sqrt+1)*R ≤ 1600*K^3*(R+m*G)) :
    2^404 < R+G+m := by
  by_contra! small
  have cap := full_work hk hm many total
  have sz := Nat.mul_le_mul_left 81920000 (Nat.pow_le_pow_left small 5)
  have coeff : 81920000*(2^404)^5 < (2:ℕ)^2047 := by
    rw [← pow_mul, show 2047 = 27 + (404*5) by decide, pow_add]
    exact Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)
  omega

/-- For either available side h is a sum of denominators, den is h(ha ± 1),
and gain is the larger available radicand increment. -/
structure Window where
  h : ℕ
  den : ℕ
  gain : ℕ
  step : ℕ
  offset : ℕ

/-- Bounds required of a public window. Smaller strides and a larger gain
are allowed. The bounds do not presume a factor or a collision. -/
def Window.admissible (w : Window) (N K a b : ℕ) : Prop :=
  w.h ≤ 2*K ∧ 0 < w.den ∧ w.den ≤ w.h*(w.h*a+1) ∧
  b*N/w.den ≤ w.gain ∧ w.offset < w.step ∧ w.step ≤ 24

def Window.blocks (w : Window) (N a b m : ℕ) : ℕ :=
  rowGiants (ceilSqrt (4*a*b*N)) (4*a*b*N+w.gain).sqrt w.offset w.step m

set_option exponentiation.threshold 4096 in
/-- The complete bound for all primitive slopes except 1/1 already exceeds 2^404.
No uniform lower bound on the number of records before an early exit is implied. -/
theorem complete_farey_2048 {N K m : ℕ} (large : 2^2047 ≤ N) (hk : 1 ≤ K)
    (hm : 1 ≤ m) (window : ℕ × ℕ → Window)
    (valid : ∀ z ∈ primitiveOffsets K, (window z).admissible N K (z.2+z.1) z.2) :
    2^404 < (primitiveOffsets K).card +
      (∑ z ∈ primitiveOffsets K, (window z).blocks N (z.2+z.1) z.2 m) + m := by
  have enough : (2:ℕ)^8 ≤ 2^2047 := Nat.pow_le_pow_right (by decide) (by decide)
  have sz : 16 ≤ N.sqrt := Nat.le_sqrt'.mpr (show (16:ℕ)^2 ≤ N from enough.trans large)
  apply work_2048 large hk hm (primitive_count K)
  apply total_capacity
  intro z hz
  obtain ⟨square,xy,_⟩ := mem_filter.mp hz
  obtain ⟨bpos,bK⟩ := mem_Icc.mp (mem_product.mp square).2
  obtain ⟨hs,dp,db,side,ds,stride⟩ := valid z hz
  have len := window_length sz hk bpos bK (show z.2+z.1 ≤ 2*z.2 by omega) hs dp db side
  exact row_work hk len ds stride hm

end PrimeFactors.FareyWork
