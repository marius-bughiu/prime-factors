import PrimeFactors.QuotientStripLevels
import Mathlib.Tactic

namespace PrimeFactors.QuotientStripTailCost
open QuotientStripScheduleCost
set_option exponentiation.threshold 4096
set_option maxRecDepth 8000
set_option maxHeartbeats 800000

/-- Integer bounds on the two public roots used in the tail. -/
theorem root_bounds {n : ℕ} (lo : 2^2047 ≤ n) (hi : n < 2^2048) :
    11*2^1020 ≤ n.sqrt ∧ n.sqrt < 2^1024 ∧
    2^341 ≤ roundedSixth n ∧ roundedSixth n ≤ 2^342 := by
  classical
  refine ⟨Nat.le_sqrt'.mpr ((by decide +kernel : (11*2^1020)^2 ≤ 2^2047).trans lo),
    Nat.sqrt_lt'.mpr (hi.trans_le (by decide +kernel)), ?_, ?_⟩
  · have hr : 64*n ≤ (2*roundedSixth n+1)^6 := by
      unfold roundedSixth
      exact (Nat.find_spec (p := fun r : ℕ => 0<r ∧ 64*n ≤ (2*r+1)^6) _).2
    by_contra! small
    have le : 2*roundedSixth n+1 ≤ 2*2^341-1 := by omega
    have bound := Nat.pow_le_pow_left le 6
    have imposs : (2*2^341-1)^6 < 64*2^2047 := by decide +kernel
    exact (not_lt_of_ge (Nat.mul_le_mul_left 64 lo)) (hr.trans_lt (bound.trans_lt imposs))
  · unfold roundedSixth
    apply Nat.find_min'
    exact ⟨by decide, (Nat.mul_le_mul_left 64 hi.le).trans (by decide +kernel)⟩

noncomputable def f (N x : ℚ) := x+N/x
noncomputable def pad (N a b : ℚ) := N*(b-a)^2/(4*a^2*b)

/-- A single denominator controls both the lost column and the next continued
fraction denominator. All constants are absolute on a 2048-bit input. -/
theorem tail_slope {N T a : ℚ} (tlo : 11*2^1020 ≤ T) (nhi : N < (T+1)^2)
    (tail : T-2^679 ≤ a) :
    0 < a ∧ (2^343 : ℚ)*N < (2^343+1)*a^2 := by
  let K : ℚ := 2^679+1
  let D : ℚ := 2^343
  have al : (5*2^1021 : ℚ) ≤ a := by linarith only [tlo,tail]
  have ap : 0<a := lt_of_lt_of_le (by norm_num) al
  have kp : 0<K := by norm_num [K]
  have dp : 0<D := by norm_num [D]
  have tk : T+1 ≤ a+K := by dsimp[K]; linarith only [tail]
  have nup : N < (a+K)^2 := nhi.trans_le (by
    apply pow_le_pow_left₀ _ tk
    linarith only [tlo])
  have ksmall : 4*K ≤ a := (by norm_num [K] : 4*K ≤ 5*2^1021).trans al
  have small : 9*D*K < 4*a := (by norm_num [D,K] : 9*D*K < 4*(5*2^1021 : ℚ)).trans_le
    (mul_le_mul_of_nonneg_left al (by norm_num))
  have err := mul_lt_mul_of_pos_left nup dp
  have ks := mul_le_mul_of_nonneg_left ksmall (mul_nonneg dp.le kp.le)
  have margin := mul_lt_mul_of_pos_right small ap
  exact ⟨ap,by change D*N < (D+1)*a^2; nlinarith only [err,ks,margin]⟩

theorem direction_and_gap {N T a b : ℚ} (tlo : 11*2^1020 ≤ T)
    (nhi : N < (T+1)^2) (tail : T-2^679 ≤ a) (ab : a ≤ b) :
    N/(a*b)-1 < 1/2^343 ∧ f N b-f N (b+1) < 1/2^343 := by
  obtain ⟨ap,h⟩ := tail_slope tlo nhi tail
  have bp := lt_of_lt_of_le ap ab
  have b1 : 0 < b+1 := by linarith
  have d : (0:ℚ)<2^343 := by norm_num
  have aa : a^2 ≤ a*b := by nlinarith only [mul_le_mul_of_nonneg_left ab ap.le]
  have ab' : a*b ≤ b*(b+1) := by
    apply mul_le_mul_of_nonneg_right _ bp.le |>.trans_eq (mul_comm (b+1) b)
    linarith
  have slope {v : ℚ} (vp : 0<v) (av : a^2≤v) : N/v-1 < 1/2^343 := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ vp]
    have bigger := h.trans_le (mul_le_mul_of_nonneg_left av (by positivity))
    norm_num1 at bigger ⊢
    linarith only [bigger]
  refine ⟨slope (mul_pos ap bp) aa, ?_⟩
  have id : f N b-f N (b+1)=N/(b*(b+1))-1 := by
    unfold f
    field_simp
    ring
  rw [id]
  exact slope (mul_pos bp b1) (aa.trans ab')

theorem pad_bound {N T r a b : ℚ} (tlo : 11*2^1020 ≤ T) (thi : T ≤ 2^1024)
    (tsq : T^2 ≤ N) (rl : 2^341 ≤ r) (tail : T-2^679 ≤ a)
    (bt : b ≤ T) (full : b-a=2*r-1) :
    1/2^343 ≤ pad N a b := by
  have ap : 0<a := by linarith only [tlo,tail]
  have tp : 0<T := by linarith only [tlo]
  have ab : a≤b := by linarith only [full,rl]
  have bp := ap.trans_le ab
  have asq : a^2 ≤ T^2 := pow_le_pow_left₀ ap.le (ab.trans bt) 2
  have aN := asq.trans tsq
  have dlow : (7*2^339:ℚ) ≤ b-a := by linarith only [full,rl]
  have dsq := pow_le_pow_left₀ (by norm_num : (0:ℚ)≤7*2^339) dlow 2
  have ds : 4*b ≤ 2^343*(b-a)^2 := by
    have bd := bt.trans thi
    linarith only [bd,dsq]
  have npos : 0 ≤ N := (sq_nonneg T).trans tsq
  unfold pad
  rw [le_div_iff₀ (by positivity)]
  have l := mul_le_mul_of_nonneg_right aN (by positivity : 0≤4*b)
  have m := mul_le_mul_of_nonneg_left ds npos
  norm_num1 at m ⊢
  nlinarith only [l,m]

/-- The leftmost complete block enters the tail by at most one whole width. -/
theorem first_value {N T a w : ℚ} (tlo : 11*2^1020 ≤ T) (thi : T≤2^1024)
    (tsq : T^2≤N) (wl : w≤2^343) (tail : T-2^679 ≤ a)
    (start : a ≤ T-2^679+w) :
    2*T+2^333 < f N a := by
  have ap : 0<a := by linarith only [tail,tlo]
  have al : a ≤ 2^1024 := by linarith only [thi,start,wl]
  have distance : (7*2^676:ℚ) ≤ T-a := by linarith only [wl,start]
  have sq := pow_le_pow_left₀ (by norm_num : (0:ℚ)≤7*2^676) distance 2
  unfold f
  rw [← sub_lt_iff_lt_add',lt_div_iff₀ ap]
  nlinarith only [tsq,sq,al]

/-- The rightmost full block stops fewer than 2w columns below the integer square root. -/
theorem last_value {N T b w : ℚ} (tlo : 11*2^1020 ≤ T) (nhi : N < (T+1)^2)
    (wl : w≤2^343) (bt : b≤T) (stop : T-2*w ≤ b) :
    f N b < 2*T+4 := by
  have bp : 0<b := by linarith only [tlo,wl,stop]
  have dlow : 0≤T-b := by linarith
  have dist : T-b≤2^344 := by linarith only [wl,stop]
  have sq := pow_le_pow_left₀ dlow dist 2
  unfold f
  rw [← lt_sub_iff_add_lt', div_lt_iff₀ bp]
  nlinarith only [nhi,tlo,wl,stop,sq]

/-- The five-level certificate itself forces the unit slope on this tail.
Reduction of the weights then forces the ordinary convergent to be 1/1. -/
theorem unique_direction {u v : ℕ} {α r : ℚ}
    (rlo : 3 ≤ r) (rhi : r ≤ 2^342)
    (vp : 0<v) (cap : (v:ℚ)≤r)
    (low : 1≤α) (high : α-1<1/2^343)
    (approximation : |(u:ℚ)-v*α|≤1/r) (prim : u.Coprime v) : u=1 ∧ v=1 := by
  have vr : 0 < (v:ℚ) := by exact_mod_cast vp
  have errs := abs_le.mp approximation
  have small : 1/r ≤ (1/3:ℚ) := by
    apply (div_le_div_iff₀ (by linarith) (by norm_num)).mpr
    linarith
  have left := mul_le_mul_of_nonneg_left low vr.le
  have right := mul_lt_mul_of_pos_left high vr
  have half : (v:ℚ)*(1/2^343) ≤ 1/2 := by
    calc
      _ ≤ 2^342*(1/2^343:ℚ) := mul_le_mul_of_nonneg_right (cap.trans rhi) (by positivity)
      _ = _ := by norm_num
  have a : (u:ℚ) < v+1 := by nlinarith only [small,errs.2,right,half]
  have b : (v:ℚ) < u+1 := by nlinarith only [small,errs.1,left]
  have eq : u=v := by
    have x : u<v+1 := by exact_mod_cast a
    have y : v<u+1 := by exact_mod_cast b
    omega
  subst u
  have one : v=1 := by simpa [Nat.Coprime] using prim
  exact ⟨one,one⟩

end PrimeFactors.QuotientStripTailCost
