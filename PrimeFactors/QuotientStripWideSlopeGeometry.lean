import Mathlib.Tactic


/-!
# Stationary intervals of weighted sums

Near the minimum of `u*x + v*N/x`, successive full blocks have overlapping
ranges of candidate labels. Explicit constants control the widths and gaps.
-/

namespace PrimeFactors.QuotientStripWideSlopeGeometry

structure Band (s r u v t L : ℝ) : Prop where
  rp : 1 ≤ r
  vp : 7 ≤ v
  ratioLow : 5*v ≤ 4*u
  ratioHigh : 3*u ≤ 4*v
  cap : 2^11*v ≤ r
  rootLo : r^3 ≤ 2*s
  rootHi : s ≤ 2*r^3
  tp : 0<t
  lp : 0<L
  atCenter : u*t^2 = v*s^2
  span : 4*v*r*L=s

variable {s r u v t L : ℝ}

namespace Band

theorem basic (G : Band s r u v t L) :
    0<r ∧ 0<v ∧ v≤u ∧ 0<u ∧ 0<s := by
  obtain ⟨rp,vp,low,high,cap,lo,hi,tp,lp,ctr,span⟩ := G
  have R : 0<r := by linarith
  have V : 0<v := by linarith
  have U : v≤u := by linarith
  exact ⟨R,V,U,V.trans_le U,(by nlinarith only [lo,pow_pos R 3])⟩

theorem center (G : Band s r u v t L) : 3*s ≤ 4*t ∧ 16*t ≤ 15*s := by
  obtain ⟨_,_,_,up,sp⟩ := G.basic
  have low : 3*s^2 ≤ 4*t^2 := by
    apply le_of_mul_le_mul_left _ up
    nlinarith only [mul_le_mul_of_nonneg_right G.ratioHigh (sq_nonneg s),G.atCenter]
  have high : 5*t^2 ≤ 4*s^2 := by
    apply le_of_mul_le_mul_left _ up
    nlinarith only [mul_le_mul_of_nonneg_right G.ratioLow (sq_nonneg s),G.atCenter]
  constructor
  · by_contra! bad
    nlinarith only [low, sq_nonneg t, mul_self_lt_mul_self (by linarith [G.tp] : 0≤4*t) bad]
  · by_contra! bad
    nlinarith only [high, sq_nonneg s, mul_self_lt_mul_self (by linarith : 0≤15*s) bad]

theorem near_center (G : Band s r u v t L) : 6*s ≤ 7*t := by
  obtain ⟨_,_,_,up,sp⟩ := G.basic
  have base : 3*s^2 ≤ 4*t^2 := by
    apply le_of_mul_le_mul_left _ up
    nlinarith only [mul_le_mul_of_nonneg_right G.ratioHigh (sq_nonneg s),G.atCenter]
  by_contra! bad
  nlinarith only [base,sq_nonneg t,mul_self_lt_mul_self (by linarith [G.tp] : 0≤7*t) bad]

theorem span_bounds (G : Band s r u v t L) : 256*L≤s ∧ 256*r≤L := by
  obtain ⟨rp,vp,_,_,_⟩ := G.basic
  have r64 : 64≤r := by linarith [G.cap,G.vp]
  have v1 : 1≤v := by linarith [G.vp]
  have vr : 64≤v*r := by nlinarith only [mul_le_mul_of_nonneg_right v1 rp.le,r64]
  have left := mul_le_mul_of_nonneg_right vr G.lp.le
  have r2 : r^2 ≤ 8*v*L := by
    apply le_of_mul_le_mul_left _ rp
    nlinarith only [G.rootLo,G.span]
  have large := mul_le_mul_of_nonneg_right G.cap rp.le
  have right : 256*r≤L := by
    apply le_of_mul_le_mul_left _ vp
    norm_num1 at large
    nlinarith only [large,r2]
  exact ⟨by nlinarith only [left,G.span],right⟩

theorem band_interior (G : Band s r u v t L) :
    47*s/64 ≤ t-L ∧ t ≤ 15*s/16 ∧ 16*r ≤ s := by
  obtain ⟨_,_,_,_,sp⟩ := G.basic
  obtain ⟨l,h⟩ := G.center
  obtain ⟨a,b⟩ := G.span_bounds
  exact ⟨by linarith,by linarith,by linarith [G.lp]⟩

theorem slope_at (G : Band s r u v t L) {y : ℝ} (low : t-L≤y) (high : y≤t) :
    0<y ∧ 0≤v*s^2/y^2-u ∧ v*s^2/y^2-u<7/(8*r) := by
  obtain ⟨rp,vp,_,up,sp⟩ := G.basic
  obtain ⟨cs,_⟩ := G.center
  have le : 256*L≤s := G.span_bounds.1
  have yp : 0<y := by linarith [G.tp]
  have y34 : 63*t/64≤y := by linarith [G.near_center]
  have sq := pow_le_pow_left₀ yp.le high 2
  have sq' := pow_le_pow_left₀ (by linarith [G.tp] : 0≤63*t/64) y34 2
  have a : (t-y)*(t+y) ≤ L*(2*t) := by
    apply mul_le_mul _ _ (by linarith [G.tp]) G.lp.le <;> linarith
  have b := mul_le_mul_of_nonneg_left a (mul_nonneg (by linarith : 0≤8*r) up.le)
  have c := mul_le_mul_of_nonneg_right G.ratioHigh (mul_nonneg (mul_nonneg rp.le G.lp.le) G.tp.le)
  have d := congrArg (fun z : ℝ => z*t) G.span
  change 4*v*r*L*t = s*t at d
  have e := mul_le_mul_of_nonneg_right G.near_center G.tp.le
  have sep : 8*r*(v*s^2-u*y^2)<7*y^2 := by
    rw [← G.atCenter]
    have core : 8*r*(u*t^2-u*y^2) ≤ 16*s*t/3 := by nlinarith only [b,c,d]
    have margin : 16*s*t/3 < 7*y^2 := by nlinarith only [e,sq',sq_pos_of_pos G.tp]
    exact core.trans_lt margin
  refine ⟨yp,?_,?_⟩
  · rw [sub_nonneg,le_div_iff₀ (sq_pos_of_pos yp)]
    exact (mul_le_mul_of_nonneg_left sq up.le).trans_eq G.atCenter
  · rw [sub_lt_iff_lt_add,div_lt_iff₀ (sq_pos_of_pos yp)]
    apply lt_of_mul_lt_mul_left (a:=8*r) _ (by positivity)
    field_simp
    nlinarith only [sep]

theorem chord_slope (G : Band s r u v t L) {a b : ℝ}
    (low : t-L≤a) (ab : a≤b) (high : b≤t) :
    0≤v*s^2/(a*b)-u ∧ v*s^2/(a*b)-u<7/(8*r) := by
  obtain ⟨_,_,ap⟩ := G.slope_at low (ab.trans high)
  obtain ⟨yp,_,_⟩ := G.slope_at low (ab.trans high)
  have bp := yp.trans_le ab
  obtain ⟨_,vp,_,up,_⟩ := G.basic
  have above : a*b ≤ t^2 := by
    simpa [sq] using mul_le_mul (ab.trans high) high bp.le G.tp.le
  have below : a^2 ≤ a*b := by nlinarith only [mul_le_mul_of_nonneg_left ab yp.le]
  refine ⟨?_, (sub_le_sub_right (div_le_div_of_nonneg_left
    (mul_nonneg vp.le (sq_nonneg s)) (sq_pos_of_pos yp) below) _).trans_lt ap⟩
  rw [sub_nonneg,le_div_iff₀ (mul_pos yp bp)]
  exact (mul_le_mul_of_nonneg_left above up.le).trans_eq G.atCenter

noncomputable def F (s u v x : ℝ) := u*x+v*s^2/x
noncomputable def pad (s v a b : ℝ) := v*s^2*(b-a)^2/(4*a^2*b)

theorem adjacent (G : Band s r u v t L) {a b : ℝ}
    (low : t-L≤a) (full : b-a=2*r-1) (high : b≤t) :
    F s u v b-pad s v a b ≤ F s u v (b+1) := by
  obtain ⟨rp,vp,_,_,sp⟩ := G.basic
  have ab : a≤b := by linarith [G.rp]
  obtain ⟨ap,_,_⟩ := G.slope_at low (ab.trans high)
  obtain ⟨bp,_,slope⟩ := G.slope_at (low.trans ab) high
  have b1 : 0<b+1 := by linarith
  have id : F s u v b-F s u v (b+1)=v*s^2/(b*(b+1))-u := by
    unfold F
    field_simp
    ring
  have bot : b^2 ≤ b*(b+1) := by nlinarith only [bp.le]
  have step : F s u v b-F s u v (b+1) ≤ 7/(8*r) := by
    rw [id]
    exact (sub_le_sub_right (div_le_div_of_nonneg_left
      (mul_nonneg vp.le (sq_nonneg s)) (sq_pos_of_pos bp) bot) _).trans slope.le
  have bs : b≤s := by linarith [G.center.2]
  have a2 := pow_le_pow_left₀ ap.le (ab.trans bs) 2
  have d2 := pow_le_pow_left₀ rp.le (by linarith [G.rp] : r≤b-a) 2
  have bot' := mul_le_mul a2 bs bp.le (sq_nonneg s)
  have top := mul_le_mul_of_nonneg_right d2 (by positivity : 0≤8*r*v*s^2)
  have vlo := mul_le_mul_of_nonneg_right G.vp (by positivity : 0≤8*r^3*s^2)
  have rhi := mul_le_mul_of_nonneg_right G.rootHi (sq_nonneg s)
  have bound : 7/(8*r) ≤ pad s v a b := by
    unfold pad
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [bot',top,vlo,rhi]
  linarith only [step,bound]

theorem offset (G : Band s r u v t L) {x : ℝ} (xp : 0<x) :
    F s u v x-2*u*t=u*(t-x)^2/x := by
  unfold F
  rw [← G.atCenter]
  field_simp
  ring

theorem first_height (G : Band s r u v t L) {a : ℝ}
    (lo : t-L≤a) (hi : a≤t-L+2*r) : 2*u*t+64 ≤ F s u v a := by
  obtain ⟨rp,vp,vu,up,sp⟩ := G.basic
  obtain ⟨_,rl⟩ := G.span_bounds
  have dist : 15*L/16 ≤ t-a := by linarith
  have at' : a≤t := by linarith [G.lp]
  have ap := (G.slope_at lo at').1
  have as' : a≤s := by linarith [G.center.2]
  have d2 := pow_le_pow_left₀ (by linarith [G.lp] : 0≤15*L/16) dist 2
  have large := mul_le_mul_of_nonneg_right rl (mul_nonneg vp.le G.lp.le)
  have mid := mul_le_mul_of_nonneg_left d2 up.le
  have top := mul_le_mul_of_nonneg_right G.ratioLow (sq_nonneg L)
  have bound : 64 ≤ u*(t-a)^2/a := by
    apply (le_div_iff₀ ap).mpr
    nlinarith only [G.span,large,mid,top,as',mul_nonneg vp.le (sq_nonneg L)]
  linarith only [G.offset ap,bound]

theorem last_height (G : Band s r u v t L) {b : ℝ}
    (lo : t-4*r≤b) (hi : b≤t) : F s u v b < 2*u*t+1 := by
  obtain ⟨rp,vp,vu,up,sp⟩ := G.basic
  have bot : s/2 ≤ b := by linarith [G.band_interior.2.2,G.center.1]
  have bp : 0<b := by linarith
  have d2 := pow_le_pow_left₀ (by linarith : 0≤t-b) (by linarith : t-b≤4*r) 2
  have top := mul_le_mul_of_nonneg_left d2 up.le
  have slope := mul_le_mul_of_nonneg_right G.ratioHigh (sq_nonneg r)
  have cap := mul_le_mul_of_nonneg_right G.cap (sq_nonneg r)
  have bound : u*(t-b)^2/b < 1 := by
    apply (div_lt_iff₀ bp).mpr
    norm_num1 at cap
    nlinarith only [top,slope,cap,G.rootLo,bot,pow_pos rp 3]
  linarith only [bound,G.offset bp]

end Band
end PrimeFactors.QuotientStripWideSlopeGeometry
