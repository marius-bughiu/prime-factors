import PrimeFactors.NormArc
import PrimeFactors.RootIntervalSlope
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Rational enclosing lines for a block on b z²=M+a x² with M positive.
Positive and negative signed norms use the same increasing branch after a
coordinate swap. -/
namespace PrimeFactors.HyperbolicNormArc

/-- On the positive branch the height increases. -/
private theorem monotone {a b M x j u y : ℝ} (ap : 0 ≤ a) (bp : 0 < b)
    (xp : 0 ≤ x) (jp : 0 ≤ j) (up : 0 ≤ u) (yp : 0 ≤ y)
    (left : b*u^2=M+a*x^2) (point : b*y^2=M+a*(x+j)^2) : u ≤ y := by
  apply (sq_le_sq₀ up yp).mp
  apply le_of_mul_le_mul_left _ bp
  rw [point,left]
  exact add_le_add_left (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ xp (add_nonneg xp jp)).mpr (le_add_of_nonneg_right jp)) ap) _

/-- The graph stays above its tangent. The squared comparison has residual
a·b·M·j². -/
private theorem above_tangent {a b M x j u y : ℝ} (ap : 0 ≤ a) (bp : 0 < b)
    (mp : 0 ≤ M) (xp : 0 ≤ x) (jp : 0 ≤ j) (up : 0 ≤ u) (yp : 0 ≤ y)
    (left : b*u^2=M+a*x^2) (point : b*y^2=M+a*(x+j)^2) :
    a*x*j ≤ b*u*(y-u) := by
  have sq : (b*u*y)^2-(b*u^2+a*x*j)^2 = a*M*j^2 := by
    linear_combination b*u^2*point + (a*j^2-b*u^2)*left
  have cmp : b*u^2+a*x*j ≤ b*u*y := (sq_le_sq₀ (by positivity) (by positivity)).mp
    (by nlinarith only [sq, mul_nonneg (mul_nonneg ap mp) (sq_nonneg j)])
  linarith only [cmp]

/-- On a block the graph lies below the line joining its two endpoints. -/
private theorem below_secant {a b M x j w u y v : ℝ} (ap : 0 ≤ a) (bp : 0 < b)
    (mp : 0 ≤ M) (xp : 0 ≤ x) (jp : 0 ≤ j) (jw : j ≤ w)
    (up : 0 ≤ u) (yp : 0 ≤ y) (vp : 0 ≤ v)
    (left : b*u^2=M+a*x^2) (point : b*y^2=M+a*(x+j)^2)
    (right : b*v^2=M+a*(x+w)^2) : w*(y-u) ≤ j*(v-u) := by
  have wp := jp.trans jw
  have vu := monotone ap bp xp wp up vp left right
  have slope := above_tangent ap bp mp xp wp up vp left right
  have room : 0 ≤ a*w^2-b*(v-u)^2 := by linarith only [left,right,slope]
  have square : b*(w*u+j*(v-u))^2 - b*(w*y)^2 =
      j*(w-j)*(a*w^2-b*(v-u)^2) := by
    linear_combination w*j*right + w*(w-j)*left - w^2*point
  have compare : (w*y)^2 ≤ (w*u+j*(v-u))^2 := by
    apply le_of_mul_le_mul_left _ bp
    linarith only [square,mul_nonneg (mul_nonneg jp (sub_nonneg.mpr jw)) room]
  have := (sq_le_sq₀ (mul_nonneg wp yp)
    (add_nonneg (mul_nonneg wp up) (mul_nonneg jp (sub_nonneg.mpr vu)))).mp compare
  linarith only [this]

/-- Rational slopes used by the search. The lower and upper rounded left
heights are LL and UL, and LR is the rounded-down right height. -/
theorem slope_bounds {a b M x j w u y v LL UL LR : ℝ} (ap : 0 ≤ a) (bp : 0 < b)
    (mp : 0 ≤ M) (xp : 0 ≤ x) (jp : 0 ≤ j) (jw : j ≤ w)
    (up : 0 ≤ u) (yp : 0 ≤ y) (vp : 0 ≤ v)
    (left : b*u^2=M+a*x^2) (point : b*y^2=M+a*(x+j)^2)
    (right : b*v^2=M+a*(x+w)^2) (ll : LL ≤ u) (ul : u ≤ UL) (lr : LR ≤ v)
    (posL : 0 < UL) (posR : 0 < LL+LR) :
    a*x/(b*UL)*j ≤ y-u ∧ y-u ≤ a*(2*x+w)/(b*(LL+LR))*j := by
  have yu := monotone ap bp xp jp up yp left point
  have tan := above_tangent ap bp mp xp jp up yp left point
  have sec := below_secant ap bp mp xp jp jw up yp vp left point right
  have wp := jp.trans jw
  have endpoint : b*(u+v)*(v-u) = a*w*(2*x+w) := by linear_combination right-left
  have lower := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ul bp.le) (sub_nonneg.mpr yu)
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos bp posL)]
    linarith only [tan,lower]
  · rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos bp posR)]
    rcases wp.eq_or_lt with zero|wpos
    · have jzero : j=0 := by linarith
      rw [jzero,add_zero] at point
      have eq : u=y := (sq_eq_sq₀ up yp).mp (mul_left_cancel₀ bp.ne' (left.trans point.symm))
      simp [jzero,eq]
    · have exactUp : b*(u+v)*(y-u) ≤ a*(2*x+w)*j := by
        apply le_of_mul_le_mul_left _ wpos
        calc
          _ = b*(u+v)*(w*(y-u)) := by ring
          _ ≤ b*(u+v)*(j*(v-u)) :=
            mul_le_mul_of_nonneg_left sec (mul_nonneg bp.le (add_nonneg up vp))
          _ = (b*(u+v)*(v-u))*j := by ring
          _ = _ := by rw [endpoint]; ring
      nlinarith only [exactUp,mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add ll lr) bp.le) (sub_nonneg.mpr yu)]

/-- The actual integer intercept den·y−num·j lies between the search's
floor and ceiling arguments, for either sign of the approximation error. -/
theorem intercept_bounds {u y den num j w LL UL slo shi : ℝ}
    (dp : 0 ≤ den) (jp : 0 ≤ j) (jw : j ≤ w)
    (ll : LL ≤ u) (ul : u ≤ UL)
    (slo_le : slo*j ≤ y-u) (le_shi : y-u ≤ shi*j) :
    den*LL + min 0 ((den*slo-num)*w) ≤ den*y-num*j ∧
    den*y-num*j ≤ den*UL + max 0 ((den*shi-num)*w) := by
  have h := NormArc.intercept_bounds (u:=-u) (y:=-y) (den:=den) (num:=num)
    (j:=j) (w:=w) (lowerLeft:=-UL) (upperLeft:=-LL) (lowSlope:=slo) (highSlope:=shi)
    dp jp jw (by linarith only [ul]) (by linarith only [ll])
    (by linarith only [slo_le]) (by linarith only [le_shi])
  constructor
  · rcases le_total 0 ((den*slo-num)*w) with pos|neg
    · rw [min_eq_left pos]
      rw [max_eq_left (show (num-den*slo)*w ≤ 0 by linarith only [pos])] at h
      linarith only [h.2]
    · rw [min_eq_right neg]
      rw [max_eq_right (show 0 ≤ (num-den*slo)*w by linarith only [neg])] at h
      linarith only [h.2]
  · rcases le_total 0 ((den*shi-num)*w) with pos|neg
    · rw [max_eq_right pos]
      rw [min_eq_right (show (num-den*shi)*w ≤ 0 by linarith only [pos])] at h
      linarith only [h.1]
    · rw [max_eq_left neg]
      rw [min_eq_left (show 0 ≤ (num-den*shi)*w by linarith only [neg])] at h
      linarith only [h.1]

/-- The difference between the two rational slope bounds. LL and LR can
each underestimate their endpoint by eps; UL can overestimate by eps. -/
theorem rounded_gap {a b x w u v LL UL LR eps : ℝ}
    (ap : 0 ≤ a) (bp : 0 < b) (xp : 0 ≤ x) (wp : 0 ≤ w) (up : 0 < u)
    (ep : 0 ≤ eps) (tiny : 2*eps ≤ u) (coord : x ≤ b*u) (rising : u ≤ v)
    (ll : u-eps ≤ LL) (lo : u ≤ UL) (hi : UL ≤ u+eps) (lr : v-eps ≤ LR) :
    let slo := a*x/(b*UL)
    let shi := a*(2*x+w)/(b*(LL+LR))
    b*u*(shi-slo) ≤ 2*a*w+4*b*a*eps := by
  have sum : u ≤ LL+LR := by linarith only [ll,lr,rising,tiny]
  have sp : 0 < LL+LR := up.trans_le sum
  have ulp := up.trans_le lo
  have identity :
      b*(LL+LR)*UL*(a*(2*x+w)/(b*(LL+LR)) - a*x/(b*UL)) =
        a*((2*x+w)*UL-x*(LL+LR)) := by
    field_simp
    ring
  have bound : (2*x+w)*UL - x*(LL+LR) ≤ 2*w*u+4*b*u*eps := by
    have c := mul_le_mul_of_nonneg_right coord ep
    have small := mul_le_mul_of_nonneg_left (show eps ≤ u by linarith only [ep,tiny]) wp
    have top := mul_le_mul_of_nonneg_left hi (by linarith only [xp,wp] : 0≤2*x+w)
    have bot := mul_le_mul_of_nonneg_left (show 2*u-2*eps ≤ LL+LR by linarith only [ll,lr,rising]) xp
    linarith only [c,small,top,bot]
  dsimp only
  let gap := a*(2*x+w)/(b*(LL+LR)) - a*x/(b*UL)
  change b*u*gap ≤ _
  by_cases non : 0 ≤ gap
  · have den := mul_le_mul sum lo up.le sp.le
    have t := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left den bp.le) non
    have bottom : b*(LL+LR)*UL*gap = a*((2*x+w)*UL-x*(LL+LR)) := identity
    apply le_of_mul_le_mul_left _ up
    linarith only [t,bottom,mul_le_mul_of_nonneg_left bound ap]
  · exact (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg bp.le up.le)
      (le_of_not_ge non)).trans (by positivity)

/-- Under the actual block-size inequalities, endpoint rounding and curvature
enlarge the approximating strip by at most 5/4 in intercept coordinates. -/
theorem scaled_gap {a b u eps w W den gap : ℝ} (ap : 0 ≤ a) (bp : 0 < b) (up : 1 ≤ u)
    (wp : 0 ≤ w) (wW : w ≤ W) (dp : 0 ≤ den) (dW : den ≤ W) (ep : 0 ≤ eps)
    (radius : 8*a*W^3 ≤ b*u) (precision : 4*a*eps*W^2 ≤ 1)
    (slope : b*u*gap ≤ 2*a*w+4*b*a*eps) : den*gap*w ≤ 5/4 := by
  have ww := mul_le_mul dW wW wp (wp.trans wW)
  have cube := mul_le_mul ww wW wp (mul_self_nonneg W)
  have geom : 8*a*(den*w*w) ≤ b*u := by
    apply le_trans _ radius
    calc
      _ ≤ 8*a*(W*W*W) := mul_le_mul_of_nonneg_left cube (by positivity)
      _ = _ := by ring
  have quant : 4*a*eps*(den*w) ≤ 1 := by
    apply le_trans _ precision
    simpa only [pow_two] using mul_le_mul_of_nonneg_left ww (by positivity : 0≤4*a*eps)
  have ub : b ≤ b*u := by simpa using mul_le_mul_of_nonneg_left up bp.le
  apply le_of_mul_le_mul_left _ (mul_pos bp (by linarith only [up] : 0<u))
  linarith only [mul_le_mul_of_nonneg_right slope (mul_nonneg dp wp),
    geom,mul_le_mul_of_nonneg_left quant bp.le,ub]

/-- A length bound for the actual rational intercept interval. Integer
endpoints can be rounded inward after applying the inclusion theorem. -/
theorem strip_width {den num w LL UL slo shi : ℝ} (point : den*(UL-LL) ≤ 1)
    (errorLo : -1 ≤ (den*slo-num)*w) (errorHi : (den*slo-num)*w ≤ 1)
    (curvature : den*(shi-slo)*w ≤ 5/4) :
    (den*UL+max 0 ((den*shi-num)*w)) - (den*LL+min 0 ((den*slo-num)*w)) ≤ 17/4 := by
  have low : -1 ≤ min 0 ((den*slo-num)*w) := le_min (by norm_num) errorLo
  have high : max 0 ((den*shi-num)*w) ≤ 9/4 := max_le (by norm_num)
    (by linarith only [errorHi,curvature])
  linarith only [low,high,point]

/-- At most five integer lines intersect a strip of the certified width. -/
theorem integer_lines {lo hi : ℝ} (width : hi-lo ≤ 17/4) :
    (Finset.Icc (⌈lo⌉ : ℤ) (⌊hi⌋ : ℤ)).card ≤ 5 := by
  rw [Int.card_Icc]
  have diff : (⌊hi⌋ : ℤ)-⌈lo⌉ < 5 := by
    have h : ((⌊hi⌋ : ℤ) : ℝ)-((⌈lo⌉ : ℤ) : ℝ) < 5 := by
      linarith only [width,Int.floor_le hi,Int.le_ceil lo]
    exact_mod_cast h
  omega

/-- The integer square root computed after floor division encloses a curve
height between two successive multiples of 1/S. -/
theorem rounded_height {a b M x S : ℕ} {u : ℝ} (bp : 0 < b) (sp : 0 < S) (up : 0 ≤ u)
    (height : (b:ℝ)*u^2=M+(a:ℝ)*(x:ℝ)^2) :
    let L := (((M+a*x^2)*S^2)/b).sqrt
    (L:ℝ)/S ≤ u ∧ u < ((L:ℝ)+1)/S := by
  let L := (((M+a*x^2)*S^2)/b).sqrt
  change (L:ℝ)/S ≤ u ∧ u < ((L:ℝ)+1)/S
  have hb : (0:ℝ)<b := by exact_mod_cast bp
  have hs : (0:ℝ)<S := by exact_mod_cast sp
  obtain ⟨hlo,hhi⟩ := rootIntervalSlope_width (N:=(M+a*x^2)*S^2) bp
  have hlo' : (L:ℝ)^2*(b:ℝ) ≤ ((M:ℝ)+(a:ℝ)*(x:ℝ)^2)*(S:ℝ)^2 := by exact_mod_cast hlo
  have hhi' : ((M:ℝ)+(a:ℝ)*(x:ℝ)^2)*(S:ℝ)^2 < ((L:ℝ)+1)^2*(b:ℝ) := by exact_mod_cast hhi
  rw [← height] at hlo' hhi'
  rw [div_le_iff₀ hs, lt_div_iff₀ hs]
  constructor
  · apply (sq_le_sq₀ (by positivity) (mul_nonneg up hs.le)).mp
    apply le_of_mul_le_mul_left _ hb
    linarith only [hlo']
  · apply (sq_lt_sq₀ (mul_nonneg up hs.le) (by positivity)).mp
    apply lt_of_mul_lt_mul_left _ hb.le
    linarith only [hhi']

/-- The unsigned coordinate estimate and radius inequality used in the
strip bound follow by squaring against the curve equation. -/
theorem coordinate_radius {a b M x u R : ℝ} (ap : 1 ≤ a) (bp : 1 ≤ b)
    (mp : 0 ≤ M) (up : 0 ≤ u) (height : b*u^2=M+a*x^2) (radius : R^2 ≤ b*M) :
    x ≤ b*u ∧ R ≤ b*u := by
  have hb : 0 ≤ b := by linarith only [bp]
  have ha : 0 ≤ a := by linarith only [ap]
  have z0 := mul_nonneg hb up
  have hbx := mul_le_mul_of_nonneg_right ap (sq_nonneg x)
  have b2 := mul_le_mul_of_nonneg_right bp (mul_nonneg hb (sq_nonneg u))
  have pos := mul_nonneg ha (sq_nonneg x)
  constructor <;> apply le_of_sq_le_sq _ z0
  · linarith only [height,hbx,b2,mp]
  · linarith only [radius,mul_le_mul_of_nonneg_left (show M ≤ b*u^2 by
      linarith only [height,pos]) hb]

/-- A block of integer width W admits a denominator at most W and both
signed errors required by the intercept count. This uses the same
Dirichlet approximation as the rational slope construction. -/
theorem strip_slope (W : ℕ) {s w : ℝ} (pos : 0<W) (wp : 0≤w) (wW : w≤W) :
    ∃ (den : ℕ) (num : ℤ), 1≤den ∧ den≤W ∧
      -1 ≤ ((den:ℝ)*s-(num:ℝ))*w ∧ ((den:ℝ)*s-(num:ℝ))*w ≤ 1 := by
  obtain ⟨den,dp,dW,approx⟩ := Real.exists_nat_abs_mul_sub_round_le s pos
  let num := round ((den:ℝ)*s)
  change |(den:ℝ)*s-(num:ℝ)| ≤ 1/((W:ℝ)+1) at approx
  have weight : 0 < (W:ℝ)+1 := by positivity
  have h := (le_div_iff₀ weight).mp approx
  have lew := mul_le_mul_of_nonneg_left (show w ≤ (W:ℝ)+1 by linarith only [wW])
    (abs_nonneg ((den:ℝ)*s-(num:ℝ)))
  have full : |((den:ℝ)*s-(num:ℝ))*w| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg wp]
    exact lew.trans h
  exact ⟨den,num,dp,dW,(abs_le.mp full).1,(abs_le.mp full).2⟩

/-- The implementation's reciprocal scale controls all three height
rounding costs, including on the last, possibly shorter block. -/
theorem precision_parameters {a b W den : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hW : 1 ≤ W)
    (hden : den ≤ W) :
    let eps := 1/(4*(a+b+1)*W^2)
    2*eps ≤ 1 ∧ den*eps ≤ 1 ∧ 4*a*eps*W^2 ≤ 1 := by
  let S := 4*(a+b+1)*W^2
  have w2 : W ≤ W^2 := by nlinarith only [mul_nonneg (show 0≤W by linarith) (sub_nonneg.mpr hW)]
  have a0 : 0≤a := by linarith only [ha]
  have b0 : 0≤b := by linarith only [hb]
  have w0 : 0≤W^2 := sq_nonneg W
  have aw := mul_nonneg a0 w0
  have bw := mul_nonneg b0 w0
  have sp : 0<S := by dsimp [S]; linarith only [aw,bw,hW,w2]
  have s2 : 2≤S := by dsimp [S]; linarith only [aw,bw,hW,w2]
  have sd : den≤S := by dsimp [S]; linarith only [aw,bw,hW,w2,hden]
  have sa : 4*a*W^2≤S := by dsimp [S]; linarith only [bw,w0]
  change 2*(1/S) ≤ 1 ∧ den*(1/S) ≤ 1 ∧ 4*a*(1/S)*W^2 ≤ 1
  have last : 4*a*(1/S)*W^2 = 4*a*W^2/S := by ring
  rw [last]
  simpa only [mul_one_div,div_le_iff₀ sp,one_mul] using And.intro s2 (And.intro sd sa)

/-- All the rounded strips used on a nonsingleton block with the cubic
radius inequality contain at most five integer intercepts. The integer
square-root bounds are supplied by `rounded_height`. -/
theorem five_lines {a b M x u v w W den num LL LR : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hm : 0 ≤ M) (xp : 0 ≤ x) (up : 1 ≤ u)
    (rising : u ≤ v) (height : b*u^2=M+a*x^2)
    (width : 1 ≤ W) (wp : 0 ≤ w) (wW : w ≤ W) (dp : 0 ≤ den) (dW : den ≤ W)
    (radius : (8*a*W^3)^2 ≤ b*M) :
    let eps := 1/(4*(a+b+1)*W^2)
    let UL := LL+eps
    let slo := a*x/(b*UL)
    let shi := a*(2*x+w)/(b*(LL+LR))
    LL ≤ u → u ≤ UL → v-eps ≤ LR →
      -1 ≤ (den*slo-num)*w → (den*slo-num)*w ≤ 1 →
    (Finset.Icc (⌈den*LL+min 0 ((den*slo-num)*w)⌉ : ℤ)
      (⌊den*UL+max 0 ((den*shi-num)*w)⌋ : ℤ)).card ≤ 5 := by
  intro eps UL slo shi ll ul lr e₁ e₂
  have ha' : 0 ≤ a := by linarith only [ha]
  have hb' : 0 < b := by linarith only [hb]
  have up' : 0 < u := by linarith only [up]
  have ep : 0≤eps := by dsimp [eps]; positivity
  obtain ⟨tiny,point,rounding⟩ := precision_parameters ha hb width dW
  obtain ⟨coord,rad⟩ := coordinate_radius ha hb hm up'.le height radius
  have gap : b*u*(shi-slo) ≤ 2*a*w+4*b*a*eps :=
    rounded_gap ha' hb' xp wp up' ep (tiny.trans up) coord rising
      (by dsimp [UL] at ul; linarith only [ul]) ul
      (by dsimp [UL]; linarith only [ll]) lr
  apply integer_lines
  apply strip_width _ e₁ e₂ (scaled_gap ha' hb' up wp wW dp dW ep rad rounding gap)
  simpa only [UL,add_sub_cancel_left] using point

/-- Singletons use zero span even if the minimum allowed width is too
large for the cubic inequality. -/
theorem singleton_lines {den num LL UL slo shi : ℝ} (rounding : den*(UL-LL) ≤ 1) :
    (Finset.Icc (⌈den*LL+min 0 ((den*slo-num)*0)⌉ : ℤ)
      (⌊den*UL+max 0 ((den*shi-num)*0)⌋ : ℤ)).card ≤ 5 := by
  apply integer_lines
  simpa only [mul_zero,min_self,max_self,add_zero] using
    (show den*UL-den*LL ≤ 17/4 by linarith only [rounding])

/-- With the public cube-root schedule, every partial width within the
maximal allowed radius satisfies the squared curvature inequality. -/
theorem block_radius {a b M W W' : ℕ} (ap : 0<a)
    (fits : 64*W^3 ≤ 8*(b*M).sqrt/a) (partialWidth : W'≤W) :
    (8*a*W'^3)^2 ≤ b*M := by
  have h := (Nat.le_div_iff_mul_le ap).mp fits
  rw [show 64*W^3*a=8*(8*a*W^3) by ring] at h
  have hc : 8*a*W^3 ≤ (b*M).sqrt := by omega
  have small := Nat.pow_le_pow_left partialWidth 3
  calc
    _ ≤ (8*a*W^3)^2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ small) _
    _ ≤ (b*M).sqrt^2 := Nat.pow_le_pow_left hc _
    _ ≤ _ := Nat.sqrt_le' _

/-- The integer work bound behind the cube-root exponent. A chart scanned
up to X with full block width W uses at most 1+X/W blocks; the cubic
power of that quotient is bounded by 2048 N. This accounts for floor
division and the maximal cube-root radius even when W is forced to 1. -/
theorem chart_block_budget {N M a b X W : ℕ} (ap : 0<a) (a6 : a≤6) (wp : 0<W)
    (size : N ≤ b*M) (distance : X^2 ≤ 3*N)
    (maximal : 8*(b*M).sqrt/a < 64*(W+1)^3) : (X/W)^3 ≤ 2048*N := by
  have larger := (Nat.div_lt_iff_lt_mul ap).mp maximal
  have lim : (b*M).sqrt+1 ≤ 8*a*(W+1)^3 := by
    rw [show 64*(W+1)^3*a = 8*(8*a*(W+1)^3) by ring] at larger
    omega
  have ww : W+1 ≤ 2*W := by omega
  have rad : (b*M).sqrt+1 ≤ 384*W^3 := calc
    _ ≤ 8*a*(W+1)^3 := lim
    _ ≤ (8*6)*(2*W)^3 := Nat.mul_le_mul (Nat.mul_le_mul_left _ a6) (Nat.pow_le_pow_left ww 3)
    _ = _ := by ring
  have ncap : N ≤ 384^2*W^6 := calc
    _ ≤ b*M := size
    _ ≤ ((b*M).sqrt+1)^2 := (Nat.lt_succ_sqrt' _).le
    _ ≤ (384*W^3)^2 := Nat.pow_le_pow_left rad 2
    _ = _ := by ring
  have xcap : (X/W)^6*W^6 ≤ (3*N)^3 := calc
    _ = ((X/W)*W)^6 := by ring
    _ ≤ X^6 := Nat.pow_le_pow_left (Nat.div_mul_le_self X W) 6
    _ = (X^2)^3 := by ring
    _ ≤ _ := Nat.pow_le_pow_left distance 3
  have ws : 0<W^6 := pow_pos wp _
  have bound : ((X/W)^3)^2*W^6 ≤ (2048*N)^2*W^6 := calc
    _ = (X/W)^6*W^6 := by ring
    _ ≤ (3*N)^3 := xcap
    _ = (27*N^2)*N := by ring
    _ ≤ (27*N^2)*(384^2*W^6) := Nat.mul_le_mul_left _ ncap
    _ ≤ (2048*N)^2*W^6 := by
      have t : 27*384^2 ≤ 2048^2 := by decide
      calc
        _ = (27*384^2)*(N^2*W^6) := by ring
        _ ≤ 2048^2*(N^2*W^6) := Nat.mul_le_mul_right _ t
        _ = _ := by ring
  exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (Nat.le_of_mul_le_mul_right bound ws)

/-- The height cutoff gives exactly the finite scanned range after moving
the coordinate with positive coefficient to the left. -/
theorem orientations {D x y m N : ℤ} (point : x^2-D*y^2=m*N)
    (short : x^2+D*y^2<3*N) :
    (x^2=m*N+D*y^2 ∧ 2*D*y^2 ≤ 3*N-1-m*N) ∧
    (D*y^2=(-m)*N+x^2 ∧ 2*x^2 ≤ 3*N-1-(-m)*N) := by
  have cut := Int.add_one_le_iff.mpr short
  constructor <;> constructor <;> linarith only [point,cut]

/-- Exact quadratic after substituting den·y=J+num·j. -/
theorem line_quadratic {a b M x j y den num J : ℤ}
    (point : b*y^2=M+a*(x+j)^2) (line : J=den*y-num*j) :
    let K := b*num^2-a*den^2
    let L := b*J*num-a*den^2*x
    let C := b*J^2-den^2*(M+a*x^2)
    K*j^2+2*L*j+C=0 := by
  subst J
  dsimp
  linear_combination den^2*point

/-- Signed integer-root reconstruction on every non-linear line, including
the exact denominator for the coordinate in the curve's height direction. -/
theorem line_recovers {a b M x j y den num J : ℤ} (dpos : 0<den)
    (point : b*y^2=M+a*(x+j)^2) (line : J=den*y-num*j)
    (regular : b*num^2-a*den^2 ≠ 0) :
    let K := b*num^2-a*den^2
    let L := b*J*num-a*den^2*x
    let C := b*J^2-den^2*(M+a*x^2)
    ∃ r : ℕ, (r:ℤ)^2=L^2-K*C ∧
      ((K ∣ -L+r ∧ j=(-L+r)/K) ∨ (K ∣ -L-r ∧ j=(-L-r)/K)) ∧
      den ∣ J+num*j ∧ y=(J+num*j)/den := by
  let K := b*num^2-a*den^2
  let L := b*J*num-a*den^2*x
  let C := b*J^2-den^2*(M+a*x^2)
  change ∃ r : ℕ, (r:ℤ)^2=L^2-K*C ∧ _ ∧ _
  have sq : (K*j+L)^2=L^2-K*C := by
    have h : K*j^2+2*L*j+C=0 := line_quadratic point line
    linear_combination K*h
  refine ⟨(K*j+L).natAbs,by rw [Int.natCast_natAbs,sq_abs,sq],?_,?_,?_⟩
  · rw [Int.natCast_natAbs]
    rcases le_total 0 (K*j+L) with pos|neg
    · left
      rw [abs_of_nonneg pos,show -L+(K*j+L)=K*j by ring, Int.mul_ediv_cancel_left _ regular]
      exact ⟨dvd_mul_right _ _,rfl⟩
    · right
      rw [abs_of_nonpos neg,show -L- -(K*j+L)=K*j by ring, Int.mul_ediv_cancel_left _ regular]
      exact ⟨dvd_mul_right _ _,rfl⟩
  · rw [line,sub_add_cancel]
    exact dvd_mul_right _ _
  · rw [line,sub_add_cancel,Int.mul_ediv_cancel_left _ dpos.ne']

/-- If the squared ratio a/b is excluded, the denominator of the quadratic
root formula cannot vanish. This covers both orientations for nonsquare D. -/
theorem quadratic_nonzero {a b den num : ℤ} (d : den≠0)
    (ns : ¬IsSquare ((a:ℚ)*(b:ℚ))) : b*num^2-a*den^2 ≠ 0 := by
  intro zero
  have eq : (b:ℚ)*(num:ℚ)^2=(a:ℚ)*(den:ℚ)^2 := by exact_mod_cast sub_eq_zero.mp zero
  apply ns
  refine ⟨(b:ℚ)*num/den, ?_⟩
  have nz : (den:ℚ)≠0 := by exact_mod_cast d
  field_simp
  linear_combination -(b:ℚ)*eq

end PrimeFactors.HyperbolicNormArc
