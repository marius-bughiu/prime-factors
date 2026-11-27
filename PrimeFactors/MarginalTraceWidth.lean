import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Compare a second batch at multiplier six to continuing ordinary Fermat.
All widths refer to fixed-product factor-coordinate intervals. -/
namespace PrimeFactors.MarginalTraceWidth

open Real

/-- For n=u^4, multiplier k=j^4, and the first omitted trace
2j²u²+h, the relative upper endpoint is 1+rise/u. -/
noncomputable def rise (u j h : ℝ) : ℝ :=
  let x := √h/j
  let s := x/(2*u)
  x*(s+√(1+s^2))

noncomputable def endpoint (u j h : ℝ) := 1+rise u j h/u

theorem linear_rise {u j h : ℝ} (big : 100000≤u) (one : 1≤j) (_lo : 0≤h)
    (hi : h≤900) : √h/j ≤ rise u j h ∧ rise u j h ≤ √h/j+1/100 := by
  let x := √h/j
  let s := x/(2*u)
  have sane : √h ≤ 30 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith⟩
  have jp : 0<j := by linarith
  have up : 0<u := by linarith
  have x0 : 0≤x := div_nonneg (sqrt_nonneg _) jp.le
  have x1 : x≤30 := (div_le_iff₀ jp).mpr (by linarith)
  have sp : 0≤s := div_nonneg x0 (by positivity)
  have s1 : s≤3/20000 := (div_le_iff₀ (by positivity : 0<2*u)).mpr (by linarith)
  have sq := sq_sqrt (by positivity : 0≤1+s^2)
  have nn := sqrt_nonneg (1+s^2)
  have rt : 1≤√(1+s^2) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg s])
  have rt' : √(1+s^2)≤1+s := Real.sqrt_le_iff.mpr ⟨by linarith,by nlinarith⟩
  change x ≤ x*(s+√(1+s^2)) ∧ x*(s+√(1+s^2)) ≤ x+1/100
  constructor
  · nlinarith only [mul_nonneg x0 (show 0≤s+√(1+s^2)-1 by linarith)]
  · have prod := mul_le_mul (show s+√(1+s^2)-1≤3/10000 by linarith) x1 x0 (by norm_num)
    linarith only [prod]

/-- Exact endpoints of the positive trace interval, in factor coordinates
with center j²u²/a. -/
theorem band_iff {u j h a x : ℝ} (up : 0<u) (jp : 0<j) (hp : 0≤h)
    (ap : 0<a) :
    a*x^2 + j^4*u^4/a < (2*j^2*u^2+h)*x ↔
    j^2*u^2/a/endpoint u j h < x ∧ x < j^2*u^2/a*endpoint u j h := by
  let c := j^2*u^2/a
  let e := endpoint u j h
  let s := √h/j/(2*u)
  let z := √(1+s^2)
  have s0 : 0≤s := by dsimp [s]; positivity
  have zsq : z^2=1+s^2 := Real.sq_sqrt (by positivity)
  have z0 : 0<z := Real.sqrt_pos.mpr (by positivity)
  have id : e=(s+z)^2 := by
    change 1+(√h/j)*(s+z)/u=(s+z)^2
    have eq : √h/j/u=2*s := by dsimp only [s]; ring
    rw [show (√h/j)*(s+z)/u=(√h/j/u)*(s+z) by ring, eq]
    nlinarith only [zsq]
  have ene : 0<e := by rw [id]; positivity
  have h4 : 4*s^2*j^2*u^2=h := by
    have hs : 2*u*j*s=√h := by dsimp only [s]; field_simp; ring
    calc 4*s^2*j^2*u^2 = (2*u*j*s)^2 := by ring
         _ = h := by rw [hs, sq_sqrt hp]
  have relation : (e-1)^2*j^2*u^2=h*e := by
    have v : e-1=2*s*(s+z) := by rw [id]; nlinarith only [zsq]
    rw [v,id]
    linear_combination (s+z)^2*h4
  have ce : c/e≤c*e := by
    have e1 : 1≤e := by
      dsimp [e,endpoint,rise]
      have : 0≤√h/j*(√h/j/(2*u)+√(1+(√h/j/(2*u))^2))/u := by positivity
      linarith
    have c0 : 0<c := by dsimp [c]; positivity
    exact (div_le_iff₀ ene).mpr (by nlinarith only [mul_nonneg c0.le (sub_nonneg.mpr (one_le_pow₀ e1 (n:=2)))])
  have identity : (a*x^2+j^4*u^4/a-(2*j^2*u^2+h)*x)*e =
      a*e*((x-c/e)*(x-c*e)) := by
    dsimp [c]
    field_simp [ne_of_gt ap, ne_of_gt ene]
    linear_combination a^3*x*e*relation
  change _ ↔ c/e < x ∧ x < c*e
  constructor
  · intro hlt
    have neg := mul_neg_of_neg_of_pos (sub_neg.mpr hlt) ene
    rw [identity] at neg
    have pn : (x-c/e)*(x-c*e)<0 := by
      rcases mul_neg_iff.mp neg with h|h
      · exact h.2
      · linarith only [h.1, mul_pos ap ene]
    rcases mul_neg_iff.mp pn with h|h
    · exact ⟨sub_pos.mp h.1,sub_neg.mp h.2⟩
    · linarith only [h.1,h.2,ce]
  · rintro ⟨left,right⟩
    have n := mul_neg_of_pos_of_neg (sub_pos.mpr left) (sub_neg.mpr right)
    have neg := mul_neg_of_pos_of_neg (mul_pos ap ene) n
    rw [←identity] at neg
    rcases mul_neg_iff.mp neg with h|h
    · linarith only [h.2,ene]
    · exact sub_neg.mp h.1

/-- Excess heights of the first omitted traces. The ordinary average step
is m, and an extra ordinary label has been charged before the comparison. -/
structure Heights (m h₁ h₂ h₆ : ℝ) : Prop where
  step : m=6 ∨ m=12 ∨ m=24
  first : 16*m≤h₁
  last : h₁≤16*m+24
  ordered : h₁≤h₂
  more : h₂≤h₁+16*m+24
  six_low : 48≤h₆
  six_high : h₆≤72

private theorem sqrt_gap {x y z e d : ℝ} (z0 : 0≤z) (e0 : 0≤e)
    (base : z^2≤x) (more : y≤x+d) (room : d≤2*z*e+e^2) : √y-√x ≤ e := by
  have x0 : 0≤x := (sq_nonneg z).trans base
  have zle := (Real.le_sqrt z0 x0).mpr base
  have cross := mul_le_mul_of_nonneg_right zle e0
  have cap : √y≤√x+e := Real.sqrt_le_iff.mpr ⟨by positivity,
    by nlinarith only [sq_sqrt x0, more, room, cross]⟩
  linarith

private theorem height_gap {m a b c : ℝ} (H : Heights m a b c) :
    √b-√a ≤ 43/5 ∧ (m≤12 → √b-√a ≤ 32/5) := by
  rcases H with ⟨h,h1,_,_,delta,_,_⟩
  rcases h with rfl|rfl|rfl
  · have b := sqrt_gap (z:=39/4) (e:=32/5) (by norm_num) (by norm_num)
          (by linarith : (39/4:ℝ)^2 ≤ a) (by linarith only [delta] : b≤a+120) (by norm_num)
    exact ⟨by linarith,fun _ => b⟩
  · have b := sqrt_gap (z:=69/5) (e:=32/5) (by norm_num) (by norm_num)
          (by linarith : (69/5:ℝ)^2 ≤ a) (by linarith only [delta] : b≤a+216) (by norm_num)
    exact ⟨by linarith,fun _ => b⟩
  · have b := sqrt_gap (z:=39/2) (e:=43/5) (by norm_num) (by norm_num)
          (by linarith : (39/2:ℝ)^2 ≤ a) (by linarith only [delta] : b≤a+408) (by norm_num)
    exact ⟨b,by norm_num⟩

theorem rise_gaps {u j m a b c : ℝ} (big : 100000≤u) (j1 : 1≤j)
    (j2 : j≤157/100) (H : Heights m a b c) :
    0≤rise u 1 a ∧ 0≤rise u 1 b ∧ 44/10≤rise u j c ∧
    rise u 1 b-rise u 1 a≤861/100 ∧ (m≤12 → rise u 1 b-rise u 1 a≤641/100) := by
  have mm : 6≤m ∧ m≤24 := by rcases H.step with h|h|h <;> rw [h] <;> norm_num
  have a0 : 0≤a := by linarith only [mm.1,H.first]
  have b0 : 0≤b := a0.trans H.ordered
  have c0 : 0≤c := by linarith only [H.six_low]
  have aa := linear_rise (j:=1) big le_rfl a0 (by linarith only [H.last,mm.2])
  have bb := linear_rise (j:=1) big le_rfl b0 (by linarith only [H.more,H.last,mm.2])
  have cc := linear_rise big j1 c0 (by linarith only [H.six_high])
  simp only [div_one] at aa bb
  have cl : (691/100:ℝ) ≤ √c := (Real.le_sqrt (by norm_num) c0).mpr (by linarith only [H.six_low])
  have rat : (44/10:ℝ)≤√c/j := (le_div_iff₀ (by linarith)).mpr (by linarith)
  refine ⟨(sqrt_nonneg _).trans aa.1, (sqrt_nonneg _).trans bb.1,rat.trans cc.1,?_,?_⟩
  · linarith only [aa.1,bb.2,(height_gap H).1]
  · intro small
    linarith only [aa.1,bb.2,(height_gap H).2 small]

/-- Two-sided logarithmic width at the interior center exceeds the new
one-sided width of the ordinary continuation, including one extra trace. -/
theorem log_dominance {u j m a b c : ℝ} (big : 100000≤u) (j1 : 1≤j)
    (j2 : j≤157/100) (H : Heights m a b c) :
    Real.log (endpoint u 1 b)-Real.log (endpoint u 1 a) <
      2*Real.log (endpoint u j c) := by
  obtain ⟨A,_,C,gap,_⟩ := rise_gaps big j1 j2 H
  have up : 0<u := by linarith
  let e := endpoint u 1 a
  let f := endpoint u j c
  have e1 : 1≤e := le_add_of_nonneg_right (div_nonneg A up.le)
  have f1 : 1≤f := le_add_of_nonneg_right (div_nonneg (by linarith only [C]) up.le)
  have cap : endpoint u 1 b-e<2*(f-1) := by
    dsimp only [endpoint,e,f]
    rw [show 1+rise u 1 b/u-(1+rise u 1 a/u)=(rise u 1 b-rise u 1 a)/u by ring,
        show 2*(1+rise u j c/u-1)=2*rise u j c/u by ring]
    exact (div_lt_div_iff_of_pos_right up).mpr (by linarith only [C,gap])
  have mag := mul_nonneg (sub_nonneg.mpr e1) (sub_nonneg.mpr (one_le_pow₀ f1 (n:=2)))
  have rel : endpoint u 1 b < e*f^2 := by nlinarith only [cap,mag,sq_nonneg (f-1)]
  have posB : 0<endpoint u 1 b := by
    exact add_pos_of_pos_of_nonneg one_pos (div_nonneg (rise_gaps big j1 j2 H).2.1 up.le)
  have lg := Real.log_lt_log posB rel
  rw [Real.log_mul (by linarith : e≠0) (by positivity : f^2≠0), Real.log_pow] at lg
  change _-Real.log e < 2*Real.log f
  norm_num at lg
  linarith only [lg]

/-- Admissible offsets from the ceiling of the minimum trace. The units
modulo 24 form one orbit for each possible gcd with 24. -/
noncomputable def offsets (r o a b : ℕ) : List ℕ :=
  (List.range 24).filter (fun i => (o+i).gcd 24 == (a+b*r).gcd 24)

/-- Offset of the zero-based ith admissible trace from that ceiling. -/
noncomputable def offset (r o a b i : ℕ) : ℕ :=
  let xs := offsets r o a b
  24*(i/xs.length) + xs[i%xs.length]?.getD 0

noncomputable def step (r : ℕ) : ℕ := 24/(offsets r 0 1 1).length

private theorem ordinary_ranks : ∀ r o : Fin 24, Nat.Coprime (r:ℕ) 6 →
    (step r=6 ∨ step r=12 ∨ step r=24) ∧
    16*step r≤offset r o 1 1 16 ∧ offset r o 1 1 16<16*step r+24 ∧
    offset r o 1 1 16≤offset r o 1 1 33 ∧
    offset r o 1 1 33≤offset r o 1 1 16+16*step r+24 := by
  decide +kernel

private theorem six_ranks : ∀ r o : Fin 24, Nat.Coprime (r:ℕ) 6 →
    48≤offset r o 3 2 16 ∧ offset r o 3 2 16<72 := by
  decide +kernel

/-- The two (potentially unrelated) ceiling errors are retained. In the two
ordinary batches they coincide because the starting real trace is the same. -/
theorem public_heights (r o v : Fin 24) (unit : Nat.Coprime (r:ℕ) 6)
    (x y : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    Heights (step r) (offset r o 1 1 16+x) (offset r o 1 1 33+x) (offset r v 3 2 16+y) := by
  obtain ⟨st,f0,f1,inc,d⟩ := ordinary_ranks r o unit
  obtain ⟨g0,g1⟩ := six_ranks r v unit
  constructor
  · rcases st with h|h|h
    · left; exact_mod_cast h
    · right; left; exact_mod_cast h
    · right; right; exact_mod_cast h
  · have : (16:ℝ)*step r ≤ offset r o 1 1 16 := by exact_mod_cast f0
    linarith only [this,hx.1]
  · have : (offset r o 1 1 16:ℝ)+1 ≤ 16*step r+24 := by exact_mod_cast f1
    linarith only [this,hx.2]
  · have : (offset r o 1 1 16:ℝ)≤offset r o 1 1 33 := by exact_mod_cast inc
    linarith only [this]
  · have : (offset r o 1 1 33:ℝ) ≤ offset r o 1 1 16+16*step r+24 := by exact_mod_cast d
    linarith only [this]
  · have : (48:ℝ)≤offset r v 3 2 16 := by exact_mod_cast g0
    linarith only [this,hy.1]
  · have : (offset r v 3 2 16:ℝ)+1≤72 := by exact_mod_cast g1
    linarith only [this,hy.2]

private theorem cycle_sizes : ∀ r o : Fin 24, Nat.Coprime (r:ℕ) 6 →
    0 < (offsets r o 1 1).length ∧ step r*(offsets r o 1 1).length=24 := by
  decide +kernel

theorem ordinary_multiple (r o : Fin 24) (unit : (r:ℕ).Coprime 6) {i : ℕ}
    (divides : (offsets r o 1 1).length ∣ i) :
    offset r o 1 1 i = offset r o 1 1 0 + step r * i := by
  obtain ⟨pos,period⟩ := cycle_sizes r o unit
  obtain ⟨k,rfl⟩ := divides
  dsimp only [offset]
  rw [Nat.mul_div_cancel_left _ pos, Nat.mul_mod_right, Nat.zero_div, Nat.zero_mod]
  rw [mul_zero,zero_add,←mul_assoc,period,add_comm]

noncomputable def sixRoot : ℝ := √(√6)

theorem six_root_bounds : 1≤sixRoot ∧ sixRoot≤157/100 ∧
    81/100≤sixRoot^2/3 ∧ sixRoot^2/3≤82/100 ∧ sixRoot^4=6 := by
  have lo : (243/100:ℝ)≤√6 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hi : √(6:ℝ)≤246/100 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have jsq : sixRoot^2=√6 := sq_sqrt (sqrt_nonneg _)
  constructor
  · exact (Real.le_sqrt (by norm_num) (sqrt_nonneg _)).mpr (by linarith only [lo])
  constructor
  · exact Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [hi]⟩
  refine ⟨by linarith only [lo,jsq],by linarith only [hi,jsq],?_⟩
  rw [show sixRoot^4=(sixRoot^2)^2 by ring,jsq,sq_sqrt (by norm_num)]

theorem endpoint_small {u j h : ℝ} (big : 100000≤u) (j1 : 1≤j) (lo : 0≤h)
    (hi : h≤900) : 1≤endpoint u j h ∧ endpoint u j h≤1001/1000 := by
  have up : 0<u := by linarith
  have jp : 0<j := by linarith
  have g := linear_rise big j1 lo hi
  have rt : √h≤30 := Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [hi]⟩
  have x : √h/j≤30 := (div_le_iff₀ jp).mpr (by linarith)
  have g0 := (div_nonneg (sqrt_nonneg h) jp.le).trans g.1
  have g1 : rise u j h/u ≤ 1/1000 := (div_le_iff₀ up).mpr (by linarith only [g.2,x,big])
  exact ⟨le_add_of_nonneg_right (div_nonneg g0 up.le),by dsimp [endpoint]; linarith only [g1]⟩

/-- Every ordinary endpoint is above .99√N, and both interior endpoints
fall between .80√N and .83√N. Thus the new window is disjoint and unclipped
whenever the feasible lower endpoint is at most .80√N. -/
theorem separated {u m a b c : ℝ} (big : 100000≤u) (H : Heights m a b c) :
    (99/100)*u^2 < u^2/endpoint u 1 b ∧
    (80/100)*u^2 < (sixRoot^2/3*u^2)/endpoint u sixRoot c ∧
    (sixRoot^2/3*u^2)*endpoint u sixRoot c < (83/100)*u^2 := by
  obtain ⟨j1,_,jl,jh,_⟩ := six_root_bounds
  have mm : 6≤m ∧ m≤24 := by rcases H.step with h|h|h <;> rw [h] <;> norm_num
  have a0 : 0≤a := by linarith only [H.first,mm.1]
  have ep := endpoint_small (j:=1) big le_rfl (a0.trans H.ordered)
    (by linarith only [H.more,H.last,mm.2])
  have gp := endpoint_small big j1 (by linarith only [H.six_low] : 0≤c) (by linarith only [H.six_high])
  have t0 : 0<u^2 := sq_pos_of_pos (by linarith)
  refine ⟨(lt_div_iff₀ (by linarith only [ep.1])).mpr ?_,
    (lt_div_iff₀ (by linarith only [gp.1])).mpr ?_,?_⟩
  · have := mul_lt_mul_of_pos_right (show 99/100*endpoint u 1 b<1 by linarith only [ep.2]) t0
    linarith only [this]
  · have := mul_lt_mul_of_pos_right (show 80/100*endpoint u sixRoot c<sixRoot^2/3 by linarith only [gp.2,jl]) t0
    linarith only [this]
  · have z := mul_le_mul jh gp.2 (by linarith only [gp.1]) (by norm_num)
    have := mul_lt_mul_of_pos_right (show sixRoot^2/3*endpoint u sixRoot c < 83/100 by linarith only [z]) t0
    linarith only [this]

/-- The rounded public equal-width lower bound lies below .80√N
throughout the fixed product slice, including its endpoints. -/
theorem slice_lower {B t : ℝ} (large : 10000≤B) (tp : 0≤t)
    (lo : 9/16*B^2≤t^2) (hi : t^2≤5/8*B^2) :
    max (B/2) (⌈t^2/(B-1)⌉:ℤ) ≤ 80/100*t := by
  have B0 : 0<B := by linarith
  have tlo : (3/4)*B≤t := le_of_sq_le_sq (by linarith only [lo]) tp
  have thi : t≤(159/200)*B := le_of_sq_le_sq (by nlinarith only [hi,sq_nonneg B]) (by positivity)
  have h : t/(B-1)≤799/1000 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have prod := mul_le_mul_of_nonneg_left h tp
  have calcP : t*(t/(B-1))=t^2/(B-1) := by ring
  rw [calcP] at prod
  have add := Int.ceil_lt_add_one (t^2/(B-1))
  exact max_le (by linarith only [tlo,large]) (by linarith only [add,prod,tlo,large])

/-- For the six residues giving at least two ordinary trace classes, even
the ordinary-coordinate lengths (and hence integer-position counts after
rounding) favor the multiplier-six window. -/
theorem length_margin {u m a b c : ℝ} (big : 100000≤u) (H : Heights m a b c)
    (small : m≤12) :
    u^2/endpoint u 1 a-u^2/endpoint u 1 b + u/4 <
      (sixRoot^2/3*u^2)*endpoint u sixRoot c-(sixRoot^2/3*u^2)/endpoint u sixRoot c := by
  have up : 0<u := by linarith
  obtain ⟨j1,j2,jl,_,_⟩ := six_root_bounds
  obtain ⟨g1,g2,g6,_,gap⟩ := rise_gaps big j1 j2 H
  let e := endpoint u 1 a
  let f := endpoint u 1 b
  let y := endpoint u sixRoot c
  have e1 : 1≤e := le_add_of_nonneg_right (div_nonneg g1 up.le)
  have f1 : 1≤f := le_add_of_nonneg_right (div_nonneg g2 up.le)
  have yf := endpoint_small big j1 (by linarith only [H.six_low] : 0≤c) (by linarith only [H.six_high])
  have y1 : 1≤y := yf.1
  have y2 : y≤1001/1000 := yf.2
  have udelta : (f-e)*u≤641/100 := by
    change ((1+rise u 1 b/u)-(1+rise u 1 a/u))*u ≤ _
    rw [show ((1+rise u 1 b/u)-(1+rise u 1 a/u))*u=rise u 1 b-rise u 1 a by field_simp]
    exact gap small
  have ud6 : 44/10 ≤ (y-1)*u := by
    change _≤(1+rise u sixRoot c/u-1)*u
    rwa [show (1+rise u sixRoot c/u-1)*u=rise u sixRoot c by field_simp]
  have ef0 : 0<e*f := mul_pos (by linarith) (by linarith)
  have ef1 : 1≤e*f := one_le_mul_of_one_le_of_one_le e1 f1
  have ord : u^2/e-u^2/f ≤ (641/100)*u := by
    rw [show u^2/e-u^2/f = ((f-e)*u*u)/(e*f) by field_simp; ring]
    apply (div_le_iff₀ ef0).mpr
    calc (f-e)*u*u ≤ (641/100)*u := mul_le_mul_of_nonneg_right udelta up.le
         _ ≤ (641/100)*u*(e*f) := le_mul_of_one_le_right (by positivity) ef1
  have yp : 0<y := by linarith
  have yi : 99/100≤1/y := (le_div_iff₀ yp).mpr (by linarith only [y2])
  have interior : 7*u ≤ (sixRoot^2/3*u^2)*y-(sixRoot^2/3*u^2)/y := by
    have v := mul_le_mul jl ud6 (by linarith) (by positivity)
    have w := mul_le_mul v (show 199/100≤1+1/y by linarith only [yi]) (by norm_num) (by positivity)
    have s : 7 ≤ sixRoot^2/3*((y-1)*u)*(1+1/y) := by linarith only [w]
    have t := mul_le_mul_of_nonneg_right s up.le
    convert t using 1
    field_simp
    ring
  change u^2/e-u^2/f+u/4 < (sixRoot^2/3*u^2)*y-(sixRoot^2/3*u^2)/y
  linarith only [ord,interior,big]

theorem length_dominance {u m a b c : ℝ} (big : 100000≤u) (H : Heights m a b c)
    (small : m≤12) :
    u^2/endpoint u 1 a-u^2/endpoint u 1 b + 10 <
      (sixRoot^2/3*u^2)*endpoint u sixRoot c-(sixRoot^2/3*u^2)/endpoint u sixRoot c := by
  linarith only [length_margin big H small,big]

/-- The public excess height at zero-based index i, with u=n^(1/4).
The residue of the starting ceiling is computed independently for each multiplier. -/
noncomputable def height (r : Fin 24) (u j : ℝ) (a b i : ℕ) : ℝ :=
  let start := 2*j^2*u^2
  let top := ⌈start⌉₊
  (offset r (top%24) a b i : ℝ) + ((top:ℝ)-start)

theorem actual_heights (r : Fin 24) (unit : (r:ℕ).Coprime 6) (u : ℝ) :
    Heights (step r) (height r u 1 1 1 16) (height r u 1 1 1 33) (height r u sixRoot 3 2 16) := by
  have ceiling (s : ℝ) (s0 : 0≤s) : ((⌈s⌉₊:ℝ)-s) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨sub_nonneg.mpr (Nat.le_ceil _),by linarith only [Nat.ceil_lt_add_one s0]⟩
  apply public_heights (o:=⟨_,Nat.mod_lt _ (by decide)⟩) (v:=⟨_,Nat.mod_lt _ (by decide)⟩) r unit _ _
  · exact ceiling _ (by positivity)
  · exact ceiling _ (by positivity)

theorem ordinary_span {u m a b h : ℝ} (big : 100000≤u) (H : Heights m a b h) :
    u^2/endpoint u 1 b ≤ u^2/endpoint u 1 a := by
  apply div_le_div_of_nonneg_left (sq_nonneg _)
  · have H0 := (rise_gaps big six_root_bounds.1 six_root_bounds.2.1 H).1
    exact add_pos_of_pos_of_nonneg one_pos (div_nonneg H0 (by linarith))
  · dsimp only [endpoint,rise]
    gcongr <;> exact H.ordered

/-- Full fixed-batch log-width comparison using only the two public starting
ceilings, the product residue, and the fourth root of the product. -/
theorem actual_log_dominance (r : Fin 24) (unit : (r:ℕ).Coprime 6) {u : ℝ} (big : 100000≤u) :
    Real.log (endpoint u 1 (height r u 1 1 1 33)) -
      Real.log (endpoint u 1 (height r u 1 1 1 16)) <
      2*Real.log (endpoint u sixRoot (height r u sixRoot 3 2 16)) :=
  log_dominance big six_root_bounds.1 six_root_bounds.2.1 (actual_heights r unit u)

private theorem residue_unit (n : ℕ) (hn : n.Coprime 6) : (n%24).Coprime 6 := by
  change (n%24).gcd 6 = 1
  rw [Nat.gcd_comm, Nat.gcd_rec, Nat.mod_mod_of_dvd _ (by decide : 6∣24), ←Nat.gcd_rec, Nat.gcd_comm]
  exact hn

noncomputable def productRoot (n : ℕ) : ℝ := √(√(n:ℝ))

/-- Every odd product coprime to six in the specified 2048-bit slice has
a disjoint, unclipped multiplier-six interval and strict marginal log-width
dominance. The upper bound for each equal-width prime is B-1. -/
theorem target {n : ℕ} (hn : n.Coprime 6)
    (lo : 9/16*(2^1024:ℝ)^2 ≤ n) (hi : (n:ℝ)≤5/8*(2^1024:ℝ)^2) :
    let u := productRoot n
    let t := u^2
    let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
    let e := endpoint u 1 (height r u 1 1 1 16)
    let f := endpoint u 1 (height r u 1 1 1 33)
    let y := endpoint u sixRoot (height r u sixRoot 3 2 16)
    let center := sixRoot^2/3*t
    max ((2^1024:ℝ)/2) (⌈(n:ℝ)/(2^1024-1)⌉:ℤ) < center/y ∧
    center*y < t/f ∧ log f-log e<2*log y ∧
    (step r≤12 → t/e-t/f+10<center*y-center/y) := by
  dsimp only
  let u := productRoot n
  let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
  have eqt : u^2=√(n:ℝ) := sq_sqrt (sqrt_nonneg _)
  have eqn : (u^2)^2=(n:ℝ) := by rw [eqt,sq_sqrt (by positivity)]
  have up : 0≤u := sqrt_nonneg _
  have Bb : (10000:ℝ)≤2^1024 := by norm_num
  have big : 100000≤u := by
    apply le_of_sq_le_sq _ up
    apply le_of_sq_le_sq _ (sq_nonneg u)
    rw [eqn]
    exact le_trans (by norm_num) lo
  have small := slice_lower Bb (sq_nonneg u) (eqn.symm ▸ lo) (eqn.symm ▸ hi)
  rw [eqn] at small
  have good : (r:ℕ).Coprime 6 := residue_unit n hn
  have H := actual_heights r good u
  have geo := separated big H
  refine ⟨small.trans_lt geo.2.1,?_,actual_log_dominance r good big,?_⟩
  · exact geo.2.2.trans (((mul_lt_mul_of_pos_right (by norm_num : (83/100:ℝ)<99/100)
         (sq_pos_of_pos (by linarith : 0<u)))).trans geo.1)
  · intro m
    exact length_dominance big H (by exact_mod_cast m)

theorem more_sites {a b l h : ℝ} (span : a≤b) (gain : b-a+2<h-l) :
    (Finset.Icc ⌈a⌉ ⌊b⌋).card < (Finset.Ioo ⌊l⌋ ⌈h⌉).card := by
  have inequality : ((⌊b⌋:ℤ):ℝ) + 1 - (⌈a⌉:ℤ) < (⌈h⌉:ℤ) - (⌊l⌋:ℤ) - 1 := by
    linarith only [Int.floor_le b,Int.le_ceil a,Int.le_ceil h,Int.floor_le l,gain]
  have sign : (0:ℝ) < (⌈h⌉:ℤ) - (⌊l⌋:ℤ) - 1 := by
    linarith only [Int.le_ceil h,Int.floor_le l,span,gain]
  have hi : ⌊b⌋ + 1 - ⌈a⌉ < ⌈h⌉ - ⌊l⌋ - 1 := by exact_mod_cast inequality
  have hp : 0 < ⌈h⌉ - ⌊l⌋ - 1 := by exact_mod_cast sign
  rw [Int.card_Icc,Int.card_Ioo]
  omega
/-- Even counting both endpoints for the ordinary shell and omitting both
endpoints for multiplier six, more integer sites lie in the multiplier-six
window for these six residues. Apply target for the feasibility and disjointness. -/
theorem integer_sites {n : ℕ} (hn : n.Coprime 6) {u : ℝ} (big : 100000≤u)
    (reg : n%24≠11 ∧ n%24≠23) :
    let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
    let e := endpoint u 1 (height r u 1 1 1 16)
    let f := endpoint u 1 (height r u 1 1 1 33)
    let y := endpoint u sixRoot (height r u sixRoot 3 2 16)
    let center := sixRoot^2/3*u^2
    (Finset.Icc ⌈u^2/f⌉ ⌊u^2/e⌋).card < (Finset.Ioo ⌊center/y⌋ ⌈center*y⌉).card := by
  let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
  have ru : (r:ℕ).Coprime 6 := residue_unit n hn
  have sr : ∀ v : Fin 24, (v:ℕ).Coprime 6 → (v:ℕ)≠11 → (v:ℕ)≠23 → step v≤12 := by decide +kernel
  have H := actual_heights r ru u
  have cap := length_dominance big H (by exact_mod_cast sr r ru reg.1 reg.2)
  dsimp only
  apply more_sites
  · exact ordinary_span big H
  · linarith only [cap]

/-- In the two residue classes with a single ordinary sum modulo 24, the
ordinary continuation has the longer interval in the usual integer scale. -/
theorem exceptional_width {n : ℕ} {u : ℝ} (big : 100000≤u)
    (reg : n%24=11 ∨ n%24=23) :
    let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
    let e := endpoint u 1 (height r u 1 1 1 16)
    let f := endpoint u 1 (height r u 1 1 1 33)
    let y := endpoint u sixRoot (height r u sixRoot 3 2 16)
    let c := sixRoot^2/3*u^2
    c/y ≤ c*y ∧ c*y-c/y+u/20 < u^2/e-u^2/f := by
  let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
  let a := height r u 1 1 1 16
  let b := height r u 1 1 1 33
  let h := height r u sixRoot 3 2 16
  let e := endpoint u 1 a
  let f := endpoint u 1 b
  let y := endpoint u sixRoot h
  let c := sixRoot^2/3*u^2
  have ex : (r:ℕ)=11 ∨ (r:ℕ)=23 := reg
  have table : ∀ z o : Fin 24, (z:ℕ)=11 ∨ (z:ℕ)=23 →
      (z:ℕ).Coprime 6 ∧ step z=24 ∧
      offset z o 1 1 33=offset z o 1 1 16+408 ∧ offset z o 3 2 16≤51 := by decide +kernel
  obtain ⟨unit,st,_,_⟩ := table r 0 ex
  have H := actual_heights r unit u
  have delta : b=a+408 := by
    dsimp only [a,b,height]
    rw [(table r ⟨_,Nat.mod_lt _ (by decide)⟩ ex).2.2.1,Nat.cast_add,Nat.cast_ofNat]
    ring
  have room : h≤52 := by
    let start := 2*sixRoot^2*u^2
    have cap0 := (table r ⟨⌈start⌉₊%24,Nat.mod_lt _ (by decide)⟩ ex).2.2.2
    have cap : (offset r (⌈start⌉₊%24) 3 2 16:ℝ)≤51 := by exact_mod_cast cap0
    change (offset r (⌈start⌉₊%24) 3 2 16:ℝ)+((⌈start⌉₊:ℝ)-start)≤52
    linarith only [cap,Nat.ceil_lt_add_one (by dsimp [start]; positivity : 0≤start)]
  have HS : (step r:ℝ)=24 := by exact_mod_cast st
  have a0 : 0≤a := by linarith only [HS,H.first]
  have ah : a≤408 := by linarith only [HS,H.last]
  have b0 : 0≤b := a0.trans H.ordered
  have h0 : 0≤h := by linarith only [H.six_low]
  have btop : b≤900 := by linarith only [ah,delta]
  have aw := linear_rise (j:=1) big le_rfl a0 (by linarith only [ah])
  have bw := linear_rise (j:=1) big le_rfl b0 btop
  have hw := linear_rise big six_root_bounds.1 h0 (by linarith only [room])
  simp only [div_one] at aw bw
  have a_rt : √a≤81/4 := sqrt_le_iff.mpr ⟨by norm_num, by linarith only [ah]⟩
  have diff : √a+33/4≤√b := (Real.le_sqrt (by positivity) b0).mpr (by nlinarith only [a_rt,sq_sqrt a0,delta])
  have gap : 824/100 ≤ rise u 1 b-rise u 1 a := by linarith only [diff,aw.2,bw.1]
  have jlow : (3/2:ℝ)≤sixRoot := by
    apply (Real.le_sqrt (by norm_num) (sqrt_nonneg 6)).mpr
    apply (Real.le_sqrt (by positivity) (by norm_num)).mpr
    norm_num
  have h_rt : √h≤29/4 := sqrt_le_iff.mpr ⟨by norm_num, by linarith only [room]⟩
  have hg : √h/sixRoot ≤ 29/6 := (div_le_iff₀ (by linarith)).mpr (by linarith only [h_rt,jlow])
  have htop : rise u sixRoot h≤97/20 := by linarith only [hw.2,hg]
  have up : 0<u := by linarith only [big]
  have E := endpoint_small (j:=1) big le_rfl a0 (by linarith only [ah])
  have F := endpoint_small (j:=1) big le_rfl b0 btop
  have Y := endpoint_small big six_root_bounds.1 h0 (by linarith only [room])
  have e1 : 1≤e := E.1
  have f1 : 1≤f := F.1
  have y1 : 1≤y := Y.1
  have yp : 0<y := by linarith only [y1]
  have ef0 : 0<e*f := mul_pos (by linarith) (by linarith)
  have efcap : e*f≤(1001/1000)^2 := by simpa only [pow_two] using mul_le_mul E.2 F.2 (by linarith only [F.1]) (by norm_num)
  have g : (81/10)*(e*f)≤rise u 1 b-rise u 1 a := by linarith only [efcap,gap]
  have ediff : (f-e)*u=rise u 1 b-rise u 1 a := by dsimp only [e,f,endpoint]; field_simp
  have ord : (81/10)*u≤u^2/e-u^2/f := by
    rw [show u^2/e-u^2/f=((f-e)*u*u)/(e*f) by field_simp; ring,ediff]
    apply (le_div_iff₀ ef0).mpr
    linarith only [mul_le_mul_of_nonneg_right g up.le]
  have yi : 1/y≤1 := (div_le_iff₀ yp).mpr (by simpa)
  have z0 : 0≤rise u sixRoot h := (div_nonneg (sqrt_nonneg _) (by linarith only [jlow])).trans hw.1
  have gain := mul_le_mul six_root_bounds.2.2.2.1 htop z0 (by norm_num)
  have gain' := mul_le_mul gain (show 1+1/y≤2 by linarith only [yi]) (by positivity) (by norm_num)
  have limit : sixRoot^2/3*rise u sixRoot h*(1+1/y) ≤ 8 := by linarith only [gain']
  have yr : (y-1)*u=rise u sixRoot h := by dsimp only [y,endpoint]; field_simp
  have interior : c*y-c/y ≤ 8*u := by
    have eq : c*y-c/y = (sixRoot^2/3*((y-1)*u)*(1+1/y))*u := by dsimp only [c]; field_simp; ring
    rw [eq,yr]
    exact mul_le_mul_of_nonneg_right limit up.le
  change c/y≤c*y ∧ c*y-c/y+u/20<u^2/e-u^2/f
  have cp : 0≤c := by dsimp [c]; positivity
  exact ⟨(div_le_self cp y1).trans (le_mul_of_one_le_right cp y1),by linarith only [ord,interior,big]⟩

/-- On the remaining two residues even conservative endpoint rounding favors
ordinary continuation when counting individual integer locations. -/
theorem exceptional_sites {n : ℕ} {u : ℝ} (big : 100000≤u)
    (reg : n%24=11 ∨ n%24=23) :
    let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
    let e := endpoint u 1 (height r u 1 1 1 16)
    let f := endpoint u 1 (height r u 1 1 1 33)
    let y := endpoint u sixRoot (height r u sixRoot 3 2 16)
    let c := sixRoot^2/3*u^2
    (Finset.Icc ⌈c/y⌉ ⌊c*y⌋).card < (Finset.Ioo ⌊u^2/f⌋ ⌈u^2/e⌉).card := by
  obtain ⟨span,gt⟩ := exceptional_width big reg
  apply more_sites span
  linarith only [gt,big]

end PrimeFactors.MarginalTraceWidth
