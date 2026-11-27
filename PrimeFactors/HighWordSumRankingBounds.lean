import PrimeFactors.Fermat
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Square-root estimates for ranking factor sums in a high product word.
After the first midpoint above the end of the word, the real interval of
admissible half-gaps gets shorter by at least two at widths of 14 bits or more. -/

namespace PrimeFactors.HighWordSumRankingBounds

structure Frame (B n T : ℕ) : Prop where
  space : B ≤ 2*(T.sqrt+1)+1
  excess : (T.sqrt+1)^2-T ≤ 2*B
  above : T < (T.sqrt+1)^2
  prev : (T.sqrt-1)^2 < n
  ceil_eq : PrimeFactors.ceilSqrt T = T.sqrt+1

/-- A word with top bit set begins above the penultimate square and ends
strictly between two consecutive squares. -/
theorem endpoints {b h : ℕ} (hb : 14 ≤ b) (low : 2^b / 2 ≤ h) (high : h < 2^b) :
    Frame (2^b) (2^b*h) (2^b*h+(2^b-1)) := by
  obtain ⟨j,hj⟩ : ∃ j : ℕ, b=j+2 := ⟨b-2,by omega⟩
  let d := 2^j
  have bp : 2^b=4*d := by rw [hj,pow_add]; dsimp [d]; ring
  have dp : 0<d := pow_pos (by decide : 0<2) _
  have dl : 2≤d := by
    change 2 ≤ 2^j
    calc 2 = 2^1 := by decide
         _ ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
  rw [bp] at low high ⊢
  have dh : 2*d ≤ h := by omega
  let n := 4*d*h
  let T := n+(4*d-1)
  let a := T.sqrt
  change Frame (4*d) n T
  have nw : n+4*d=T+1 := by dsimp [T]; omega
  have al : a^2≤T := Nat.le_sqrt'.mp (le_refl _)
  have au : T<(a+1)^2 := Nat.lt_succ_sqrt' _
  have Tmin : (2*d+1)^2≤T := by
    have hm := Nat.mul_le_mul_left (4*d) dh
    change 4*d*(2*d)≤n at hm
    nlinarith only [hm,nw,dl,Nat.zero_le ((d-1)^2)]
  have amin : 2*d+1≤a := Nat.le_sqrt'.mpr Tmin
  have Tmax : T<(4*d)^2 := by
    have bound := Nat.mul_le_mul_left (4*d) (show h+1≤4*d by omega)
    dsimp [n] at nw
    nlinarith only [bound,nw]
  have amax : a<4*d := Nat.sqrt_lt'.mpr Tmax
  have mult : T+1 = 4*(d*h+d) := by rw [←nw]; dsimp [n]; ring
  have tmod : T%4=3 := by omega
  have nonsq : a^2<T := by
    apply lt_of_le_of_ne al
    intro same
    have bad : a^2%4=3 := same ▸ tmod
    have sqmod : ∀ k : Fin 4, k.val^2%4≠3 := by decide
    have sm := sqmod ⟨a%4,Nat.mod_lt _ (by decide)⟩
    change (a%4)^2%4≠3 at sm
    rw [Nat.pow_mod] at bad
    exact sm bad
  have pred_eq : a-1+1=a := by omega
  have prev : (a-1)^2<n := by
    nlinarith only [congrArg (·^2) pred_eq, al,nw,amin,pred_eq]
  have ce : PrimeFactors.ceilSqrt T=a+1 := by
    have up := PrimeFactors.ceilSqrt_le_iff.mpr au.le
    have down : ¬PrimeFactors.ceilSqrt T≤a := fun h => (not_le_of_gt nonsq) (PrimeFactors.ceilSqrt_le_iff.mp h)
    omega
  exact ⟨by change 4*d≤2*(a+1)+1; omega,
    by
      change (a+1)^2-T≤2*(4*d)
      have bound : (a+1)^2≤T+2*(4*d) := by nlinarith only [al,amax]
      omega,
    au, prev, ce⟩

/-- Two equal-width intervals at separation s², with their square roots
bounded by 2s. The inverse width estimate retains the actual width W. -/
theorem width_product_drop {s W a b c d : ℝ} (sp : 0<s) (wp : 0<W)
    (an : 0≤a) (ab : a<b) (ac : a≤c) (bd : b≤d) (cd : c≤d) (cap : d≤2*s)
    (w1 : b^2-a^2=W) (w2 : d^2-c^2=W)
    (s1 : c^2-a^2=s^2) (s2 : d^2-b^2=s^2) :
    W≤32*s*((b-a)-(d-c)) := by
  have move {v z : ℝ} (vz : v≤z) (limit : v+z≤4*s) (square : z^2-v^2=s^2) :
      s≤4*(z-v) := by
    have t := mul_le_mul_of_nonneg_left limit (sub_nonneg.mpr vz)
    exact le_of_mul_le_mul_left (a:=s) (by nlinarith only [square,t]) sp
  have ca := move ac (by linarith) s1
  have db := move bd (by linarith) s2
  have span : s/2≤(c+d)-(a+b) := by linarith
  let V := (a+b)*(c+d)
  let diff := (b-a)-(d-c)
  have vp : 0<V := mul_pos (by linarith) (by linarith)
  have id : diff*V=W*((c+d)-(a+b)) := by
    dsimp [diff,V]
    linear_combination (c+d)*w1-(a+b)*w2
  have difp : 0<diff := pos_of_mul_pos_left (id ▸ mul_pos wp (by linarith)) vp.le
  have capV : V≤16*s^2 := by
    have t := mul_le_mul (show a+b≤4*s by linarith) (show c+d≤4*s by linarith)
      (show 0≤c+d by linarith) (show 0≤4*s by linarith)
    dsimp [V]; nlinarith only [t]
  have t := mul_le_mul_of_nonneg_left capV difp.le
  have u := mul_le_mul_of_nonneg_left span wp.le
  apply le_of_mul_le_mul_right (a:=s) _ sp
  change W*s ≤ 32*s*diff*s
  nlinarith only [id,t,u]

/-- For roots a²=x, b²=x+w, c²=x+B, d²=x+B+w with x≤2B and
B/2≤w≤B, the length of the square-root interval decreases by at
least sqrt(B)/64 after a shift of B. -/
private theorem width_drop {s W a b c d : ℝ} (sp : 0<s) (wp : s^2/2≤W)
    (an : 0≤a) (ab : a<b) (ac : a≤c) (bd : b≤d) (cd : c≤d) (cap : d≤2*s)
    (w1 : b^2-a^2=W) (w2 : d^2-c^2=W)
    (s1 : c^2-a^2=s^2) (s2 : d^2-b^2=s^2) :
    s ≤ 64*((b-a)-(d-c)) := by
  have wp' : 0<W := lt_of_lt_of_le (half_pos (sq_pos_of_pos sp)) wp
  have gain := width_product_drop sp wp' an ab ac bd cd cap w1 w2 s1 s2
  apply le_of_mul_le_mul_left (a:=s) _ sp
  nlinarith only [gain,wp]

/-- Increasing the squared lower endpoint shortens the half-gap interval. -/
theorem width_antitone {x y w : ℝ} (xn : 0≤x) (xy : x≤y) (wp : 0<w) :
    Real.sqrt (y+w)-Real.sqrt y ≤ Real.sqrt (x+w)-Real.sqrt x := by
  have yn : 0≤y := xn.trans xy
  have key (z : ℝ) (nonneg : 0≤z) :
      (Real.sqrt (z+w)-Real.sqrt z)*(Real.sqrt (z+w)+Real.sqrt z)=w := by
    nlinarith only [Real.sq_sqrt nonneg,Real.sq_sqrt (by linarith : 0≤z+w)]
  have xpos : 0<Real.sqrt (x+w)+Real.sqrt x := add_pos_of_pos_of_nonneg
    (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_nonneg _)
  have pos : 0≤Real.sqrt (y+w)-Real.sqrt y :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  apply le_of_mul_le_mul_right (a:=Real.sqrt (x+w)+Real.sqrt x) _ xpos
  calc
    _ ≤ (Real.sqrt (y+w)-Real.sqrt y)*(Real.sqrt (y+w)+Real.sqrt y) :=
      mul_le_mul_of_nonneg_left (add_le_add (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_le_sqrt xy)) pos
    _ = w := key y yn
    _ = _ := (key x xn).symm

private theorem real_drop {x y W B : ℝ} (large : 16384≤B) (xn : 0≤x) (close : x≤2*B)
    (lo : B/2≤W) (hi : W≤B) (shift : x+B≤y) :
    Real.sqrt (y+W)-Real.sqrt y+2 ≤ Real.sqrt (x+W)-Real.sqrt x := by
  have bn : 0≤B := by linarith
  have wp : 0<W := by linarith
  have ss := Real.sq_sqrt bn
  have bound : 128≤Real.sqrt B := Real.le_sqrt_of_sq_le (by norm_num; exact large)
  have cap : Real.sqrt (x+B+W)≤2*Real.sqrt B := Real.sqrt_le_iff.mpr
    ⟨by positivity, by nlinarith only [ss,hi,close]⟩
  have aa := Real.sq_sqrt xn
  have bb := Real.sq_sqrt (by linarith : 0≤x+W)
  have cc := Real.sq_sqrt (by linarith : 0≤x+B)
  have dd := Real.sq_sqrt (by linarith : 0≤x+B+W)
  have gap := width_drop
    (s:=Real.sqrt B) (W:=W) (a:=Real.sqrt x) (b:=Real.sqrt (x+W))
    (c:=Real.sqrt (x+B)) (d:=Real.sqrt (x+B+W))
    (by linarith) (by linarith) (Real.sqrt_nonneg x)
    (Real.sqrt_lt_sqrt xn (by linarith)) (Real.sqrt_le_sqrt (by linarith))
    (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_le_sqrt (by linarith)) cap
    (by linarith only [aa,bb]) (by linarith only [cc,dd])
    (by linarith only [aa,cc,ss]) (by linarith only [bb,dd,ss])
  have decrease := width_antitone (by linarith : 0≤x+B) shift wp
  linarith only [gap,bound,decrease]

/-- Starting at the first specified upper-side midpoint, any later integer row
loses at least two units of the real interval of possible half-gaps. -/
theorem drop_two {n w B r u : ℕ} (large : 16384≤B) (width : w+1=B)
    (above : n+w<r^2) (close : r^2-(n+w)≤2*B) (step : B≤2*r+1) (later : r<u) :
    Real.sqrt ((u^2-n:ℕ):ℝ) - Real.sqrt ((u^2-(n+w):ℕ):ℝ) + 2 ≤
    Real.sqrt ((r^2-n:ℕ):ℝ) - Real.sqrt ((r^2-(n+w):ℕ):ℝ) := by
  let x := r^2-(n+w)
  let y := u^2-(n+w)
  have squares := Nat.pow_le_pow_left (show r+1≤u by omega) 2
  have room : r^2+B≤u^2 := by nlinarith only [squares,step]
  have shift : x+B≤y := by dsimp [x,y]; omega
  have ra : r^2-n=x+w := by dsimp [x]; omega
  have ua : u^2-n=y+w := by dsimp [y]; omega
  rw [ua,ra,Nat.cast_add,Nat.cast_add]
  apply real_drop (B:=(B:ℝ)) (x:=(x:ℝ)) (y:=(y:ℝ)) (W:=(w:ℝ)) (by exact_mod_cast large) (by positivity) (by exact_mod_cast close) _ _ (by exact_mod_cast shift)
  · have twice : B≤2*w := by omega
    have cast : (B:ℝ)≤2*(w:ℝ) := by exact_mod_cast twice
    linarith
  · exact_mod_cast (show w≤B by omega)

end PrimeFactors.HighWordSumRankingBounds
