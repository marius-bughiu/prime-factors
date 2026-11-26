import PrimeFactors.FareyWindow
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! The exact common additive error for weighted sums on an order-`K` Farey grid.
The optimization is over the continuous balanced ratio. It does not assume that
all ratios in the cover occur as ratios of prime factors of the given integer. -/

namespace PrimeFactors.WeightedRatioCover

noncomputable section

open Real

/-- For `y = √(q/p)` this is `(a*p+b*q−2√(abpq))/√(pq)`, with
`A=√a` and `B=√b`. -/
def error (A B y : ℝ) := (A-B*y)^2/y

/-- Location in square-root ratio coordinates where the neighboring errors agree. -/
def cut (A B C D : ℝ) := (A+C)/(B+D)

/-- Reciprocal of the maximum normalized error on the cell with endpoints `a/b,c/d`. -/
def cellScale (a b c d : ℕ) : ℝ :=
  (√(b*c : ℕ)+√(a*d : ℕ))^2 * (√(a:ℝ)+√(c:ℝ)) * (√(b:ℝ)+√(d:ℝ))

/-- The first Farey cell gives the sharp common scale for all cells. -/
def scale (K : ℕ) := cellScale 1 1 (K+1) K

private theorem compare_error {A B u v : ℝ} (hu : 0<u) (hv : 0<v) :
    error A B u ≤ error A B v ↔ 0 ≤ (v-u)*(B^2*u*v-A^2) := by
  rw [error,error,div_le_div_iff₀ hu hv]
  constructor <;> intro h <;> nlinarith only [h]

private theorem errors_at_cut {A B C D : ℝ} (hp : 0<A+C) (hq : 0<B+D) :
    error A B (cut A B C D) = (B*C-A*D)^2 / ((A+C)*(B+D)) ∧
    error C D (cut A B C D) = (B*C-A*D)^2 / ((A+C)*(B+D)) := by
  constructor <;> unfold error cut <;> field_simp <;> ring

/-- The smaller endpoint error never exceeds the common error at the cut. -/
theorem cell_peak {A B C D y : ℝ} (ha : 0<A) (hb : 0<B) (hc : 0<C) (hd : 0<D)
    (hy : 0<y) (lo : A≤B*y) (hi : D*y≤C) :
    min (error A B y) (error C D y) ≤ (B*C-A*D)^2 / ((A+C)*(B+D)) := by
  let z := cut A B C D
  have hz : 0<z := div_pos (add_pos ha hc) (add_pos hb hd)
  obtain ⟨left,right⟩ := errors_at_cut (add_pos ha hc) (add_pos hb hd)
  change error A B z = _ at left
  change error C D z = _ at right
  rcases le_total y z with h | h
  · apply (min_le_left ..).trans
    rw [←left,compare_error hy hz]
    apply mul_nonneg (sub_nonneg.mpr h); apply sub_nonneg.mpr
    have m := mul_le_mul lo (lo.trans (mul_le_mul_of_nonneg_left h hb.le)) ha.le (by positivity : 0≤B*y)
    nlinarith only [m]
  · apply (min_le_right ..).trans
    rw [←right,compare_error hy hz]
    apply mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h); apply sub_nonpos.mpr
    have m := mul_le_mul hi ((mul_le_mul_of_nonneg_left h hd.le).trans hi) (by positivity : 0≤D*z) hc.le
    nlinarith only [m]

private theorem sum_roots {i j k : ℕ} (s : k + 1 ≤ i + j) (m : k ≤ i * j) :
    1+√(k:ℝ) ≤ √(i:ℝ)+√(j:ℝ) := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  have hs : (k:ℝ)+1 ≤ i + j := by exact_mod_cast s
  have hm : √(k:ℝ)≤√(i:ℝ)*√(j:ℝ) := by
    rw [←Real.sqrt_mul (by positivity : 0≤(i:ℝ))]
    apply Real.sqrt_le_sqrt; exact_mod_cast m
  nlinarith only [hs, hm,Real.sq_sqrt (by positivity : 0≤(i:ℝ)),
    Real.sq_sqrt (by positivity : 0≤(j:ℝ)),Real.sq_sqrt (by positivity : 0≤(k:ℝ))]

/-- The endpoint pair `1/1,(K+1)/K` minimizes the scale over all terminal cells. -/
theorem scale_le_cell {p q K a b c d : ℕ} (B : FareyWindow.Bracket p q K a b c d)
    (stop : K<b+d) : scale K ≤ cellScale a b c d := by
  have bp:=B.bpos; have dp:=B.dpos; have det:=B.det; have ab:=B.leftLo; have cd:=B.rightLo
  have strict : d<c := by
    by_contra! con
    have h:=Nat.mul_le_mul_right d ab
    have eq : c=d := by omega
    rw [eq] at det; omega
  have prod : K≤b*d := by
    obtain ⟨u,hu⟩:=Nat.exists_eq_add_of_le (show 1≤b by omega)
    obtain ⟨v,hv⟩:=Nat.exists_eq_add_of_le (show 1≤d by omega)
    nlinarith only [Nat.zero_le (u*v),stop,congrArg₂ (·*·) hu hv,hu,hv]
  have ad : K≤a*d := prod.trans (Nat.mul_le_mul_right d ab)
  have ac : K+1≤a*c := by
    have := Nat.mul_lt_mul_of_pos_left strict bp
    have := Nat.mul_le_mul_right c ab
    omega
  have bc : K+1≤b*c := by omega
  have comp (x y : ℕ) (h : x≤y) : √(x:ℝ)≤√(y:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast h)
  unfold scale cellScale
  simp only [one_mul,Nat.cast_one,Real.sqrt_one]
  exact mul_le_mul_of_nonneg (mul_le_mul_of_nonneg
    ((sq_le_sq₀ (by positivity) (by positivity)).mpr (add_le_add (comp _ _ bc) (comp _ _ ad)))
    (sum_roots (by omega) ac) (by positivity) (by positivity))
    (sum_roots (by omega) prod) (by positivity) (by positivity)


private theorem root_mono {a b : ℕ} (h : a≤b) : √(a:ℝ) ≤ √(b:ℝ) :=
  Real.sqrt_le_sqrt (by exact_mod_cast h)

private theorem reciprocal_square {x y u v : ℝ} (h : x*y=1) (hy : 0<y)
    (hu : 0<u) (hv : 0<v) : x^2/(u*v) = 1/(y^2*u*v) := by
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  linear_combination (u*v)*(x*y+1)*h

private theorem peak_value {a b c d : ℕ} (ab : 0<a) (bb : 0<b) (cc : 0<c) (dd : 0<d)
    (det : b*c=a*d+1) :
    (√(b:ℝ)*√(c:ℝ)-√(a:ℝ)*√(d:ℝ))^2 /
    ((√(a:ℝ)+√(c:ℝ))*(√(b:ℝ)+√(d:ℝ))) = 1/cellScale a b c d := by
  have h (l r : ℕ) : √(l*r:ℕ)=√(l:ℝ)*√(r:ℝ) := by
    rw [Nat.cast_mul,Real.sqrt_mul (by positivity)]
  have cancel : (√(b*c:ℕ)-√(a*d:ℕ))*(√(b*c:ℕ)+√(a*d:ℕ))=1 := by
    have t := Real.sq_sqrt (by positivity : 0≤((b*c:ℕ):ℝ))
    have u := Real.sq_sqrt (by positivity : 0≤((a*d:ℕ):ℝ))
    have eq : ((b*c:ℕ):ℝ)= ↑(a*d:ℕ)+1 := by exact_mod_cast det
    nlinarith only [eq,t,u]
  rw [←h b c,←h a d]
  unfold cellScale
  exact reciprocal_square cancel (by positivity) (by positivity) (by positivity)

private theorem choose_endpoint {p q K a b c d : ℕ} (B : FareyWindow.Bracket p q K a b c d)
    (stop : K<b+d) {y : ℝ} (yp : 0<y)
    (l : √(a:ℝ)≤√(b:ℝ)*y) (r : √(d:ℝ)*y≤√(c:ℝ)) :
    ∃ a b : ℕ, 0<b ∧ b≤K ∧ b≤a ∧ a≤2*b ∧ a.Coprime b ∧
      error (√(a:ℝ)) (√(b:ℝ)) y ≤ 1/scale K := by
  have ab:=B.bpos.trans_le B.leftLo; have cd:=B.dpos.trans_le B.rightLo
  have bp:=B.bpos; have dp:=B.dpos
  have h := cell_peak (by positivity) (by positivity) (by positivity) (by positivity)
    yp l r
  rw [peak_value ab bp cd dp B.det] at h
  have pos : 0 < scale K := by unfold scale cellScale; positivity
  have bound := h.trans (one_div_le_one_div_of_le pos (scale_le_cell B stop))
  obtain ⟨cop,other⟩ := FareyWindow.bracket_primitive B
  rcases min_le_iff.mp bound with left | right
  · exact ⟨a,b,bp,B.bK,B.leftLo,B.leftHi,cop,left⟩
  · exact ⟨c,d,dp,B.dK,B.rightLo,B.rightHi,other,right⟩


/-- Every actual factor ratio admits one primitive weighted trace fitting the same
explicit additive error. The factors are used only to establish existence. -/
theorem uniform_cover {p q K : ℕ} (pp : 0<p) (ordered : p≤q) (balanced : q≤2*p)
    (hk : 0<K) : ∃ a b : ℕ, 0<b ∧ b≤K ∧ b≤a ∧ a≤2*b ∧ a.Coprime b ∧
      error (√(a:ℝ)) (√(b:ℝ)) (√(q:ℝ)/√(p:ℝ)) ≤ 1/scale K := by
  obtain ⟨a,b,c,d,B,stop⟩ := FareyWindow.exists_terminal ordered balanced hk
  have qp:=pp.trans_le ordered
  have sp : 0<√(p:ℝ) := by positivity
  have sq : 0<√(q:ℝ) := by positivity
  have br (A P B Q : ℕ) (le : A*P≤B*Q) : √(A:ℝ)*√(P:ℝ)≤√(B:ℝ)*√(Q:ℝ) := by
    rw [←Real.sqrt_mul (by positivity),←Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt; exact_mod_cast le
  have l : √(a:ℝ) ≤ √(b:ℝ)*(√(q:ℝ)/√(p:ℝ)) := by
    rw [←mul_div_assoc,le_div_iff₀ sp]; exact br _ _ _ _ B.lo
  have r : √(d:ℝ)*(√(q:ℝ)/√(p:ℝ)) ≤ √(c:ℝ) := by
    rw [←mul_div_assoc,div_le_iff₀ sp]; exact br _ _ _ _ B.hi
  exact choose_endpoint B stop (div_pos sq sp) l r

/-- The first cell's interior equal-error cut, in square-root ratio coordinates. -/
def firstCut (K : ℕ) : ℝ := (1+√((K+1:ℕ):ℝ))/(1+√(K:ℝ))

private theorem sqrt_step (k : ℕ) :
    √((k+1:ℕ):ℝ)-√(k:ℝ) = 1/(√((k+1:ℕ):ℝ)+√(k:ℝ)) := by
  apply (eq_div_iff (by positivity)).mpr
  have plus : ((k+1:ℕ):ℝ)=(k:ℝ)+1 := by norm_cast
  nlinarith only [plus,Real.sq_sqrt (by positivity : 0≤((k+1:ℕ):ℝ)),
    Real.sq_sqrt (by positivity : 0≤(k:ℝ))]

/-- Throughout the part of the first cell preceding the cut, no allowed
positive integer weights improve on the unweighted sum, even if nonprimitive
weights are admitted. -/
theorem first_optimal {K a b : ℕ} (bp : 0<b) (bK : b≤K) (ab : b≤a)
    {y : ℝ} (lo : 1≤y) (hi : y≤firstCut K) :
    error 1 1 y ≤ error (√(a:ℝ)) (√(b:ℝ)) y := by
  have hy : 0<y := zero_lt_one.trans_le lo
  unfold error
  apply div_le_div_of_nonneg_right _ hy.le
  have base : 1≤√(b:ℝ) := by simpa using (root_mono (show 1≤b from bp))
  rcases eq_or_lt_of_le ab with eq | lt
  · subst a
    have coef := mul_le_mul_of_nonneg_right base (sub_nonneg.mpr lo)
    have h : 0≤√(b:ℝ)*y-√(b:ℝ) := by nlinarith only [coef,lo]
    have sq := (sq_le_sq₀ (sub_nonneg.mpr lo) h).mpr (by nlinarith only [coef] : y-1≤√(b:ℝ)*y-√(b:ℝ))
    nlinarith only [sq]
  · have step : √((K+1:ℕ):ℝ)-√(K:ℝ) ≤ √((b+1:ℕ):ℝ)-√(b:ℝ) := by
      rw [sqrt_step,sqrt_step]
      apply one_div_le_one_div_of_le (by positivity)
      exact add_le_add (root_mono (by omega)) (root_mono bK)
    have cap := (le_div_iff₀ (show 0<1+√(K:ℝ) by positivity)).mp hi
    have m := mul_le_mul_of_nonneg_left (root_mono bK) (sub_nonneg.mpr lo)
    have aa := root_mono (show b+1≤a by omega)
    have gap : y-1≤√(a:ℝ)-√(b:ℝ)*y := by nlinarith only [step,cap,m,aa]
    have sq := (sq_le_sq₀ (sub_nonneg.mpr lo) ((sub_nonneg.mpr lo).trans gap)).mpr gap
    nlinarith only [sq]

/-- The universal error is attained at the first cut of the real relaxation. -/
theorem sharp_at_cut {K : ℕ} (hk : 0<K) :
    1≤firstCut K ∧ firstCut K≤√2 ∧ error 1 1 (firstCut K)=1/scale K ∧
    ∀ a b : ℕ, 0<b → b≤K → b≤a → 1/scale K ≤ error (√(a:ℝ)) (√(b:ℝ)) (firstCut K) := by
  have den : 0<1+√(K:ℝ) := by positivity
  have low : 1≤firstCut K := by
    apply (le_div_iff₀ den).mpr
    linarith only [root_mono (show K≤K+1 by omega)]
  have two : 1≤√(2:ℝ) := by norm_num
  have kg : √((K+1:ℕ):ℝ) ≤ √(2:ℝ)*√(K:ℝ) := by
    rw [←Real.sqrt_mul (by norm_num : 0≤(2:ℝ))]
    apply Real.sqrt_le_sqrt; exact_mod_cast (show K+1≤2*K by omega)
  have top : firstCut K≤√2 := (div_le_iff₀ den).mpr (by linarith only [two,kg])
  have eq := (errors_at_cut (show 0<(1:ℝ)+√((K+1:ℕ):ℝ) by positivity) den).1
  have pv := peak_value (a:=1) (b:=1) (c:=K+1) (d:=K) (by decide) (by decide)
    (by omega) hk (by simp)
  simp only [Nat.cast_one,Real.sqrt_one] at pv
  have win : error 1 1 (firstCut K)=1/scale K := eq.trans pv
  refine ⟨low,top,win,?_⟩
  intro a b bp bK ab; rw [←win]; exact first_optimal bp bK ab low le_rfl


private theorem unit_mono {u v : ℝ} (hu : 1≤u) (h : u≤v) :
    error 1 1 u ≤ error 1 1 v := by
  apply (compare_error (zero_lt_one.trans_le hu) (zero_lt_one.trans_le (hu.trans h))).mpr
  have prod := mul_le_mul hu (hu.trans h) zero_le_one (zero_le_one.trans hu)
  apply mul_nonneg (sub_nonneg.mpr h); nlinarith only [prod]

/-- Sharpness persists after truncating the range to `1 ≤ y ≤ Y`.
The witnessing `y` is public and can be irrational. -/
theorem clipped_sharp {K : ℕ} (hk : 0<K) {Y : ℝ} (hY : 1≤Y) :
    ∃ y : ℝ, 1≤y ∧ y≤√2 ∧ y≤Y ∧ ∀ a b : ℕ, 0<b → b≤K → b≤a →
      min (error 1 1 Y) (1/scale K) ≤ error (√(a:ℝ)) (√(b:ℝ)) y := by
  obtain ⟨low,top,eq,_⟩ := sharp_at_cut hk
  let y := min Y (firstCut K)
  have hy : 1≤y := le_min hY low
  refine ⟨y,hy,(min_le_right ..).trans top,min_le_left ..,?_⟩
  intro a b bp bK ab
  apply le_trans _ (first_optimal bp bK ab hy (min_le_right ..))
  rcases le_total Y (firstCut K) with h | h
  · rw [show y=Y from min_eq_left h]; exact min_le_left ..
  · rw [show y=firstCut K from min_eq_right h,eq]; exact min_le_right ..

private theorem trace_algebra (A B : ℝ) {P Q : ℝ} (hp : 0<P) (hq : 0<Q) :
    (P*Q)*error A B (Q/P) = A^2*P^2+B^2*Q^2-2*(A*B)*(P*Q) := by
  unfold error; field_simp; ring

/-- The normalized error is exactly the additive excess of the ordinary integer trace. -/
theorem trace_identity {p q : ℕ} (pp : 0<p) (qp : 0<q) (a b : ℕ) :
    √(p*q:ℕ) * error (√(a:ℝ)) (√(b:ℝ)) (√(q:ℝ)/√(p:ℝ)) =
    (a*p+b*q:ℕ) - 2*√((a*b)*(p*q):ℕ) := by
  push_cast
  simpa only [Real.sqrt_mul (show 0≤(a:ℝ) by positivity),
    Real.sqrt_mul (show 0≤(b:ℝ) by positivity),Real.sqrt_mul (show 0≤(p:ℝ) by positivity),
    Real.sqrt_mul (show 0≤(a:ℝ)*b by positivity),
    Real.sq_sqrt (show 0≤(a:ℝ) by positivity),Real.sq_sqrt (show 0≤(b:ℝ) by positivity),
    Real.sq_sqrt (show 0≤(p:ℝ) by positivity),Real.sq_sqrt (show 0≤(q:ℝ) by positivity),mul_assoc]
    using trace_algebra (√(a:ℝ)) (√(b:ℝ)) (P:=√(p:ℝ)) (Q:=√(q:ℝ))
      (by positivity) (by positivity)

/-- With a known factor upper limit `U`, a primitive direction achieves the smaller
of the sharp Farey budget and the public Fermat endpoint budget. -/
theorem product_cover {p q n K U : ℕ} (prod : p*q=n) (pp : 0<p) (ordered : p≤q)
    (balanced : q≤2*p) (cap : q≤U) (hk : 0<K) :
    ∃ a b : ℕ, 0<b ∧ b≤K ∧ b≤a ∧ a≤2*b ∧ a.Coprime b ∧
      (a*p+b*q:ℕ)-2*√((a*b)*n:ℕ) ≤ min (√(n:ℝ)/scale K) (((U:ℝ)-√(n:ℝ))^2/U) := by
  subst n
  have qp := pp.trans_le ordered
  rcases le_total (√(p*q:ℕ)/scale K) (((U:ℝ)-√(p*q:ℕ))^2/U) with left | right
  · obtain ⟨a,b,bp,bK,ab,ba,cop,h⟩ := uniform_cover pp ordered balanced hk
    refine ⟨a,b,bp,bK,ab,ba,cop,?_⟩
    rw [min_eq_left left,←trace_identity pp qp]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
  · refine ⟨1,1,by decide,hk,by decide,by decide,by decide,?_⟩
    rw [min_eq_right right]; simp only [one_mul,Nat.cast_add]
    have u : 0<(U:ℝ) := by exact_mod_cast (qp.trans_le cap)
    have sides := mul_nonneg (sub_nonneg.mpr (show (p:ℝ)≤U by exact_mod_cast ordered.trans cap))
      (sub_nonneg.mpr (show (q:ℝ)≤U by exact_mod_cast cap))
    apply (le_div_iff₀ u).mpr
    have sq := Real.sq_sqrt (show 0≤((p*q:ℕ):ℝ) by positivity)
    push_cast at sq ⊢; nlinarith only [sides,sq]


/-- Subdivide the fraction interval at its mediant using the real ratio.
`Bracket 0 0` carries just the public integer endpoint data. -/
private theorem real_bracket {K a b c d : ℕ} {r : ℝ} (B : FareyWindow.Bracket 0 0 K a b c d)
    (lo : (a:ℝ)≤b*r) (hi : (d:ℝ)*r≤c) : ∃ A B' C D : ℕ,
    FareyWindow.Bracket 0 0 K A B' C D ∧ K<B'+D ∧ (A:ℝ)≤B'*r ∧ (D:ℝ)*r≤C := by
  by_cases stop : K<b+d
  · exact ⟨a,b,c,d,B,stop,lo,hi⟩
  have cap : b+d≤K := by omega
  have den := add_pos B.bpos B.dpos
  have l := Nat.add_le_add B.leftLo B.rightLo
  have u : a+c≤2*(b+d) := by linarith only [B.leftHi,B.rightHi]
  by_cases left : ((b+d:ℕ):ℝ)*r≤((a+c:ℕ):ℝ)
  · exact real_bracket (a:=a) (b:=b) (c:=a+c) (d:=b+d)
      ⟨B.bpos,den,B.bK,cap,B.leftLo,B.leftHi,l,u,by nlinarith only [B.det],by simp,by simp⟩ lo left
  · exact real_bracket (a:=a+c) (b:=b+d) (c:=c) (d:=d)
      ⟨den,B.dpos,cap,B.dK,l,u,B.rightLo,B.rightHi,by nlinarith only [B.det],by simp,by simp⟩
      (le_of_not_ge left) hi
termination_by 2*K-(b+d)
decreasing_by all_goals have := B.bpos; have := B.dpos; have := B.bK; have := B.dK; omega

/-- The matching upper bound, for all real ratios in the truncated balanced interval. -/
theorem clipped_upper {K : ℕ} (hk : 0<K) {y Y : ℝ} (lo : 1≤y) (hi : y≤√2) (cap : y≤Y) :
    ∃ a b : ℕ, 0<b ∧ b≤K ∧ b≤a ∧ a≤2*b ∧ a.Coprime b ∧
      error (√(a:ℝ)) (√(b:ℝ)) y ≤ min (error 1 1 Y) (1/scale K) := by
  rcases le_total (error 1 1 Y) (1/scale K) with h | h
  · refine ⟨1,1,by decide,hk,by decide,by decide,by decide,?_⟩
    simpa only [Nat.cast_one,Real.sqrt_one,min_eq_left h] using unit_mono lo cap
  have y0 : 0<y := zero_lt_one.trans_le lo
  have bounds : 1≤y^2 ∧ y^2≤2 := ⟨by nlinarith only [(sq_le_sq₀ zero_le_one y0.le).mpr lo],
    by nlinarith only [(sq_le_sq₀ y0.le (Real.sqrt_nonneg _)).mpr hi,Real.sq_sqrt (by norm_num : 0≤(2:ℝ))]⟩
  obtain ⟨a,b,c,d,B,stop,l,r⟩ := real_bracket (K:=K) (a:=1) (b:=1) (c:=2) (d:=1) (r:=y^2)
    ⟨by decide,by decide,hk,hk,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
    (by simpa only [Nat.cast_one,one_mul] using bounds.1)
    (by simpa only [Nat.cast_one,Nat.cast_ofNat,one_mul] using bounds.2)
  have sqrtY (x : ℕ) : √(x*y^2 : ℝ)=√(x:ℝ)*y := by
    rw [Real.sqrt_mul (by positivity),Real.sqrt_sq y0.le]
  have l':=Real.sqrt_le_sqrt l; have r':=Real.sqrt_le_sqrt r
  rw [sqrtY] at l' r'
  rw [min_eq_right h]
  exact choose_endpoint B stop y0 l' r'

/-- The previous common Dirichlet budget at `K=32` was `√N/4356`. The new
worst-case budget is strictly smaller than `√N/5833`, a saving exceeding 25%. -/
theorem scale_32 : 5833 < scale 32 := by
  have r32 : (5656:ℝ)/1000 < √(32:ℝ) := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by norm_num : 0≤(32:ℝ))]; norm_num
  have r33 : (5744:ℝ)/1000 < √(33:ℝ) := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by norm_num : 0≤(33:ℝ))]; norm_num
  unfold scale cellScale
  norm_num only [one_mul,Nat.cast_one,Nat.cast_ofNat,Real.sqrt_one, Nat.reduceAdd]
  have m := mul_le_mul_of_nonneg (mul_le_mul_of_nonneg
    ((sq_le_sq₀ (by norm_num) (by positivity)).mpr (add_le_add r33.le r32.le))
    (add_le_add_left r33.le 1) (by norm_num) (by positivity))
    (add_le_add_left r32.le 1) (by norm_num) (by positivity)
  exact lt_of_lt_of_le (by norm_num) m

end

end PrimeFactors.WeightedRatioCover
