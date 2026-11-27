import PrimeFactors.MixedUnityCofactors
import Mathlib.Tactic

/-! Multiplicity of the real smaller-divisor windows of rectangular
difference-of-squares rows. The location need not divide the input. -/
namespace PrimeFactors.WeightWindowOverlap

/-- The two nonnegative scaled weights have matching parity in both
cofactor cases: both are odd, or both are multiplied by two. -/
structure Weight where
  a : ℤ
  b : ℤ
  parity : Even (a-b)

def det (u v : Weight) : ℤ := u.a*v.b-v.a*u.b

noncomputable def gap (p q : ℝ) (u : Weight) : ℝ := (u.a*p-u.b*q)/2
noncomputable def mid (p q : ℝ) (u : Weight) : ℝ := (u.a*p+u.b*q)/2

def Fits (p q H B : ℝ) (u : Weight) : Prop :=
  |gap p q u|≤H ∧ 0≤mid p q u ∧ mid p q u≤B

theorem det_even (u v : Weight) : 2∣det u v := by
  obtain ⟨i,hi⟩ := u.parity
  obtain ⟨j,hj⟩ := v.parity
  refine ⟨i*v.b-j*u.b,?_⟩
  unfold det
  linear_combination v.b*hi-u.b*hj

theorem area (p q : ℝ) (u v : Weight) :
    2*(gap p q u*mid p q v-gap p q v*mid p q u) = (det u v : ℝ)*(p*q) := by
  simp only [gap,mid,det,Int.cast_sub,Int.cast_mul]
  ring

/-- Any two distinct rays in the scaled weight lattice enclose determinant
of magnitude at least N in the (signed gap, midpoint) plane. -/
theorem separation {p q : ℝ} (n : 0<p*q) {u v : Weight} (diff : det u v≠0) :
    p*q ≤ |gap p q u*mid p q v-gap p q v*mid p q u| := by
  obtain ⟨z,h⟩ := det_even u v
  have nz : z≠0 := fun e => diff (by rw [h,e,mul_zero])
  have norm : (1:ℝ)≤|(z:ℝ)| := by
    rw [←Int.cast_abs]
    exact_mod_cast (show (1:ℤ)≤|z| by have := abs_pos.mpr nz; omega)
  have a := area p q u v
  rw [h,Int.cast_mul,Int.cast_ofNat] at a
  have val : gap p q u*mid p q v-gap p q v*mid p q u=(z:ℝ)*(p*q) := by linarith
  rw [val,abs_mul,abs_of_pos n]
  simpa using mul_le_mul_of_nonneg_right norm n.le

private theorem side_bound {x z y w H B : ℝ} (ax : |x|≤H) (az : |z|≤H)
    (y0 : 0≤y) (yb : y≤B) (w0 : 0≤w) (wb : w≤B)
    (side : (0≤x ∧ 0≤z) ∨ (x≤0 ∧ z≤0)) : |x*w-z*y|≤H*B := by
  have hx := abs_le.mp ax
  have hz := abs_le.mp az
  rcases side with ⟨xp,zp⟩|⟨xn,zn⟩
  · have xw := mul_le_mul hx.2 wb w0 (xp.trans hx.2)
    have zy := mul_le_mul hz.2 yb y0 (zp.trans hz.2)
    exact abs_le.mpr ⟨by linarith [mul_nonneg xp w0],by linarith [mul_nonneg zp y0]⟩
  · have xw := mul_le_mul (show -x≤H by linarith) wb w0 ((abs_nonneg x).trans ax)
    have zy := mul_le_mul (show -z≤H by linarith) yb y0 ((abs_nonneg z).trans az)
    rw [neg_mul] at xw zy
    exact abs_le.mpr ⟨by linarith [mul_nonpos_of_nonpos_of_nonneg zn y0],
      by linarith [mul_nonpos_of_nonpos_of_nonneg xn w0]⟩

/-- Two different weight rays cannot cover the same candidate on the
same side of the exact ratio. This holds throughout the real interval. -/
theorem same_side {p q H B : ℝ} (small : H*B<p*q) (n : 0<p*q)
    {u v : Weight} (hu : Fits p q H B u) (hv : Fits p q H B v)
    (side : (0≤gap p q u ∧ 0≤gap p q v) ∨ (gap p q u≤0 ∧ gap p q v≤0)) :
    det u v=0 := by
  by_contra diff
  exact (not_le_of_gt small) ((separation n diff).trans
    (side_bound hu.1 hv.1 hu.2.1 hu.2.2 hv.2.1 hv.2.2 side))

/-- At most two distinct weight ratios can cover one location. -/
theorem no_three {p q H B : ℝ} (small : H*B<p*q) (n : 0<p*q)
    {u v w : Weight} (hu : Fits p q H B u) (hv : Fits p q H B v) (hw : Fits p q H B w) :
    det u v=0 ∨ det u w=0 ∨ det v w=0 := by
  rcases le_total 0 (gap p q u) with up|un <;> rcases le_total 0 (gap p q v) with vp|vn
  · exact Or.inl (same_side small n hu hv (Or.inl ⟨up,vp⟩))
  · rcases le_total 0 (gap p q w) with wp|wn
    · exact Or.inr (Or.inl (same_side small n hu hw (Or.inl ⟨up,wp⟩)))
    · exact Or.inr (Or.inr (same_side small n hv hw (Or.inr ⟨vn,wn⟩)))
  · rcases le_total 0 (gap p q w) with wp|wn
    · exact Or.inr (Or.inr (same_side small n hv hw (Or.inl ⟨vp,wp⟩)))
    · exact Or.inr (Or.inl (same_side small n hu hw (Or.inr ⟨un,wn⟩)))
  · exact Or.inl (same_side small n hu hv (Or.inr ⟨un,vn⟩))

/-- A finite family of distinct ratios covering the same location has
cardinality at most two. -/
theorem geometric_count {p q H B : ℝ} (small : H*B<p*q) (n : 0<p*q) (s : Finset Weight)
    (fit : ∀ u∈s, Fits p q H B u)
    (distinct : ∀ u∈s, ∀ v∈s, u≠v → det u v≠0) : s.card≤2 := by
  by_contra! bad
  obtain ⟨u,v,w,hu,hv,hw,uv,uw,vw⟩ := Finset.two_lt_card_iff.mp bad
  rcases no_three small n (fit u hu) (fit v hv) (fit w hw) with a|b|c
  · exact distinct u hu v hv uv a
  · exact distinct u hu w hw uw b
  · exact distinct v hv w hw vw c

/-- Count one operation per location/window incidence. On any finite
population the total before merging is at most twice the number of
locations appearing in the union. -/
theorem aggregate_savings {ι : Type*} (locations : Finset ι) (windows : ι → Finset Weight)
    (P Q : ι → ℝ) (H B : ℝ) (small : ∀ i∈locations, H*B<P i*Q i)
    (n : ∀ i∈locations, 0<P i*Q i) (fit : ∀ i∈locations, ∀ u∈windows i, Fits (P i) (Q i) H B u)
    (distinct : ∀ i∈locations, ∀ u∈windows i, ∀ v∈windows i, u≠v → det u v≠0) :
    ∑ i ∈ locations, (windows i).card ≤ 2*(locations.filter fun i => 0<(windows i).card).card := by
  calc
    _ ≤ ∑ i ∈ locations, if 0<(windows i).card then 2 else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs with h
      · exact geometric_count (small i hi) (n i hi) (windows i) (fit i hi) (distinct i hi)
      · omega
    _ = _ := by rw [←Finset.sum_filter]; simp [Nat.mul_comm]

/-- A nonparallel pair of doubly scaled weight vectors has determinant a
nonzero multiple of four. Their rectangles are disjoint on either side. -/
theorem no_double_scale {p q H B : ℝ} (small : H*B<p*q) (n : 0<p*q)
    {u v : Weight} (hu : Fits p q H B u) (hv : Fits p q H B v)
    (four : 4∣det u v) : det u v=0 := by
  by_contra nz
  obtain ⟨z,hz⟩ := four
  have zn : z≠0 := fun e => nz (by rw [hz,e,mul_zero])
  have norm : (1:ℝ)≤|(z:ℝ)| := by
    rw [←Int.cast_abs]
    exact_mod_cast (show (1:ℤ)≤|z| by have := abs_pos.mpr zn; omega)
  have a := area p q u v
  rw [hz,Int.cast_mul,Int.cast_ofNat] at a
  have val : gap p q u*mid p q v-gap p q v*mid p q u=(2*(z:ℝ))*(p*q) := by linarith
  have bound := abs_sub (gap p q u*mid p q v) (gap p q v*mid p q u)
  rw [val,abs_mul,abs_mul,abs_of_pos n,abs_of_pos (by norm_num : (0:ℝ)<2),
    abs_mul,abs_mul,abs_of_nonneg hv.2.1,abs_of_nonneg hu.2.1] at bound
  have e := mul_le_mul hu.1 hv.2.2 hv.2.1 ((abs_nonneg _).trans hu.1)
  have f := mul_le_mul hv.1 hu.2.2 hu.2.1 ((abs_nonneg _).trans hv.1)
  have g := mul_le_mul_of_nonneg_right norm n.le
  nlinarith only [bound,e,f,g,small]

/-- If the smaller proposed divisor exceeds H, a smaller weight on it
cannot work. The two scaled weights differ by at least two. -/
theorem reverse_impossible {p q H a b : ℝ} (hp : H<p) (pq : p≤q) (pp : 0≤p)
    (bp : 0≤b) (sep : a+2≤b) : 2*H<b*q-a*p := by
  have first := mul_le_mul_of_nonneg_right sep pp
  have second := mul_le_mul_of_nonneg_left pq bp
  nlinarith only [hp,first,second]

/-- A primitive positive row of the D=1 scan. -/
structure Row (N H B k : ℕ) where
  x : ℕ
  y : ℕ
  kpos : 0<k
  ypos : 0<y
  xh : x≤H
  yb : y≤B
  prim : x.Coprime y
  eqn : y^2=x^2+k*N

private def Side (p q x y : ℕ) : Prop :=
  ((p : ℤ)∣(y : ℤ)-x) ∧ ((q : ℤ)∣(y : ℤ)+x)

private theorem assigned {p q H B k : ℕ} (pp : p.Prime) (pq : q.Prime) (ne : p≠q)
    (po : Odd p) (qo : Odd q) (upper : B+H<p*q) (u : Row (p*q) H B k) :
    Side p q u.x u.y ∨ Side q p u.x u.y := by
  have yx : u.x≤u.y := by
    by_contra! bad
    have gt := Nat.pow_lt_pow_left bad (by decide : 2≠0)
    have := u.eqn
    omega
  obtain ⟨a,b,t,_,_,place,_,_⟩ := MixedUnityCofactors.decompose pp pq ne po qo u.kpos
    ((Nat.add_le_add u.yb u.xh).trans_lt upper) u.prim u.eqn
  have left (v w : ℕ) (e : t*(v*w)=u.y-u.x) : (v:ℤ)∣(u.y:ℤ)-u.x := by
    rw [←Nat.cast_sub yx,←e]
    exact_mod_cast (show v∣t*(v*w) from ⟨t*w,by ring⟩)
  have right (v w : ℕ) (e : t*(v*w)=u.y+u.x) : (v:ℤ)∣(u.y:ℤ)+u.x := by
    rw [←Nat.cast_add,←e]
    exact_mod_cast (show v∣t*(v*w) from ⟨t*w,by ring⟩)
  rcases place with ⟨a,b⟩|⟨a,b⟩
  · exact Or.inl ⟨left _ _ a,right _ _ b⟩
  · exact Or.inr ⟨left _ _ a,right _ _ b⟩

private theorem same_assignment {p q N H B k l : ℕ} (cp : p.Coprime q) (product : N=p*q)
    (np : 0<N) (small : H*B<N) (u : Row N H B k) (v : Row N H B l)
    (su : Side p q u.x u.y) (sv : Side p q v.x v.y) :
    u.x=v.x ∧ u.y=v.y ∧ k=l := by
  let z : ℤ := (u.x:ℤ)*v.y-(v.x:ℤ)*u.y
  obtain ⟨a,ha⟩ := su.1
  obtain ⟨b,hb⟩ := sv.1
  obtain ⟨c,hc⟩ := su.2
  obtain ⟨d,hd⟩ := sv.2
  have pd : (p:ℤ)∣z := ⟨(u.y:ℤ)*b-(v.y:ℤ)*a,by dsimp [z]; linear_combination (u.y:ℤ)*hb-(v.y:ℤ)*ha⟩
  have qd : (q:ℤ)∣z := ⟨(v.y:ℤ)*c-(u.y:ℤ)*d,by dsimp [z]; linear_combination (v.y:ℤ)*hc-(u.y:ℤ)*hd⟩
  have nz : (N:ℤ)∣z := by
    rw [product,Nat.cast_mul]
    have cp' : IsCoprime (p:ℤ) (q:ℤ) := Int.isCoprime_iff_nat_coprime.mpr cp
    exact cp'.mul_dvd pd qd
  have L : (u.x:ℤ)*v.y<N := by exact_mod_cast (Nat.mul_le_mul u.xh v.yb).trans_lt small
  have R : (v.x:ℤ)*u.y<N := by exact_mod_cast (Nat.mul_le_mul v.xh u.yb).trans_lt small
  have zero : z=0 := Int.eq_zero_of_abs_lt_dvd nz (abs_lt.mpr ⟨by
    dsimp [z]; linarith [show (0:ℤ)≤(u.x:ℤ)*v.y by positivity],by
    dsimp [z]; linarith [show (0:ℤ)≤(v.x:ℤ)*u.y by positivity]⟩)
  have e : u.x*v.y=v.x*u.y := by exact_mod_cast sub_eq_zero.mp zero
  have xy := u.prim.symm.dvd_of_dvd_mul_left (show u.y∣u.x*v.y from ⟨v.x,e.trans (Nat.mul_comm ..)⟩)
  have yx := v.prim.symm.dvd_of_dvd_mul_left (show v.y∣v.x*u.y from ⟨u.x,e.symm.trans (Nat.mul_comm ..)⟩)
  have y := Nat.dvd_antisymm xy yx
  have x := Nat.mul_right_cancel v.ypos (y ▸ e : u.x*v.y=v.x*v.y)
  have e' := u.eqn
  rw [x,y] at e'
  exact ⟨x,y,Nat.mul_right_cancel np (by have := v.eqn; omega)⟩

/-- For a fixed product at most two different positive primitive multipliers
can work. Facing the same prime at y−x even forces the same two coordinates. -/
theorem no_three_rows {p q H B k l j : ℕ} (pp : p.Prime) (pq : q.Prime) (ne : p≠q)
    (po : Odd p) (qo : Odd q) (upper : B+H<p*q) (small : H*B<p*q)
    (u : Row (p*q) H B k) (v : Row (p*q) H B l) (w : Row (p*q) H B j) :
    k=l ∨ k=j ∨ l=j := by
  have cp := (Nat.coprime_primes pp pq).mpr ne
  have pos := Nat.mul_pos pp.pos pq.pos
  have A := assigned pp pq ne po qo upper u
  have C := assigned pp pq ne po qo upper v
  have E := assigned pp pq ne po qo upper w
  rcases A with a|a <;> rcases C with c|c
  · exact Or.inl (same_assignment cp rfl pos small u v a c).2.2
  · rcases E with e|e
    · exact Or.inr (Or.inl (same_assignment cp rfl pos small u w a e).2.2)
    · exact Or.inr (Or.inr (same_assignment cp.symm (Nat.mul_comm ..) pos small v w c e).2.2)
  · rcases E with e|e
    · exact Or.inr (Or.inr (same_assignment cp rfl pos small v w c e).2.2)
    · exact Or.inr (Or.inl (same_assignment cp.symm (Nat.mul_comm ..) pos small u w a e).2.2)
  · exact Or.inl (same_assignment cp.symm (Nat.mul_comm ..) pos small u v a c).2.2

theorem primitive_count {p q H B : ℕ} (pp : p.Prime) (pq : q.Prime) (ne : p≠q)
    (po : Odd p) (qo : Odd q) (upper : B+H<p*q) (small : H*B<p*q) (s : Finset ℕ)
    (wins : ∀ k∈s, Nonempty (Row (p*q) H B k)) : s.card≤2 := by
  by_contra! bad
  obtain ⟨k,l,j,hk,hl,hj,kl,kj,lj⟩ := Finset.two_lt_card_iff.mp bad
  obtain ⟨u⟩ := wins k hk
  obtain ⟨v⟩ := wins l hl
  obtain ⟨w⟩ := wins j hj
  exact (no_three_rows pp pq ne po qo upper small u v w).elim kl (fun h => h.elim kj lj)

end PrimeFactors.WeightWindowOverlap
