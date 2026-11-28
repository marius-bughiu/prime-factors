import PrimeFactors.FloorSquareShiftPopulation
import PrimeFactors.SquareScaleHarmonicBound

/-! Every center from W below the floor root through the floor root and every
positive shift are granted. The shifted square equation is over the integers. -/

namespace PrimeFactors.FloorShiftCenterWindow

open Finset
open private PrimeFactors.FloorSquareShift.floor_bounds from PrimeFactors.FloorSquareShift

def window (n W s : ℕ) : Prop := s≤n.sqrt ∧ n.sqrt≤s+W

def shifted (p q s h : ℕ) : Prop :=
  0<h ∧ ((p:ℤ)-h)*((q:ℤ)-h)=((s:ℤ)-h)^2

theorem residual_bound {p q s W H : ℕ} (ord : p<q) (top : q≤H) (win : window (p*q) W s) :
    p*q-s^2 ≤ 2*(W+1)*H := by
  let r := (p*q).sqrt
  have f := PrimeFactors.FloorSquareShift.floor_bounds ord
  have rh : r≤H := f.2.1.trans top
  have sr : s≤r := win.1
  have rs : r≤s+W := win.2
  have pq := Nat.lt_succ_sqrt' (p*q)
  change p*q<(r+1)^2 at pq
  have small : r-s≤W := by omega
  have large : r+s≤2*H := by omega
  have prod := Nat.mul_le_mul small large
  have pqBound : p*q≤r^2+2*r := by nlinarith only [pq]
  have add : s+(r-s)=r := by omega
  have expan : s^2+(r-s)*(r+s)=r^2 := by
    calc s^2+(r-s)*(r+s)=s^2+(r-s)*((s+(r-s))+s) := by rw [add]
         _ = (s+(r-s))^2 := by ring
         _ = _ := by rw [add]
  rw [show 2*(W+1)*H=W*(2*H)+2*H by ring]
  omega

/-- The positive shift cannot exceed the smaller factor, including when the
center lies below the shift. -/
theorem shift_le {p q s h W : ℕ} (ord : p<q) (win : window (p*q) W s)
    (ht : shifted p q s h) : h≤p := by
  obtain ⟨_,eqn⟩ := ht
  have f := (PrimeFactors.FloorSquareShift.floor_bounds ord).2.2
  have ss := win.1
  have pos : 0<(p:ℤ)+q-2*s := by omega
  have prod : 0≤((p:ℤ)-h)*((p:ℤ)+q-2*s) := by nlinarith only [eqn,sq_nonneg ((p:ℤ)-s)]
  have := (mul_nonneg_iff_of_pos_right pos).mp prod
  omega

theorem shifted_iff {p q s h W : ℕ} (ord : p<q) (win : window (p*q) W s) (positive : 0<h) :
    shifted p q s h ↔ p*q-s^2=h*(p+q-2*s) := by
  have sr := win.1
  have f := (PrimeFactors.FloorSquareShift.floor_bounds ord).2.2
  have sh : 2*s≤p+q := by omega
  have sq : s^2≤p*q := (Nat.pow_le_pow_left sr 2).trans (Nat.sqrt_le' _)
  simp only [shifted,positive,true_and]
  zify [sh,sq]
  constructor <;> intro eqn <;> nlinarith only [eqn]

/-- Each winning pair belongs to the same coordinate cover regardless of the chosen center. The smaller square index is allowed to be zero when h=p. -/
theorem coordinates {p q s h W H : ℕ} (ord : p<q) (top : q≤H) (win : window (p*q) W s)
    (ht : shifted p q s h) :
    ∃ u x k : ℕ, 0<u ∧ 0<k ∧ p=h+u*x^2 ∧ q=h+u*(x+k)^2 ∧
      h*u*k^2≤2*(W+1)*H := by
  have hp := ht.1
  have le := shift_le ord win ht
  have rem := (shifted_iff ord win hp).mp ht
  have R := residual_bound ord top win
  obtain ⟨_,eqn⟩ := ht
  by_cases he : h=p
  · subst h
    have seq : s=p := by
      simp only [sub_self,zero_mul] at eqn
      have : (s:ℤ)-p=0 := by nlinarith only [eqn,sq_nonneg ((s:ℤ)-p)]
      omega
    subst s
    refine ⟨q-p,0,1,Nat.sub_pos_of_lt ord,by decide,by simp,by simp; omega,?_⟩
    have ident : p+q-2*p=q-p := by omega
    rw [ident] at rem
    simpa only [one_pow,mul_one,←rem] using R
  · have proper : h<p := by omega
    have hq : h≤q := le.trans ord.le
    let y := ((s:ℤ)-h).natAbs
    have product : (p-h)*(q-h)=1*y^2 := by
      simp only [one_mul]
      apply Int.ofNat_inj.mp
      push_cast [Nat.cast_sub le,Nat.cast_sub hq]
      simpa only [y,Int.natCast_natAbs,sq_abs] using eqn
    obtain ⟨u,m,n,x,z,up,mp,np,xp,zp,A,C,_,mn,_,_⟩ :=
      SquareScalePairCoordinates.coordinates (L:=1) (t:=1) (y:=y)
        (Nat.sub_pos_of_lt proper) (Nat.sub_pos_of_lt (proper.trans ord)) zero_lt_one le_rfl product
    have mn1 := Nat.eq_one_of_dvd_one mn
    obtain rfl : m=1 := Nat.eq_one_of_dvd_one (mn1 ▸ dvd_mul_right m n)
    simp only [one_mul] at mn1
    subst n
    simp only [mul_one] at A C
    have P : p=h+u*x^2 := by omega
    have Q : q=h+u*z^2 := by omega
    have xz : x<z := by
      by_contra! opp
      have mono := Nat.mul_le_mul_left u (Nat.pow_le_pow_left opp 2)
      omega
    let k := z-x
    have K : z=x+k := by dsimp [k]; omega
    rw [K] at Q
    have sq : ((s:ℤ)-h)^2 = ((u:ℤ)*x*(x+k))^2 := by
      rw [←eqn,P,Q]
      push_cast
      ring
    have sle := le_of_sq_le_sq sq.le (by positivity : (0:ℤ)≤u*x*(x+k))
    have upper : s≤h+u*x*(x+k) := by
      apply Int.ofNat_le.mp
      push_cast
      linarith only [sle]
    have term : u*k^2+2*s ≤ p+q := calc
      _ ≤ u*k^2+2*(h+u*x*(x+k)) := Nat.add_le_add_left (Nat.mul_le_mul_left 2 upper) _
      _ = _ := by rw [P,Q];ring
    have j : u*k^2≤p+q-2*s := by omega
    refine ⟨u,x,k,up,Nat.sub_pos_of_lt xz,P,Q,?_⟩
    rw [mul_assoc]
    exact (Nat.mul_le_mul_left h j).trans (rem ▸ R)

private noncomputable def row (H A u h : ℕ) :=
  ((Icc 1 (H/u).sqrt) ×ˢ (Icc 1 (A/(u*h)).sqrt)).image fun a =>
    (h+u*(a.1-1)^2,h+u*(a.1-1+a.2)^2)

private noncomputable def cover (H A : ℕ) :=
  (Icc 1 H).biUnion fun u => (Icc 1 H).biUnion fun h => row H A u h

private theorem mem_cover {p q u x k h H A : ℕ} (up : 0<u) (kp : 0<k) (hp : 0<h)
    (high : q≤H) (P : p=h+u*x^2) (Q : q=h+u*(x+k)^2) (size : h*u*k^2≤A) :
    (p,q)∈cover H A := by
  have small : u*(x+k)^2≤H := by omega
  have zpos : 0<x+k := by omega
  have usmall := (Nat.le_mul_of_pos_right u (pow_pos zpos 2)).trans small
  have hsmall : h≤H := by omega
  have a : x+1≤(H/u).sqrt := by
    apply le_trans (show x+1≤x+k by omega)
    exact Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le up).mpr (by rwa [mul_comm]))
  have b : k≤(A/(u*h)).sqrt := Nat.le_sqrt'.mpr
    ((Nat.le_div_iff_mul_le (Nat.mul_pos up hp)).mpr (by
      calc k^2*(u*h)=h*u*k^2 := by ring
           _ ≤ A := size))
  exact mem_biUnion.mpr ⟨u,mem_Icc.mpr ⟨up,usmall⟩,
    mem_biUnion.mpr ⟨h,mem_Icc.mpr ⟨hp,hsmall⟩,mem_image.mpr
      ⟨(x+1,k),mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,a⟩,mem_Icc.mpr ⟨kp,b⟩⟩,
        by simpa only [Nat.add_sub_cancel] using Prod.ext P.symm Q.symm⟩⟩⟩

private theorem row_count (H A u h : ℕ) :
    ((row H A u h).card:ℝ) ≤ (Real.sqrt H*Real.sqrt A)*(1/(u:ℝ))*(1/Real.sqrt h) := by
  have cnt : (row H A u h).card≤(H/u).sqrt*(A/(u*h)).sqrt :=
    card_image_le.trans_eq (by simp only [Nat.card_Icc,card_product,Nat.add_sub_cancel])
  have cntR := (Nat.cast_le (α:=ℝ)).mpr cnt
  rw [Nat.cast_mul] at cntR
  have root (n d : ℕ) : ((n/d).sqrt:ℝ)≤Real.sqrt n/Real.sqrt d := by
    apply Real.nat_sqrt_le_real_sqrt.trans
    rw [←Real.sqrt_div (Nat.cast_nonneg n)]
    exact Real.sqrt_le_sqrt Nat.cast_div_le
  apply cntR.trans ((mul_le_mul (root H u) (root A (u*h)) (by positivity) (by positivity)).trans_eq ?_)
  rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg u)]
  calc _ = (Real.sqrt H*Real.sqrt A)*(1/(Real.sqrt u*Real.sqrt u))*(1/Real.sqrt h) := by
             simp only [div_eq_mul_inv,mul_inv_rev]
             ring
       _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg u)]

open private PrimeFactors.SquareScaleHarmonicBound.sqrt_sum
  PrimeFactors.SquareScaleHarmonicBound.reciprocal
  PrimeFactors.SquareScaleHarmonicBound.power_harmonic from PrimeFactors.SquareScaleHarmonicBound

private theorem cover_count (H A : ℕ) :
    ((cover H A).card:ℝ) ≤ 2*H*Real.sqrt A*(harmonic H:ℝ) := by
  have cnt : (cover H A).card≤∑u∈Icc 1 H, ∑h∈Icc 1 H, (row H A u h).card :=
    card_biUnion_le.trans (sum_le_sum fun _ _ => card_biUnion_le)
  have cntR := (Nat.cast_le (α:=ℝ)).mpr cnt
  push_cast at cntR
  apply cntR.trans
  let C := Real.sqrt H*Real.sqrt A
  have hn : 0≤(harmonic H:ℝ) := by rw [←PrimeFactors.SquareScaleHarmonicBound.reciprocal]; positivity
  calc
    _ ≤ ∑u∈Icc 1 H, ∑h∈Icc 1 H, C*(1/(u:ℝ))*(1/Real.sqrt h) :=
      sum_le_sum fun u _ => sum_le_sum fun h _ => row_count H A u h
    _ = C*(harmonic H:ℝ)*(∑h∈Icc 1 H,1/Real.sqrt h) := by
      simp_rw [←mul_sum]
      rw [←sum_mul,←mul_sum,PrimeFactors.SquareScaleHarmonicBound.reciprocal]
    _ ≤ C*(harmonic H:ℝ)*(2*Real.sqrt H) :=
      mul_le_mul_of_nonneg_left (PrimeFactors.SquareScaleHarmonicBound.sqrt_sum H)
        (mul_nonneg (by dsimp [C]; positivity) hn)
    _ = _ := by
      dsimp [C]
      calc _ = 2*(Real.sqrt H)^2*Real.sqrt A*(harmonic H:ℝ) := by ring
           _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg H)]

/-- A single common cover for all centers and all positive shifts. -/
theorem finite_count (P : Finset (ℕ×ℕ)) {H W : ℕ}
    (valid : ∀ v∈P, v.1<v.2 ∧ v.2≤H ∧ ∃ s h, window (v.1*v.2) W s ∧ shifted v.1 v.2 s h) :
    (P.card:ℝ) ≤ 2*H*Real.sqrt ((2*(W+1)*H:ℕ):ℝ)*(harmonic H:ℝ) := by
  have sub : P⊆cover H (2*(W+1)*H) := by
    rintro ⟨p,q⟩ hm
    obtain ⟨ord,hi,s,h,hw,hit⟩ := valid _ hm
    obtain ⟨u,x,k,up,kp,P,Q,size⟩ := coordinates ord hi hw hit
    exact mem_cover up kp hit.1 hi P Q size
  exact ((Nat.cast_le (α:=ℝ)).mpr (card_le_card sub)).trans (cover_count _ _)

private noncomputable def gapRow (H A u k : ℕ) :=
  ((Icc 1 (H/u).sqrt) ×ˢ (Icc 1 (A/(u*k^2)))).image fun a =>
    (a.2+u*(a.1-1)^2,a.2+u*(a.1-1+k)^2)

private noncomputable def gapCover (H A : ℕ) :=
  (Icc 1 H).biUnion fun u => (Icc 1 H).biUnion fun k => gapRow H A u k

private theorem mem_gap_cover {p q u x k h H A : ℕ} (up : 0<u) (kp : 0<k) (hp : 0<h)
    (high : q≤H) (P : p=h+u*x^2) (Q : q=h+u*(x+k)^2) (size : h*u*k^2≤A) :
    (p,q)∈gapCover H A := by
  have small : u*(x+k)^2≤H := by omega
  have zpos : 0<x+k := by omega
  have usmall := (Nat.le_mul_of_pos_right u (pow_pos zpos 2)).trans small
  have ksmall : k≤H := calc
    k ≤ x+k := Nat.le_add_left _ _
    _ ≤ (x+k)^2 := Nat.le_self_pow (by decide) _
    _ ≤ u*(x+k)^2 := Nat.le_mul_of_pos_left _ up
    _ ≤ H := small
  have a : x+1≤(H/u).sqrt := by
    apply le_trans (show x+1≤x+k by omega)
    exact Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le up).mpr (by rwa [mul_comm]))
  have b : h≤A/(u*k^2) := (Nat.le_div_iff_mul_le (Nat.mul_pos up (pow_pos kp 2))).mpr
    (by rwa [←mul_assoc])
  exact mem_biUnion.mpr ⟨u,mem_Icc.mpr ⟨up,usmall⟩,
    mem_biUnion.mpr ⟨k,mem_Icc.mpr ⟨kp,ksmall⟩,mem_image.mpr ⟨(x+1,h),
      mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,a⟩,mem_Icc.mpr ⟨hp,b⟩⟩,
      by simpa only [Nat.add_sub_cancel] using Prod.ext P.symm Q.symm⟩⟩⟩

private theorem gap_row_count (H A u k : ℕ) :
    ((gapRow H A u k).card:ℝ)≤A*Real.sqrt H*(1/((u:ℝ)*Real.sqrt u))*(1/(k:ℝ)^2) := by
  have cnt : (gapRow H A u k).card ≤ (H/u).sqrt*(A/(u*k^2)) :=
    card_image_le.trans_eq (by simp only [card_product,Nat.card_Icc,Nat.add_sub_cancel])
  have cntR := (Nat.cast_le (α:=ℝ)).mpr cnt
  rw [Nat.cast_mul] at cntR
  have hr := (Real.nat_sqrt_le_real_sqrt (a:=H/u)).trans
    (Real.sqrt_le_sqrt (Nat.cast_div_le (α:=ℝ) (m:=H) (n:=u)))
  rw [Real.sqrt_div (Nat.cast_nonneg H)] at hr
  have hq : ((A/(u*k^2):ℕ):ℝ)≤(A:ℝ)/((u:ℝ)*k^2) := by
    calc _ ≤ (A:ℝ)/((u*k^2:ℕ):ℝ) := Nat.cast_div_le
         _ = _ := by push_cast; ring
  apply cntR.trans ((mul_le_mul hr hq (by positivity) (by positivity)).trans_eq ?_)
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

open private PrimeFactors.FloorSquareShiftPopulation.square_sum_aux
  PrimeFactors.FloorSquareShiftPopulation.root_sum_aux from PrimeFactors.FloorSquareShiftPopulation

private theorem gap_cover_count (H A : ℕ) (hp : 0<H) :
    ((gapCover H A).card:ℝ)≤6*A*Real.sqrt H := by
  have base : (gapCover H A).card≤∑ u∈Icc 1 H, ∑ k∈Icc 1 H, (gapRow H A u k).card :=
    card_biUnion_le.trans (sum_le_sum fun _ _ => card_biUnion_le)
  have baseR := (Nat.cast_le (α:=ℝ)).mpr base
  push_cast at baseR
  apply baseR.trans
  let C : ℝ := A*Real.sqrt H
  let f (u : ℕ) := 1/((u:ℝ)*Real.sqrt u)
  let g (k : ℕ) := 1/(k:ℝ)^2
  have both : (∑ u∈Icc 1 H,f u)*(∑ k∈Icc 1 H,g k)≤3*2 := by
    apply mul_le_mul _ _ (by dsimp [g]; positivity) (by norm_num)
    · exact (PrimeFactors.FloorSquareShiftPopulation.root_sum_aux hp).trans (sub_le_self _ (by positivity))
    · exact (PrimeFactors.FloorSquareShiftPopulation.square_sum_aux hp).trans (sub_le_self _ (by positivity))
  calc _ ≤ ∑ u∈Icc 1 H, ∑ k∈Icc 1 H, C*f u*g k :=
           sum_le_sum fun u _ => sum_le_sum fun k _ => gap_row_count H A u k
       _ = C*((∑ u∈Icc 1 H,f u)*(∑ k∈Icc 1 H,g k)) := by
         simp_rw [←mul_sum]
         rw [←sum_mul,←mul_sum,mul_assoc]
       _ ≤ C*(3*2) := mul_le_mul_of_nonneg_left both (by dsimp [C]; positivity)
       _ = _ := by dsimp [C]; ring

/-- The alternative cover is sharper for short center windows and includes h=p. -/
theorem linear_count (P : Finset (ℕ×ℕ)) {H W : ℕ} (hp : 0<H)
    (valid : ∀ v∈P, v.1<v.2 ∧ v.2≤H ∧ ∃ s h, window (v.1*v.2) W s ∧ shifted v.1 v.2 s h) :
    (P.card:ℝ) ≤ 12*((W+1:ℕ):ℝ)*H*Real.sqrt H := by
  have sub : P⊆gapCover H (2*(W+1)*H) := by
    rintro ⟨p,q⟩ hmem
    obtain ⟨lt,high,s,h,hw,ht⟩ := valid _ hmem
    obtain ⟨u,x,k,up,kp,P,Q,size⟩ := coordinates lt high hw ht
    exact mem_gap_cover up kp ht.1 high P Q size
  have bound := ((Nat.cast_le (α:=ℝ)).mpr (card_le_card sub)).trans (gap_cover_count _ _ hp)
  apply bound.trans_eq
  push_cast
  ring

open MixedPrefixSample
open private PrimeFactors.MonotoneSumPopulation.data from PrimeFactors.MonotoneSumPopulation

attribute [local irreducible] eligible MixedPrefixSample.primes
set_option exponentiation.threshold 4096

noncomputable def successes (W : ℕ) : Finset (ℕ×ℕ) := by
  classical
  exact eligible.filter fun v => ∃ s h, window (v.1*v.2) W s ∧ shifted v.1 v.2 s h

/-- The budget counts the floor center itself. -/
theorem full_width {W : ℕ} (budget : W+1≤2^900) :
    2^24*(successes W).card<eligible.card := by
  classical
  have cnt := finite_count (successes W) (H:=2^1024) (W:=W) (by
    intro v hv
    obtain ⟨mem,yes⟩ := mem_filter.mp hv
    obtain ⟨ord,top⟩ := PrimeFactors.MonotoneSumPopulation.data mem
    exact ⟨ord,top.le,yes⟩)
  have rad : 2*(W+1)*2^1024≤(3*2^961)^2 :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ budget)).trans (by decide +kernel)
  have rt := Real.sqrt_le_sqrt ((Nat.cast_le (α:=ℝ)).mpr rad)
  rw [show (((3*2^961)^2:ℕ):ℝ)=((3*2^961:ℕ):ℝ)^2 by simp only [Nat.cast_pow],
    Real.sqrt_sq (Nat.cast_nonneg _)] at rt
  have harm : (harmonic (2^1024):ℝ)≤1025 :=
    (PrimeFactors.SquareScaleHarmonicBound.power_harmonic 1024).trans_eq (by norm_num)
  have hn : 0≤(harmonic (2^1024):ℝ) := by rw [←PrimeFactors.SquareScaleHarmonicBound.reciprocal]; positivity
  have cum := mul_le_mul_of_nonneg_left (mul_le_mul rt harm hn (by positivity)) (show
    0≤2*((2^1024:ℕ):ℝ) by positivity)
  rw [←mul_assoc,←mul_assoc] at cum
  have count : (successes W).card≤2*2^1024*(3*2^961)*1025 := by
    exact_mod_cast cnt.trans cum
  have room : 21000000*(2^24*(2*2^1024*(3*2^961)*1025))≤(2:ℕ)^2046 := by decide +kernel
  exact Nat.lt_of_mul_lt_mul_left ((Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left _ count)).trans_lt
    (room.trans_lt ChebyshevPrimeSample.eligible_count))

/-- At the floor there is no shift at all. One lower center gives the true
sum as twice the center plus the power of two in its remainder. -/
theorem one_below :
    Nat.Prime 283 ∧ Nat.Prime 491 ∧ 283*491=138953 ∧ (138953:ℕ).sqrt=372 ∧
    138953-372^2=569 ∧ (∀ h, ¬shifted 283 491 372 h) ∧
    window 138953 1 371 ∧ shifted 283 491 371 41 ∧ 138953-371^2=1312 ∧
    FloorSquareShift.twoPart 1312=32 ∧ 2*371+32=283+491 ∧
    (2*371+32)^2-4*138953=208^2 := by
  have root : (138953:ℕ).sqrt=372 := by norm_num
  have zero : window (283*491) 0 372 := by unfold window; norm_num
  refine ⟨by norm_num,by norm_num,by norm_num,root,by norm_num,?_,?_,?_,by norm_num,?_,
    by norm_num,by norm_num⟩
  · intro h yes
    have eqn := (shifted_iff (by norm_num : 283<491) zero yes.1).mp yes
    norm_num at eqn
    omega
  · unfold window; rw [root]; decide
  · norm_num [shifted]
  · exact FloorSquareShift.twoPart_odd_mul 5 (h:=41) (by decide)

/-- A smaller-than-shift center satisfies the integer equation on an actual prime pair. -/
theorem negative_branch :
    Nat.Prime 11 ∧ Nat.Prime 19 ∧ 7<10 ∧ window (11*19) 7 7 ∧ shifted 11 19 7 10 :=
  by norm_num [window,shifted]

end PrimeFactors.FloorShiftCenterWindow
