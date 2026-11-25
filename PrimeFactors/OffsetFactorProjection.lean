import PrimeFactors.ReducedOffsetMinimum
import PrimeFactors.OffsetWinnerExamples
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.NormNum

namespace PrimeFactors.OffsetFactorProjection

/-- The Gram form for an arbitrary trial divisor, with integral coefficients. -/
def R (d T h s v : ℤ) : ℤ := (d*s-T*v)^2+h*v^2

theorem gram_form {N T h : ℤ} (root : N=T^2+h) (d s v : ℤ) :
    R d T h s v=ReducedOffsetMinimum.Q (d^2) (d*T) N s v := by
  unfold R ReducedOffsetMinimum.Q;rw [root];ring

/-- The Gauss inequality does not require that d divide the product. -/
theorem signed_cover {N T h d : ℤ} (root : N=T^2+h) (hp : 0<h) (dp : 0<d) :
    ∃ s v : ℤ, IsCoprime s v ∧ 0<R d T h s v ∧ 3*(R d T h s v)^2≤4*d^2*h := by
  have det : d^2*N-(d*T)^2=d^2*h := by rw [root];ring
  obtain ⟨s,v,pos,short,prim⟩ := ReducedOffsetMinimum.exists_small (sq_pos_of_pos dp)
    (mul_pos (sq_pos_of_pos dp) hp) det
  exact ⟨s,v,prim,(gram_form root ..).symm ▸ pos,by rw [gram_form root];linarith only [short]⟩

/-- All trial divisors in the usual smaller-factor interval have a positive
primitive representative. The output coordinate v is strictly smaller than d. -/
theorem balanced_cover {N T h d : ℤ} (root : N=T^2+h) (tp : 0≤T) (hp : 0<h) (gap : h≤2*T)
    (dp : 6≤d) (low : N≤2*d^2) (high : d^2≤N) :
    ∃ s v : ℤ, 0<s ∧ 0<v ∧ v<d ∧ IsCoprime s v ∧ 0<R d T h s v ∧
      3*(R d T h s v)^2≤4*d^2*h := by
  obtain ⟨x,y,prim,pos,short⟩ := signed_cover root hp (by omega : 0<d)
  have tbound : T≤2*d := by
    apply (sq_le_sq₀ tp (by omega : 0≤2*d)).mp
    nlinarith only [root,low,hp,sq_nonneg d]
  have cut : 4*h<3*d^2 := by nlinarith only [gap,tbound,dp,mul_nonneg (by omega : 0≤d-6) (by omega : 0≤d)]
  have small : R d T h x y<d^2 := by
    by_contra! bad
    have lb := pow_le_pow_left₀ (sq_nonneg d) bad 2
    have ub := mul_lt_mul_of_pos_left cut (sq_pos_of_ne_zero (by omega : d≠0))
    nlinarith only [lb,ub,short]
  have same : 0<x*y := by
    by_contra! signs
    have cross := mul_nonpos_of_nonneg_of_nonpos (show 0≤2*d*T by exact mul_nonneg (by omega) tp) signs
    rw [gram_form root] at small pos
    unfold ReducedOffsetMinimum.Q at small pos
    by_cases zx : x=0
    · have nz : y≠0 := by rintro rfl;simp [zx] at pos
      have one : 1≤y^2 := by have := sq_pos_of_ne_zero nz;omega
      nlinarith only [small,high,zx,mul_le_mul_of_nonneg_left one (sq_nonneg d),
        mul_le_mul_of_nonneg_right high (sq_nonneg y),cross,
        mul_nonneg (sq_nonneg d) (sq_nonneg x)]
    · have one : 1≤x^2 := by have := sq_pos_of_ne_zero zx;omega
      nlinarith only [small,mul_le_mul_of_nonneg_left one (sq_nonneg d),cross,
        mul_nonneg ((sq_nonneg d).trans high) (sq_nonneg y)]
  have ysmall : |y|<d := by
    by_contra! large
    have big := pow_le_pow_left₀ (by omega : 0≤d) large 2
    rw [sq_abs] at big
    unfold R at small
    nlinarith only [small,big,sq_nonneg (d*x-T*y),
      mul_le_mul_of_nonneg_right (show 1≤h by omega) (sq_nonneg y)]
  rcases (mul_pos_iff.mp same) with ⟨xp,yp⟩|⟨xn,yn⟩
  · exact ⟨x,y,xp,yp,by rwa [abs_of_pos yp] at ysmall,prim,pos,short⟩
  · have ident : R d T h (-x) (-y)=R d T h x y := by unfold R;ring
    obtain ⟨a,b,bez⟩ := prim
    exact ⟨-x,-y,by omega,by omega,by rwa [abs_of_neg yn] at ysmall,
      ⟨-a,-b,by linear_combination bez⟩,ident ▸ pos,ident ▸ short⟩

/-- The numerator reduces to N*v² modulo the proposed factor d. -/
theorem numerator_mod {N T h : ℤ} (root : N=T^2+h) (d s v : ℤ) :
    d ∣ R d T h s v-N*v^2 := by
  exact ⟨d*s^2-2*T*s*v,by unfold R;rw [root];ring⟩

theorem denominator_divides {N T h d s v a b : ℤ} (root : N=T^2+h)
    (cop : IsCoprime d N) (rat : b*R d T h s v=a*d) : d∣b*v^2 := by
  obtain ⟨u,hu⟩ := numerator_mod root d s v
  apply cop.dvd_of_dvd_mul_left
  exact ⟨a-b*u,by linear_combination rat-b*hu⟩

/-- A trial divisor coprime to N cannot produce a small positive denominator
unless the public square gap h is itself small. This applies to any short
representation and does not assume its fraction was reduced. -/
theorem denominator_floor {N T h d s v a b : ℤ} (root : N=T^2+h)
    (hp : 0<h) (dp : 0<d) (vp : 0<v) (bp : 0<b) (cop : IsCoprime d N)
    (short : 3*(R d T h s v)^2≤4*d^2*h) (rat : b*R d T h s v=a*d) : 3*h≤4*b^2 := by
  have div := denominator_divides root cop rat
  have dl := Int.le_of_dvd (mul_pos bp (sq_pos_of_pos vp)) div
  have mass : h*v^2≤R d T h s v := by unfold R;nlinarith only [sq_nonneg (d*s-T*v)]
  have br : h*d≤b*R d T h s v := by
    nlinarith only [mul_le_mul_of_nonneg_left dl hp.le,mul_le_mul_of_nonneg_left mass bp.le]
  have low := pow_le_pow_left₀ (mul_nonneg hp.le dp.le) br 2
  have upper := mul_le_mul_of_nonneg_left short (sq_nonneg b)
  apply (mul_le_mul_iff_of_pos_right (mul_pos hp (sq_pos_of_pos dp))).mp
  nlinarith only [low,upper]

/-- A prime trial divisor and 0<v<d make the reduced denominator an exact
divisibility test: it is 1 for a divisor, and d for all other primes. -/
theorem prime_denominator {N T h d s v a b : ℤ} (root : N=T^2+h)
    (prime : Prime d) (dp : 0<d) (vp : 0<v) (lt : v<d) (bp : 0<b)
    (reduced : IsCoprime a b) (rat : b*R d T h s v=a*d) :
    (d∣N ∧ b=1) ∨ (¬d∣N ∧ b=d) := by
  have bd : b∣d := reduced.symm.dvd_of_dvd_mul_left ⟨_,rat.symm⟩
  by_cases dn : d∣N
  · obtain ⟨u,hu⟩ := numerator_mod root d s v
    obtain ⟨q,hq⟩ := dn
    have rr : R d T h s v=d*(u+q*v^2) := by rw [hq] at hu;linarith only [hu]
    have ar : a=b*(u+q*v^2) := by
      apply mul_left_cancel₀ dp.ne'
      rw [rr] at rat
      linear_combination -rat
    obtain ⟨x,y,bez⟩ := reduced
    have bOne : b∣1 := ⟨x*(u+q*v^2)+y,by rw [ar] at bez;linear_combination -bez⟩
    exact Or.inl ⟨⟨q,hq⟩,by have := Int.le_of_dvd (by decide : (0:ℤ)<1) bOne;omega⟩
  · have bv := denominator_divides root (prime.coprime_iff_not_dvd.mpr dn) rat
    have db : d∣b := (prime.dvd_mul.mp bv).resolve_right (fun bad =>
      (by omega : ¬d≤v) (Int.le_of_dvd vp (prime.dvd_of_dvd_pow bad)))
    exact Or.inr ⟨dn,le_antisymm (Int.le_of_dvd dp bd) (Int.le_of_dvd bp db)⟩

/-- A public subinterval whose every trial admits the promised short pair.
The map i ↦ T−i is injective and uses no factors. -/
theorem band {N T h i : ℤ} (root : N=T^2+h) (tp : 16≤T) (hp : 0<h)
    (gap : h≤2*T) (nonneg : 0 ≤ i) (room : 4*i ≤ T) :
    N≤2*(T-i)^2 ∧ (T-i)^2≤N ∧
      ∃ s v : ℤ, 0<s ∧ 0<v ∧ v<T-i ∧ IsCoprime s v ∧ 0<R (T-i) T h s v ∧
        3*(R (T-i) T h s v)^2≤4*(T-i)^2*h := by
  have upper : (T-i)^2≤N := (pow_le_pow_left₀ (by omega : 0≤T-i) (by omega : T-i≤T) 2).trans
    (by omega)
  have square := pow_le_pow_left₀ (by omega : 0≤3*T) (by omega : 3*T≤4*(T-i)) 2
  have lower : N≤2*(T-i)^2 := by
    nlinarith only [square,root,gap,mul_nonneg (show 0≤T-16 by omega) (show 0≤T by omega)]
  exact ⟨lower,upper,balanced_cover root (by omega) hp gap (by omega) lower upper⟩

/-- At a 2,048-bit nonsquare product, at least 2^1021 distinct trial values
T−i in the balanced interval all pass the size and positivity test. -/
theorem target_band {N : ℕ} (size : 2^2047≤N) (nonsquare : N.sqrt^2<N)
    (i : Fin (2^1021)) :
    let T : ℤ := N.sqrt
    let h : ℤ := N-T^2
    let d : ℤ := T-(i:ℕ)
    (N:ℤ)≤2*d^2 ∧ d^2≤N ∧
      ∃ s v : ℤ, 0<s ∧ 0<v ∧ v<d ∧ IsCoprime s v ∧ 0<R d T h s v ∧ 3*(R d T h s v)^2≤4*d^2*h := by
  dsimp only
  have large : (4:ℕ)*2^1021≤N.sqrt := Nat.le_sqrt.mpr <|
    (show 4*2^1021*(4*2^1021)≤(2:ℕ)^2047 by decide +kernel).trans size
  have t16 : 16≤N.sqrt := (show 16≤(4:ℕ)*2^1021 by decide +kernel).trans large
  have i4 := (Nat.mul_le_mul_left 4 i.isLt.le).trans large
  have close := Nat.lt_succ_sqrt' N
  have bound : N≤N.sqrt^2+2*N.sqrt := by nlinarith only [close]
  have hp : (N.sqrt:ℤ)^2<N := by exact_mod_cast nonsquare
  have upper : (N:ℤ)≤(N.sqrt:ℤ)^2+2*N.sqrt := by exact_mod_cast bound
  have bound4 : (4:ℤ)*(i:ℕ)≤N.sqrt := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (Int.ofNat_le.mpr i4)
  exact band (T:=(N.sqrt:ℤ)) (N:=(N:ℤ)) (h:=(N:ℤ)-(N.sqrt:ℤ)^2) (i:=(i:ℕ))
    (by ring) (Int.ofNat_le.mpr t16) (by omega) (by omega) (Int.natCast_nonneg _) bound4

/-- True and false trial values can even share the same short vector.
The fractions are 4849/251, 17, 5041/263 respectively. -/
theorem sample_vectors :
    R 251 342 485 4 3=4849 ∧ R 257 342 485 4 3=257*17 ∧ R 263 342 485 4 3=5041 ∧
      3*4849^2≤4*(251:ℤ)^2*485 ∧ 3*(257*17)^2≤4*(257:ℤ)^2*485 ∧
      3*5041^2≤4*(263:ℤ)^2*485 ∧ 117449=(257:ℤ)*457 ∧
      (4849:ℕ).Coprime 251 ∧ (5041:ℕ).Coprime 263 := by decide +kernel

/-- Each of these 100 integers has a short pair by balanced_cover. Only
257 shares a factor with N; the denominator bound bars an integral value
at every other candidate. -/
theorem sample_interval :
    ((List.range 100).map (fun i => 243+i)).filter (fun d => 1<Nat.gcd d 117449)=[257] ∧
    342^2+485=(117449:ℕ) ∧ 117449≤2*243^2 ∧ 342^2≤117449 := by decide +kernel

/-- The public gaps on the two full-size controls each impose a denominator
strictly larger than 2^511 for any positive short vector at a coprime trial. -/
theorem control_gaps : 4*((2:ℤ)^511)^2<3*GroupedOffsetRowExamples.fresh.h ∧
    4*((2:ℤ)^511)^2<3*GroupedOffsetRowExamples.crossed.h := by decide +kernel

/-- With the oriented factor coordinates supplied, the inequality defining
the possible q values has these exact, rounded integer endpoints. -/
def window (C D v : ℤ) : ℤ × ℤ :=
  let B : ℤ := D.toNat.sqrt
  ( -((B-C)/(2*v^2)), (C+B)/(2*v^2))

def adviceCenter (T J s v : ℤ) := 2*T*s*v+J
def adviceDisc (N C s v : ℤ) := C^2-4*N*(s*v)^2

private theorem abs_le_root {z D : ℤ} (dp : 0≤D) : |z|≤(D.toNat.sqrt:ℤ) ↔ z^2≤D := by
  rw [←Int.natCast_natAbs]
  rw [Int.ofNat_le,Nat.le_sqrt',←Int.ofNat_le]
  simp only [Nat.cast_pow,Int.natCast_natAbs,sq_abs,Int.toNat_of_nonneg dp]

theorem window_iff {N C s v q : ℤ} (vp : 0<v) (dp : 0≤adviceDisc N C s v) :
    let w := window C (adviceDisc N C s v) v
    w.1≤q ∧ q≤w.2 ↔ v^2*q^2+N*s^2≤C*q := by
  let D := adviceDisc N C s v
  let B : ℤ := D.toNat.sqrt
  have denom : 0<2*v^2 := by positivity
  change -((B-C)/(2*v^2))≤q ∧ q≤(C+B)/(2*v^2) ↔ _
  have equivalent : -((B-C)/(2*v^2))≤q ↔ -q≤(B-C)/(2*v^2) := by omega
  rw [equivalent,Int.le_ediv_iff_mul_le denom,Int.le_ediv_iff_mul_le denom]
  have sq : |2*v^2*q-C|≤B ↔ (2*v^2*q-C)^2≤D := abs_le_root dp
  have identity : (2*v^2*q-C)^2-D=4*v^2*(v^2*q^2+N*s^2-C*q) := by
    unfold D adviceDisc;ring
  have p : 0<4*v^2 := by positivity
  constructor
  · rintro ⟨left,right⟩
    have bounds : |2*v^2*q-C|≤B := abs_le.mpr ⟨by linarith only [left],by linarith only [right]⟩
    have h := sq.mp bounds
    have neg : 4*v^2*(v^2*q^2+N*s^2-C*q)≤0 := by linarith only [identity,h]
    by_contra! bad
    exact (not_lt_of_ge neg) (mul_pos p (sub_pos.mpr bad))
  · intro h
    have neg := mul_nonpos_of_nonneg_of_nonpos p.le (sub_nonpos.mpr h)
    have bounds := abs_le.mp (sq.mpr (by linarith only [neg,identity]))
    exact ⟨by linarith only [bounds.1],by linarith only [bounds.2]⟩

/-- No factor or winning index is needed to construct the window, once the
oriented coordinates are given. Its validity uses their promise. -/
theorem winning_window {N p q T J j s v : ℤ} (pair : p*q=N) (qp : 0<q)
    (vp : 0<v) (short : j≤J) (label : j+2*T*s*v=p*s^2+q*v^2) :
    let C := adviceCenter T J s v
    let w := window C (adviceDisc N C s v) v
    w.1≤q ∧ q≤w.2 := by
  let C := adviceCenter T J s v
  have allowed : v^2*q^2+N*s^2≤C*q := by
    unfold C adviceCenter
    nlinarith only [mul_le_mul_of_nonneg_right short qp.le,
      congrArg (fun x => x*q) label,congrArg (fun x => x*s^2) pair]
  have dp : 0≤adviceDisc N C s v := by
    unfold adviceDisc
    nlinarith only [sq_nonneg (2*v^2*q-C),
      mul_le_mul_of_nonneg_left allowed (show 0≤4*v^2 by positivity)]
  exact (window_iff vp dp).mpr allowed

/-- Any two members of the balanced, clipped interval obey the diameter
bound. Thus b blocks of M consecutive integers suffice whenever the
checked public threshold is strict. -/
theorem block_budget {N T h J s v l r U b M : ℤ} (root : N=T^2+h) (hp : 0≤h)
    (jp : 0≤J) (vp : 0<v) (mp : 0<M) (bp : 0<b)
    (left : v^2*l^2+N*s^2≤adviceCenter T J s v*l)
    (right : v^2*r^2+N*s^2≤adviceCenter T J s v*r)
    (lu : l≤U) (ru : r≤U) (cost : 4*U*J<(b*M*v)^2) : r-l+1≤b*M := by
  have diameter (q : ℤ) (qu : q≤U) (hit : v^2*q^2+N*s^2≤adviceCenter T J s v*q) :
      (v*q-T*s)^2≤U*J := by
    rw [root] at hit
    unfold adviceCenter at hit
    nlinarith only [hit,mul_nonneg hp (sq_nonneg s),mul_le_mul_of_nonneg_right qu jp]
  have wide : ((r-l)*v)^2≤4*U*J := by
    nlinarith only [diameter l lu left,diameter r ru right,sq_nonneg ((v*r-T*s)+(v*l-T*s))]
  by_contra! neg
  have bad : b*M≤r-l := by omega
  have large := pow_le_pow_left₀ (mul_nonneg (mul_nonneg bp.le mp.le) vp.le)
    (mul_le_mul_of_nonneg_right bad vp.le) 2
  linarith only [large,wide,cost]

/-- M=floor(N^(1/4)) gives N<(M+1)^4. Along the balanced branch
U=floor(sqrt(2N)), these bounds imply 16U<25M² from M≥49. -/
theorem balanced_cap {N M U : ℤ} (large : 49≤M) (up : 0≤U) (fourth : N<(M+1)^4)
    (balanced : U^2≤2*N) : 16*U<25*M^2 := by
  have u : 2*U<3*(M+1)^2 := (sq_lt_sq₀ (by positivity) (by positivity)).mp (by
    nlinarith only [balanced,fourth,sq_nonneg ((M+1)^2)])
  nlinarith only [u,mul_nonneg (by omega : 0≤M-49) (by omega : 0≤M),large]

/-- If J≤a²v², a whole number b≥5a/2 of fourth-root blocks suffices. -/
theorem threshold_of_coordinate {M U J v a b : ℤ} (up : 0≤U) (vp : 0<v)
    (ap : 0<a) (narrow : 16*U<25*M^2) (given : J≤a^2*v^2) (count : 5*a≤2*b) :
    4*U*J<(b*M*v)^2 := by
  have aa := pow_le_pow_left₀ (by omega : 0≤5*a) count 2
  have pos := mul_pos (sq_pos_of_pos ap) (sq_pos_of_pos vp)
  nlinarith only [mul_lt_mul_of_pos_right narrow pos,mul_le_mul_of_nonneg_left given up,
    mul_le_mul_of_nonneg_right aa (mul_nonneg (sq_nonneg M) (sq_nonneg v))]

/-- Static diagnostic using only the product and the supplied, oriented pair.
Its output is the number of fourth-root blocks in the clipped interval. -/
def adviceBlocks (N T s v : ℕ) : ℤ :=
  let J := (4*(N-T^2)/3).sqrt
  let C := adviceCenter T J s v
  let w := window C (adviceDisc N C s v) v
  let lo := max ((T:ℤ)+1) w.1
  let hi := min ((2*N).sqrt:ℤ) w.2
  let M : ℤ := T.sqrt
  Int.neg (-(max 0 (hi-lo+1))/M)

private theorem block_receipt {N T s v J U M B : ℕ} {n : ℤ}
    (jroot : J^2≤4*(N-T^2)/3 ∧ 4*(N-T^2)/3<(J+1)^2)
    (uroot : U^2≤2*N ∧ 2*N<(U+1)^2) (mroot : M^2≤T ∧ T<(M+1)^2)
    (broot : let r := (adviceDisc N (adviceCenter T J s v) s v).toNat
             B^2≤r ∧ r<(B+1)^2)
    (count : let C := adviceCenter T J s v
             let lo := max ((T:ℤ)+1) (-(((B:ℤ)-C)/(2*(v:ℤ)^2)))
             let hi := min (U:ℤ) ((C+B)/(2*(v:ℤ)^2))
             Int.neg (-(max 0 (hi-lo+1))/(M:ℤ))=n) :
    adviceBlocks N T s v=n := by
  unfold adviceBlocks window
  rw [←Nat.eq_sqrt'.mpr jroot,←Nat.eq_sqrt'.mpr uroot,←Nat.eq_sqrt'.mpr mroot]
  dsimp only
  rw [←Nat.eq_sqrt'.mpr broot]
  exact count

open OffsetWinnerExamples in
/-- Exact block counts on both previously published oriented winning pairs.
The large integers below are public square-root witnesses for fast checking. -/
theorem diagnostic_blocks :
    adviceBlocks fresh.N fresh.T fresh.s fresh.v=4 ∧
      adviceBlocks crossed.N crossed.T crossed.s crossed.v=13 := by
  constructor
  · apply block_receipt (J:=13067502587245419214137172104630121073482637691080509949309671753508520973868181566754782517173379282774064785472833866148120530048455879939352849256687438)
      (U:=223908246094442142980375511361039506422193179527592602359425549717548204480658658974232117010331136956665574794314958174612405423331068550356751047904404193818866454566667202016622621231736709209226909768698965215652342707819673339883558453162023577800105726386456083478852215328369640288060051549180408424874)
      (M:=12582807285219238178151920199299128436706537317213621663278205455709317420753286080734434933477807423875070067930433429440740120698232220461461064570597289)
      (B:=150792826134281306880255516774702463990238801075340772480968734556535097430194006838428779583891724514244542908166955484703903626952894480819034259107510225072842523351347611305954994662148058898178465270485096290772076302160655115463409470338585847054113587561338753504719642475926471429827323638957613661884)
    all_goals decide +kernel
  · apply block_receipt (J:=10180462151122173833116201538330563755838314116875457809045809112770025232014358604535744895966672512512602273545330636867869005179574747298783823711533414)
      (U:=190972446139800417518088652074279462268963306404574793047021092955072565972169935841939141854806650902365465724683816880669029238482101799013126806262871850885678583494519719837640210387203883116550295754559478666287234810146597746006002586149182460690694226988393194638667076609387167294640505074131766763025)
      (M:=11620581383271474953481306877792968323557861615186413874341935191448832227000567855365583586571825030737413858708145463473223141577888868605281077495572686)
      (B:=42911152162788277178463919139615123755520497724445676335711620421100332233924037831092390527167717909291917971407288021349528450890816802822232517617322944675162118745665440225164310570280239384877402406087694909401787760779488855957105008478831168018773533494399510662490224235634975056376574457985657724279)
    all_goals decide +kernel

/-- Any collection of finite blocks covering the distinct smaller-factor
trials from target_band needs at least 2^509 members at this width. -/
theorem small_side_cover {ι : Type*} [DecidableEq ι] {T : ℤ}
    (indices : Finset ι) (blocks : ι → Finset ℤ)
    (cap : ∀ k∈indices, (blocks k).card≤2^512)
    (covers : ∀ i : Fin (2^1021), ∃ k∈indices, T-(i:ℕ)∈blocks k) : 2^509 ≤ indices.card := by
  classical
  let f := fun (i : Fin (2^1021)) => T-(i:ℕ)
  have inj : Function.Injective f := by
    intro i j eq
    apply Fin.ext
    exact Int.ofNat_inj.mp (sub_right_inj.mp eq)
  have sub : (Finset.univ.image f) ⊆ indices.biUnion blocks := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_biUnion.mpr (covers i)
  have size := (Finset.card_le_card sub).trans (Finset.card_biUnion_le_card_mul indices blocks _ cap)
  rw [Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_fin] at size
  have powEq : (2:ℕ)^1021=2^509*2^512 := by rw [←pow_add]
  rw [powEq] at size
  exact (Nat.le_of_mul_le_mul_right size (by positivity))

end PrimeFactors.OffsetFactorProjection
