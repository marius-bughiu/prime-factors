import PrimeFactors.SquareScalePairCoordinates
import PrimeFactors.DiscriminantStride
import Mathlib.Data.Nat.Log

/-!
# Reading a possible factor sum from the power of two in a square remainder

For a nonsquare product, let r be its floor square root, D its remainder
above r², and J the excess of the true sum above 2r. An integer shift h
matches the square (r−h)² exactly when D=hJ. The product-only proposal
uses the largest power of two dividing D as its one guess for J.
-/

namespace PrimeFactors.FloorSquareShift

def residual (n : ℕ) := n-n.sqrt^2

def excess (p q : ℕ) := p+q-2*(p*q).sqrt

def shift (p q h : ℕ) : Prop :=
  0<h ∧ h≤p ∧ (p-h)*(q-h)=((p*q).sqrt-h)^2

private theorem floor_bounds {p q : ℕ} (lt : p<q) :
    p≤(p*q).sqrt ∧ (p*q).sqrt≤q ∧ 2*(p*q).sqrt<p+q := by
  have rs : (p*q).sqrt^2 ≤ p*q := Nat.sqrt_le' _
  have sm : 4*(p*q)<(p+q)^2 := by
    have diff : (0:ℤ)<(q:ℤ)-p := sub_pos.mpr (Int.ofNat_lt.mpr lt)
    have sq := sq_pos_of_pos diff
    zify
    nlinarith only [sq]
  refine ⟨Nat.le_sqrt'.mpr (by simpa [pow_two] using Nat.mul_le_mul_left p lt.le),
    ?_, ?_⟩
  · have h := Nat.sqrt_le_sqrt (Nat.mul_le_mul_right q lt.le)
    simpa only [Nat.sqrt_eq] using h
  · apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    nlinarith only [sm,rs]

theorem excess_identity {p q : ℕ} (lt : p<q) :
    residual (p*q)+((p*q).sqrt-p)^2=p*excess p q := by
  have f := floor_bounds lt
  have h := Nat.sqrt_le' (p*q)
  unfold residual excess
  zify [h, f.1, f.2.2.le]
  ring

theorem shift_iff {p q h : ℕ} (lt : p<q) (hp : 0<h) :
    shift p q h ↔ residual (p*q)=h*excess p q := by
  have f := floor_bounds lt
  have rs := Nat.sqrt_le' (p*q)
  have ep : 0<excess p q := Nat.sub_pos_of_lt f.2.2
  constructor
  · rintro ⟨_,h₁,h₂⟩
    have hq := h₁.trans lt.le
    have hr := h₁.trans f.1
    unfold residual excess
    zify [h₁,hq,hr,rs,f.2.2.le] at h₂ ⊢
    nlinarith only [h₂]
  · intro eqn
    have id := excess_identity lt
    rw [eqn] at id
    have h₁ : h≤p := Nat.le_of_mul_le_mul_right (by omega : h*excess p q≤p*excess p q) ep
    refine ⟨hp,h₁,?_⟩
    have hq := h₁.trans lt.le
    have hr := h₁.trans f.1
    unfold residual excess at eqn
    zify [h₁,hq,hr,rs,f.2.2.le] at eqn ⊢
    nlinarith only [eqn]

theorem exists_shift_iff {p q : ℕ} (lt : p<q) (ns : 0<residual (p*q)) :
    (∃ h, shift p q h) ↔ excess p q ∣ residual (p*q) := by
  constructor
  · rintro ⟨h,h₁⟩
    have ee := (shift_iff lt h₁.1).mp h₁
    exact ⟨h,ee.trans (mul_comm _ _)⟩
  · rintro ⟨h,eqn⟩
    have hp : 0<h := by by_contra! hz; rw [show h=0 by omega,mul_zero] at eqn; omega
    exact ⟨h,(shift_iff lt hp).mpr (eqn.trans (mul_comm _ _))⟩

theorem shift_unique {p q h j : ℕ} (lt : p<q) (hh : shift p q h) (hj : shift p q j) :
    h=j := by
  have ep : 0<excess p q := Nat.sub_pos_of_lt (floor_bounds lt).2.2
  exact Nat.eq_of_mul_eq_mul_right ep (((shift_iff lt hh.1).mp hh).symm.trans ((shift_iff lt hj.1).mp hj))

/-- Divisibility is part of testing a candidate shift when natural division is used. -/
def atShift (n h : ℕ) := 2*n.sqrt+residual n/h

theorem atShift_iff {p q h : ℕ} (lt : p<q) (hp : 0<h) :
    shift p q h ↔ h∣residual (p*q) ∧ atShift (p*q) h=p+q := by
  have f := (floor_bounds lt).2.2
  rw [shift_iff lt hp]
  constructor
  · intro hit
    refine ⟨⟨excess p q,hit⟩,?_⟩
    rw [atShift,hit,Nat.mul_div_cancel_left _ hp]
    unfold excess
    omega
  · rintro ⟨dvd,eqn⟩
    unfold atShift at eqn
    have j : excess p q=residual (p*q)/h := by unfold excess; omega
    rw [j,Nat.mul_div_cancel' dvd]

theorem at_one {n : ℕ} (hp : 0<n) : atShift n 1=predecessorSquareSum n 1 := by
  have root : 1≤n.sqrt := Nat.le_sqrt'.mpr hp
  have top := Nat.sqrt_le' n
  simp only [atShift,residual,Nat.div_one,predecessorSquareSum,if_true,one_mul]
  have lt : (n.sqrt-1)^2≤n+1 := by
    have base : n.sqrt-1≤n.sqrt := Nat.sub_le _ _
    exact (Nat.pow_le_pow_left base 2).trans (by omega)
  zify [root,top,lt]
  ring

/-- A known squarefree part gives the shift when the excess is a square and
the shift is squarefree. The input decomposition supplies the squarefree part. -/
theorem at_squarefree_part {p q h k c v : ℕ} (lt : p<q) (hit : shift p q h)
    (hf : Squarefree h) (gap : excess p q=k^2)
    (cf : Squarefree c) (vp : 0<v) (supplied : residual (p*q)=c*v^2) :
    h=c ∧ atShift (p*q) c=p+q := by
  have eqn := (shift_iff lt hit.1).mp hit
  rw [gap] at eqn
  obtain ⟨w,_,hw⟩ := JacobiPeriodSquareClass.square_class hf vp (eqn.symm.trans supplied)
  have w1 : w=1 := Nat.isUnit_iff.mp (cf w (by rw [hw,pow_two]; exact dvd_mul_left ..))
  have hc : h=c := by simpa [w1] using hw.symm
  exact ⟨hc,hc ▸ ((atShift_iff lt hit.1).mp hit).2⟩

/-- One gcd with the largest power of two no larger than the displayed integer. -/
def twoPart (D : ℕ) := D.gcd (2^D.log2)

def proposed (n : ℕ) := 2*n.sqrt+twoPart (residual n)

theorem twoPart_odd_mul (j : ℕ) {h : ℕ} (odd : Odd h) : twoPart (h*2^j)=2^j := by
  have hp : 0<h := by obtain ⟨k,hk⟩ := odd; omega
  have hj : j≤Nat.log 2 (h*2^j) := Nat.le_log_of_pow_le (by decide) (by
    calc 2^j = 1*2^j := by simp
         _ ≤ _ := Nat.mul_le_mul_right _ hp)
  let k := Nat.log 2 (h*2^j)-j
  have hk : Nat.log 2 (h*2^j)=k+j := by dsimp [k]; omega
  unfold twoPart
  rw [Nat.log2_eq_log_two,hk,pow_add,Nat.gcd_mul_right,(odd.coprime_two_right.pow_right k).gcd_eq_one]
  simp

theorem dyadic_read {p q h j : ℕ} (lt : p<q) (hs : shift p q h)
    (odd : Odd h) (dyadic : excess p q=2^j) : proposed (p*q)=p+q := by
  have f := floor_bounds lt
  have eqn := (shift_iff lt hs.1).mp hs
  rw [dyadic] at eqn
  rw [proposed,eqn,twoPart_odd_mul _ odd,←dyadic]
  unfold excess
  omega

/-- Exact success of the public reading. The uniquely possible shift is the odd
part of the residual, and the true sum must be a dyadic distance above twice the root. -/
theorem dyadic_iff {p q : ℕ} (lt : p<q) (ns : 0<residual (p*q)) :
    proposed (p*q)=p+q ↔ ∃ h j, Odd h ∧ shift p q h ∧ excess p q=2^j := by
  constructor
  · intro ok
    obtain ⟨j,h,odd,hh⟩ := Nat.exists_eq_two_pow_mul_odd ns.ne'
    have prod : residual (p*q)=h*2^j := hh.trans (mul_comm _ _)
    have hp : 0<h := by obtain ⟨k,hk⟩ := odd; omega
    rw [proposed,prod,twoPart_odd_mul j odd] at ok
    have ej : excess p q=2^j := by unfold excess; rw [←ok,Nat.add_sub_cancel_left]
    exact ⟨h,j,odd,(shift_iff lt hp).mpr (by rw [ej,prod]),ej⟩
  · rintro ⟨h,j,odd,hs,ej⟩
    exact dyadic_read lt hs odd ej

/-- The same factor-square class can be nontrivial on both sides of the shift. -/
theorem square_offset (u x k h : ℕ) :
    (h+u*x^2)*(h+u*(x+k)^2)=(h+u*x*(x+k))^2+h*u*k^2 := by ring

theorem centered {u x k h : ℕ} (bound : h*u*k^2≤2*(h+u*x*(x+k))) :
    ((h+u*x^2)*(h+u*(x+k)^2)).sqrt=h+u*x*(x+k) := by
  rw [square_offset]
  apply Nat.le_antisymm
  · apply Nat.le_of_lt_succ
    apply Nat.sqrt_lt'.mpr
    nlinarith only [bound]
  · exact Nat.le_sqrt'.mpr (Nat.le_add_right _ _)

theorem square_read {x k h j : ℕ} (odd : Odd h) (power : k=2^j)
    (bound : h*k^2≤2*(h+x*(x+k))) :
    proposed ((h+x^2)*(h+(x+k)^2))=h+x^2+(h+(x+k)^2) := by
  have rs := centered (u:=1) (x:=x) (k:=k) (h:=h) (by simpa using bound)
  simp only [one_mul,mul_one] at rs
  have eqn := square_offset 1 x k h
  simp only [one_mul,mul_one] at eqn
  have remn : residual ((h+x^2)*(h+(x+k)^2))=h*k^2 := by
    unfold residual
    rw [rs,eqn,Nat.add_sub_cancel_left]
  rw [proposed,rs,remn,power,←pow_mul,twoPart_odd_mul]
  · ring
  · exact odd

/-- Every shifted-square witness below the smaller factor has common square coordinates.
The floor constraint bounds the product of the shift, common scale and squared index gap. -/
theorem coordinates {p q h : ℕ} (lt : p<q) (proper : h<p) (hs : shift p q h) :
    ∃ u x k : ℕ, 0<u ∧ 0<x ∧ 0<k ∧ p=h+u*x^2 ∧ q=h+u*(x+k)^2 ∧
      (p*q).sqrt=h+u*x*(x+k) ∧ residual (p*q)=h*u*k^2 ∧ h*u*k^2≤2*(p*q).sqrt := by
  obtain ⟨hp,hh,hit⟩ := hs
  obtain ⟨u,m,n,x,z,up,mp,np,xp,zp,A,C,_,mn,_,_⟩ :=
    SquareScalePairCoordinates.coordinates (L:=1) (t:=1) (y:=(p*q).sqrt-h)
      (Nat.sub_pos_of_lt proper) (Nat.sub_pos_of_lt (proper.trans lt)) zero_lt_one le_rfl
      (by simpa only [one_mul] using hit)
  have mn1 := Nat.eq_one_of_dvd_one mn
  obtain rfl : m=1 := Nat.eq_one_of_dvd_one (mn1 ▸ dvd_mul_right m n)
  simp only [one_mul] at mn1
  subst n
  simp only [mul_one] at A C
  have P : p=h+u*x^2 := by omega
  have Q : q=h+u*z^2 := by omega
  have order : x<z := by
    by_contra! opp
    have sq := Nat.pow_le_pow_left opp 2
    have mono := Nat.mul_le_mul_left u sq
    omega
  let k := z-x
  have K : z=x+k := by dsimp [k]; omega
  rw [K] at Q
  have prod : p*q=(h+u*x*(x+k))^2+h*u*k^2 := by rw [P,Q,square_offset]
  have rh : h≤(p*q).sqrt := hh.trans (floor_bounds lt).1
  have rhs : (p*q).sqrt-h=u*x*(x+k) := by
    apply (Nat.pow_left_inj (by decide : 2≠0)).mp
    rw [←hit,A,C,K]
    ring
  have center : (p*q).sqrt=h+u*x*(x+k) := by omega
  have rem : residual (p*q)=h*u*k^2 := by
    unfold residual
    rw [center,prod,Nat.add_sub_cancel_left]
  refine ⟨u,x,k,up,xp,Nat.sub_pos_of_lt order,P,Q,center,rem,?_⟩
  have above := Nat.lt_succ_sqrt' (p*q)
  rw [center] at above ⊢
  rw [prod] at above
  nlinarith only [above]

theorem odd_residual_excludes {p q h : ℕ} (lt : p<q) (op : Odd p) (oq : Odd q)
    (odd : Odd (residual (p*q))) : ¬shift p q h := by
  intro hit
  obtain ⟨a,pa⟩ := op
  obtain ⟨b,pb⟩ := oq
  have f := (floor_bounds lt).2.2
  have even : 2∣excess p q := by unfold excess; omega
  have dvd := even.trans ((shift_iff lt hit.1).mp hit ▸ dvd_mul_left (excess p q) h)
  exact (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr dvd)

private theorem rem_from {n r D : ℕ} (root : n.sqrt=r) (data : n=r^2+D) : residual n = D := by
  unfold residual
  rw [root,data,Nat.add_sub_cancel_left]

private theorem value_from {n r D J : ℕ} (root : n.sqrt=r) (rem : residual n=D) (part : twoPart D=J) :
    proposed n=2*r+J := by rw [proposed,root,rem,part]

private theorem shift_from {p q n r D h J : ℕ} (lt : p<q) (hp : 0<h) (prod : p*q=n)
    (root : n.sqrt=r) (rem : residual n=D) (mid : p+q=2*r+J) (eqn : D=h*J) : shift p q h := by
  apply (shift_iff lt hp).mpr
  rw [excess,prod,root,mid,Nat.add_sub_cancel_left,rem,eqn]

private theorem D138₁ : residual 32899=138 :=
  rem_from (r:=181) (by norm_num) (by norm_num)

private theorem D138₂ : residual 41347=138 :=
  rem_from (r:=203) (by norm_num) (by norm_num)

private theorem part138 : twoPart 138=2 := twoPart_odd_mul 1 (h:=69) (by decide)

private theorem D9472 : residual 36696721=9472 :=
  rem_from (r:=6057) (by norm_num) (by norm_num)

private theorem part9472 : twoPart 9472=256 := twoPart_odd_mul 8 (h:=37) (by decide)

/-- Two products of distinct eight-bit primes with the same remainder require different shifts. -/
theorem shared_remainder :
    Nat.Prime 167 ∧ Nat.Prime 197 ∧ Nat.Prime 173 ∧ Nat.Prime 239 ∧
    167*197=32899 ∧ 173*239=41347 ∧ residual 32899=138 ∧ residual 41347=138 ∧
    shift 167 197 69 ∧ shift 173 239 23 ∧ proposed 32899=364 ∧ proposed 41347=408 ∧
    173+239=412 := by
  refine ⟨by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,
    D138₁,D138₂,?_,?_,?_,?_,by norm_num⟩
  · exact shift_from (n:=32899) (r:=181) (J:=2) (by decide) (by decide) (by norm_num)
      (by norm_num) D138₁ (by norm_num) (by norm_num)
  · exact shift_from (n:=41347) (r:=203) (J:=6) (by decide) (by decide) (by norm_num)
      (by norm_num) D138₂ (by norm_num) (by norm_num)
  · exact value_from (r:=181) (by norm_num) D138₁ part138
  · exact value_from (r:=203) (by norm_num) D138₂ part138

/-- A genuine dyadic reading far past the first Fermat midpoint on a small synthetic pair. -/
theorem square_control :
    Nat.Prime 4937 ∧ Nat.Prime 7433 ∧ 4937*7433=36696721 ∧
    (36696721:ℕ).sqrt=6057 ∧ residual 36696721=9472 ∧ twoPart 9472=256 ∧
    proposed 36696721=12370 ∧ 4937+7433=12370 ∧
    4937=70^2+37 ∧ 7433=86^2+37 ∧ shift 4937 7433 37 := by
  refine ⟨by norm_num,by norm_num,by norm_num,by norm_num,D9472,part9472,
    ?_,by norm_num,by norm_num,by norm_num,?_⟩
  · exact value_from (r:=6057) (by norm_num) D9472 part9472
  · exact shift_from (n:=36696721) (r:=6057) (J:=256) (by decide) (by decide) (by norm_num)
      (by norm_num) D9472 (by norm_num) (by norm_num)

end PrimeFactors.FloorSquareShift
