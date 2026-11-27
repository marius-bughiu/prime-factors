import PrimeFactors.WeightedStride
import Mathlib.Data.Int.ModEq

/-! Recovering the distances of two factors below a known common upper endpoint. -/

namespace PrimeFactors.EndpointOffsetProduct

/-- The representative in [0, C * stride) of the product of the two offsets. -/
def residue (C n : ℕ) : ℕ :=
  ((((C : ℤ)-1)*(C-(n : ℤ))) % ((C : ℤ)*(weightedStride n 1 1 : ℕ))).toNat

theorem offset_mod {p q C : ℕ} (unit : p.Coprime 6) (hp : p≤C) (hq : q≤C) :
    residue C (p*q)=((C-p)*(C-q))%(C*weightedStride (p*q) 1 1) := by
  have sum := (weighted_sum_congruent unit 1 1 q).dvd
  simp only [one_mul, Nat.cast_add, Nat.cast_one, Nat.cast_mul] at sum
  obtain ⟨k,hk⟩ := sum
  have congr : ((C:ℤ)-1)*(C-(p:ℤ)*q) ≡ (C-(p:ℤ))*(C-(q:ℤ))
      [ZMOD (C:ℤ)*(weightedStride (p*q) 1 1 : ℕ)] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨k,by linear_combination (C:ℤ)*hk⟩
  have cast : (((C-p)*(C-q) : ℕ) : ℤ)=((C:ℤ)-p)*(C-q) := by
    rw [Nat.cast_mul, Nat.cast_sub hp, Nat.cast_sub hq]
  change _ % _ = _ % _ at congr
  rw [←cast] at congr
  unfold residue
  rw [Nat.cast_mul,congr,←Nat.cast_mul,←Int.natCast_mod,Int.toNat_natCast]

theorem exact_residue {p q C : ℕ} (unit : p.Coprime 6) (hp : p≤C) (hq : q≤C)
    (small : (C-p)*(C-q)<C*weightedStride (p*q) 1 1) :
    residue C (p*q)=(C-p)*(C-q) := by
  rw [offset_mod unit hp hq,Nat.mod_eq_of_lt small]

/-- Starting at the largest locally admissible factor sum below the endpoint
bound, the number of strides back to the true sum is exactly this quotient. -/
theorem trace_rank {p q C : ℕ} (unit : p.Coprime 6) (pos : 0<C) (hp : p≤C) (hq : q≤C) :
    (C^2+p*q-residue C (p*q))/C =
      p+q+weightedStride (p*q) 1 1 * (((C-p)*(C-q))/(C*weightedStride (p*q) 1 1)) := by
  let t := weightedStride (p*q) 1 1
  let area := (C-p)*(C-q)
  have top : C^2+p*q=C*(p+q)+area := by
    dsimp [area]
    zify [hp,hq]
    ring
  have rep := Nat.mod_add_div area (C*t)
  rw [offset_mod unit hp hq]
  change (C^2+p*q-area%(C*t))/C=p+q+t*(area/(C*t))
  have eq : C^2+p*q = C*(p+q+t*(area/(C*t)))+area%(C*t) := by
    calc
      C^2+p*q = C*(p+q)+(area%(C*t)+(C*t)*(area/(C*t))) := by rw [rep,top]
      _ = _ := by ring
  rw [eq,Nat.add_sub_cancel,Nat.mul_div_cancel_left _ pos]

/-- The decoder needs one integer square root after forming the public residue. -/
def decode (C n : ℕ) : ℕ × ℕ :=
  let r := residue C n
  let s := (C^2+r-n)/C
  let d := (s^2-4*r).sqrt
  (C-(s+d)/2,C-(s-d)/2)

theorem recover {p q C : ℕ} (unit : p.Coprime 6) (pos : 0<C) (ordered : p≤q)
    (hq : q≤C) (small : (C-p)*(C-q)<C*weightedStride (p*q) 1 1) :
    decode C (p*q)=(p,q) := by
  have hp := ordered.trans hq
  let a := C-p
  let b := C-q
  have ap : a+p=C := Nat.sub_add_cancel hp
  have bq : b+q=C := Nat.sub_add_cancel hq
  have ab : b≤a := Nat.sub_le_sub_left ordered C
  have both : C^2+a*b=C*(a+b)+p*q := by
    zify at ap bq ⊢
    linear_combination ((C:ℤ)-b)*(-ap) - (p:ℤ)*bq
  have ds : a-b+b=a := Nat.sub_add_cancel ab
  have sq : (a+b)^2=(a-b)^2+4*(a*b) := by
    zify [ab]
    ring
  unfold decode
  rw [exact_residue unit hp hq small]
  change (C-(_+_)/2,C-(_-_)/2)=(p,q)
  change (C-(((C^2+a*b-p*q)/C)+_)/2,C-(((C^2+a*b-p*q)/C)-_)/2)=(p,q)
  simp only [show C-p=a from rfl,show C-q=b from rfl,both,Nat.add_sub_cancel,
    Nat.mul_div_cancel_left _ pos,sq,Nat.sqrt_eq']
  congr 1 <;> omega

/-- A checked prediction. Both returned integers and the public remainder
are kept consistent even on an input outside the promised family. -/
def probe (C n : ℕ) : Option (ℕ × ℕ) :=
  let (p,q) := decode C n
  if 1<p ∧ p≤q ∧ q≤C ∧ p*q=n ∧ (C-p)*(C-q)=residue C n then some (p,q) else none

/-- Within the promised factor family the offset-area inequality is both
necessary and sufficient for this particular probe to return that pair. -/
theorem probe_iff {p q C : ℕ} (unit : p.Coprime 6) (proper : 1<p) (ordered : p≤q)
    (hq : q≤C) : probe C (p*q)=some (p,q) ↔ (C-p)*(C-q)<C*weightedStride (p*q) 1 1 := by
  have pos : 0<C := by omega
  constructor
  · intro hit
    unfold probe at hit
    generalize hxy : decode C (p*q)=pair at hit
    obtain ⟨x,y⟩ := pair
    dsimp only at hit
    split at hit
    next h =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hit)
      rw [h.2.2.2.2,offset_mod unit (ordered.trans hq) hq]
      exact Nat.mod_lt _ (Nat.mul_pos pos (Nat.gcd_pos_of_pos_left _ (by decide : 0<24)))
    next => contradiction
  · intro small
    simp [probe,recover unit pos ordered hq small,proper,ordered,hq,exact_residue unit (ordered.trans hq) hq small]

private theorem sum_lower {p q C h : ℕ} (hh : h≤C) (near : (C-h)^2≤p*q) :
    2*(C-h)≤p+q := by
  zify [hh] at near ⊢
  by_contra! bad
  have lower : 0≤(p:ℤ)+q := by positivity
  nlinarith only [near,sq_nonneg ((p:ℤ)-q),
    mul_pos (sub_pos.mpr bad) (by omega : 0<2*((C:ℤ)-h)+(p+q))]

/-- A sufficient condition that can be checked from the product and the endpoint. -/
theorem public_bound {p q C h : ℕ} (hp : p≤C) (hq : q≤C) (hh : h≤C)
    (near : (C-h)^2≤p*q) : (C-p)*(C-q)≤h^2 := by
  have sums := sum_lower hh near
  zify [hp,hq,hh] at sums ⊢
  have upper : (C:ℤ)-p + (C-q) ≤ 2*h := by linarith only [sums]
  have positive : 0 ≤ (2*(h:ℤ)-((C-p)+(C-q)))*(2*h+((C-p)+(C-q))) :=
    mul_nonneg (by linarith only [upper]) (by omega)
  nlinarith only [positive,sq_nonneg (((C:ℤ)-p)-(C-q))]

theorem recover_from_product {p q C h : ℕ} (unit : p.Coprime 6) (pos : 0<C)
    (ordered : p≤q) (hq : q≤C) (hh : h≤C) (near : (C-h)^2≤p*q)
    (budget : h^2<C*weightedStride (p*q) 1 1) : decode C (p*q)=(p,q) :=
  recover unit pos ordered hq ((public_bound (ordered.trans hq) hq hh near).trans_lt budget)

private theorem four_le {p q : ℕ} (op : Odd p) (oq : Odd q) :
    4 ≤ weightedStride (p*q) 1 1 := by
  obtain ⟨j,hj⟩ := op.mul oq
  have div : 4 ∣ weightedStride (p*q) 1 1 := by
    apply Nat.dvd_gcd (by decide)
    exact ⟨j+1,by rw [one_mul,hj]; ring⟩
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by decide)) div

set_option exponentiation.threshold 4096

/-- The public prefix also bounds the work of the ordinary Fermat baseline. -/
theorem ordinary_distance {p q C h m k : ℕ} (ordered : p≤q) (hq : q≤C)
    (hh : h≤C) (near : (C-h)^2≤p*q) (midpoint : p+q=2*m)
    (bound : h^2 < (k+1)*(2*(C-h)+(k+1))) : m ≤ ceilSqrt (p*q)+k := by
  let d := ceilSqrt (p*q)
  have cap : p*q≤d^2 := ceilSqrt_le_iff.mp le_rfl
  have start : C-h≤d := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (near.trans cap)
  have sums := sum_lower hh near
  have gap : q-p≤2*h := by omega
  have gapsq := Nat.pow_le_pow_left gap 2
  by_contra! above
  have beyond : d+(k+1)≤m := by change d+k<m at above; omega
  have md := Nat.pow_le_pow_left beyond 2
  have lower := Nat.mul_le_mul_left (k+1) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 start) (k+1))
  zify [ordered,hh] at bound cap md lower gapsq midpoint
  nlinarith only [bound,cap,md,lower,gapsq,congrArg (fun x : ℤ => x^2) midpoint]

/-- If a 2048-bit balanced input begins with 511 ones, one test suffices. -/
theorem first_511_bits {p q : ℕ} (unit : p.Coprime 6) (oq : Odd q)
    (ordered : p≤q) (hq : q≤2^1024) (leading : 2^2048-2^1537≤p*q) :
    decode (2^1024) (p*q)=(p,q) := by
  have op := Nat.coprime_two_right.mp (unit.of_dvd_right (by decide : 2∣6))
  apply recover_from_product (h:=2^512+1) unit (by decide) ordered hq (by decide +kernel)
  · exact (by decide +kernel : (2^1024-(2^512+1):ℕ)^2≤2^2048-2^1537).trans leading
  · exact (by decide +kernel : (2^512+1:ℕ)^2<2^1024*4).trans_le
      (Nat.mul_le_mul_left _ (four_le op oq))

/-- A larger stride gives a wider publicly recognizable interval. -/
theorem first_509_bits {p q : ℕ} (unit : p.Coprime 6)
    (ordered : p≤q) (hq : q≤2^1024) (stride : weightedStride (p*q) 1 1=24)
    (leading : 2^2048-2^1539≤p*q) : decode (2^1024) (p*q)=(p,q) := by
  apply recover_from_product (h:=4*2^512+9) unit (by decide) ordered hq (by decide +kernel)
  · exact (by decide +kernel : (2^1024-(4*2^512+9):ℕ)^2≤2^2048-2^1539).trans leading
  · rw [stride]; decide +kernel

theorem ordinary_511_bits {p q m : ℕ} (ordered : p≤q) (hq : q≤2^1024)
    (leading : 2^2048-2^1537≤p*q) (midpoint : p+q=2*m) : ceilSqrt (p*q)=m := by
  apply le_antisymm
  · apply ceilSqrt_le_iff.mpr
    zify at midpoint ⊢
    nlinarith only [sq_nonneg ((p:ℤ)-q),congrArg (fun x : ℤ => x^2) midpoint]
  · exact ordinary_distance (h:=2^512+1) (k:=0) ordered hq (by decide +kernel)
      ((by decide +kernel : (2^1024-(2^512+1):ℕ)^2≤2^2048-2^1537).trans leading)
      midpoint (by decide +kernel)

theorem ordinary_509_bits {p q m : ℕ} (ordered : p≤q) (hq : q≤2^1024)
    (leading : 2^2048-2^1539≤p*q) (midpoint : p+q=2*m) : m≤ceilSqrt (p*q)+8 :=
  ordinary_distance (h:=4*2^512+9) ordered hq (by decide +kernel)
    ((by decide +kernel : (2^1024-(4*2^512+9):ℕ)^2≤2^2048-2^1539).trans leading)
    midpoint (by decide +kernel)

end PrimeFactors.EndpointOffsetProduct
