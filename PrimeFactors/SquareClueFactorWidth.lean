import PrimeFactors.ProductDeficitBand
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic

/-! A lower bound for the width of the public factor-sum interval after both
factor endpoints are imposed, and an exact interpretation in terms of the
ordered real roots of the factor quadratic. -/
namespace PrimeFactors.SquareClueFactorWidth

/-- At an upper bound Q for both factors, every one of the first W positions
above floor(sqrt(4n)) passes the upper-endpoint sum test if the smaller factor
has a sufficient margin from Q. -/
theorem upper_endpoint {p q Q M W s : ℕ} (pos : 0<Q) (top : q≤Q)
    (margin : p+4*M≤Q) (budget : Q*W≤M^2) (slab : s≤(4*(p*q)).sqrt+W) :
    s≤Q+(p*q)/Q := by
  let w := (4*(p*q)).sqrt
  have under : w^2≤4*(p*q) := Nat.sqrt_le' _
  have upper : p*q≤p*Q := Nat.mul_le_mul_left p top
  have large : M≤Q := by omega
  have low : p*q≤(Q-M)^2 := by
    obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le margin
    rw [ha] at upper ⊢
    rw [show p+4*M+a-M=p+3*M+a by omega]
    nlinarith only [upper]
  have wr : w≤2*(Q-M) := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    (under.trans ((Nat.mul_le_mul_left 4 low).trans_eq (by ring)))
  have gap : w+2*M ≤ 2*Q := by omega
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le gap
  have spare : Q*w+M^2≤Q^2+p*q := by
    zify at under hd ⊢
    nlinarith only [under,congrArg (fun t : ℤ => t^2) hd,
      congrArg (fun t : ℤ => t*w) hd, mul_nonneg (Int.natCast_nonneg M) (Int.natCast_nonneg d),
      sq_nonneg (d:ℤ)]
  have lifted := Nat.mul_le_mul_left Q slab
  have test : s*Q≤Q*Q+p*q := by
    change Q*s≤Q*(w+W) at lifted
    rw [Nat.mul_add] at lifted
    nlinarith only [spare,budget,lifted]
  calc
    s ≤ (Q*Q+p*q)/Q := (Nat.le_div_iff_mul_le pos).mpr test
    _ = Q+(p*q)/Q := by rw [Nat.mul_add_div pos]

/-- For products above A*Q, the upper-factor endpoint is the tighter one.
Here Q=2A−1 is the largest integer of the advertised factor width. -/
theorem both_endpoints {n A Q s : ℕ} (ap : 0<A) (span : A≤Q)
    (full : A*Q≤n) (top : s≤Q+n/Q) : s≤A+n/A := by
  have qp := ap.trans_le span
  have h := Nat.mul_le_mul_right Q top
  rw [Nat.add_mul] at h
  have bound : (s:ℤ)*Q ≤ (Q:ℤ)^2+n := by
    have t := Nat.div_mul_le_self n Q
    zify at h t
    nlinarith only [h,t]
  have cap : s*A≤A*A+n := by
    zify at ap qp span full ⊢
    apply le_of_mul_le_mul_right (a:=(Q:ℤ)) _ qp
    nlinarith only [mul_le_mul_of_nonneg_right bound ap.le,
      mul_nonneg (sub_nonneg.mpr span) (sub_nonneg.mpr full)]
  calc
    s ≤ (A*A+n)/A := (Nat.le_div_iff_mul_le ap).mpr cap
    _ = A+n/A := by rw [Nat.mul_add_div ap]

/-- For a product in the advertised box, the integer ceiling on an integer
sum is equivalent to both real roots lying between A and the inclusive upper
endpoint 2A−1. Product and sum specify the roots of the factor quadratic. -/
theorem sumCap_iff_real_roots {n A s : ℕ} {x y : ℝ} (ap : 0<A)
    (lo : A^2≤n) (hi : n≤(2*A-1)^2) (order : x≤y)
    (product : x*y=(n:ℝ)) (sum : x+y=(s:ℝ)) :
    s≤ProductDeficitBand.sumCap n A ↔ (A:ℝ)≤x ∧ y≤((2*A-1:ℕ):ℝ) := by
  let Q := 2*A-1
  have qp : 0<Q := by dsimp [Q]; omega
  have ar : 0<(A:ℝ) := by exact_mod_cast ap
  have qr : 0<(Q:ℝ) := by exact_mod_cast qp
  have left : (A:ℝ)^2≤x*y := by rw [product]; exact_mod_cast lo
  have right : x*y≤(Q:ℝ)^2 := by rw [product]; exact_mod_cast hi
  have xp : 0<x := by
    apply lt_of_not_ge
    intro neg
    have sn : (0:ℝ)≤s := Nat.cast_nonneg _
    have yp : 0≤y := by linarith only [sum,neg,sn]
    exact (not_le_of_gt ((sq_pos_of_pos ar).trans_le left)) (mul_nonpos_of_nonpos_of_nonneg neg yp)
  have yp := xp.trans_le order
  have test {K : ℕ} (kp : 0<K) :
      s≤K+n/K ↔ (x+y)*(K:ℝ)≤(K:ℝ)^2+x*y := by
    have natTest : s≤K+n/K ↔ s*K≤K^2+n := by
      rw [←Nat.mul_add_div kp,Nat.le_div_iff_mul_le kp,pow_two]
    rw [sum,product]
    exact_mod_cast natTest
  rw [ProductDeficitBand.sumCap,le_min_iff]
  change (s≤A+n/A ∧ s≤Q+n/Q) ↔ (A:ℝ)≤x ∧ y≤(Q:ℝ)
  rw [test ap,test qp]
  constructor
  · rintro ⟨low,high⟩
    constructor
    · apply le_of_not_gt
      intro out
      have inward : (A:ℝ)<y := by
        apply lt_of_not_ge
        intro contrary
        have bad := (mul_le_mul_of_nonneg_left contrary xp.le).trans_lt (mul_lt_mul_of_pos_right out ar)
        nlinarith only [bad,left]
      nlinarith only [low,mul_neg_of_neg_of_pos (sub_neg.mpr out) (sub_pos.mpr inward)]
    · apply le_of_not_gt
      intro out
      have inward : x<(Q:ℝ) := by
        apply lt_of_not_ge
        intro contrary
        have bad := (mul_lt_mul_of_pos_left out qr).trans_le (mul_le_mul_of_nonneg_right contrary yp.le)
        nlinarith only [bad,right]
      nlinarith only [high,mul_neg_of_neg_of_pos (sub_neg.mpr inward) (sub_pos.mpr out)]
  · rintro ⟨xlo,yhi⟩
    constructor
    · nlinarith only [mul_nonneg (sub_nonneg.mpr xlo) (sub_nonneg.mpr (xlo.trans order))]
    · nlinarith only [mul_nonneg (sub_nonneg.mpr (order.trans yhi)) (sub_nonneg.mpr yhi)]

end PrimeFactors.SquareClueFactorWidth
