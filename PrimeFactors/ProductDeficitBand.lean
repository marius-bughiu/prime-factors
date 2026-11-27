import PrimeFactors.CenteredSumQuartic
import PrimeFactors.PowerImageWidth

/-! Bounds on p+q−1 using only the odd product and the advertised common factor width.
The upper bound uses both endpoints and the lower bound one integer square root. -/
namespace PrimeFactors.ProductDeficitBand

/-- A is the smallest integer of the advertised factor width. -/
def sumCap (N A : ℕ) := min (A+N/A) ((2*A-1)+N/(2*A-1))
def lower (N A : ℕ) := max (2*A+1) (2*ceilSqrt N-1)
def upper (N A : ℕ) := min (4*A) (2*(sumCap N A/2))

private theorem left_cap {p q A : ℕ} (apos : 0<A) (lp : A≤p) (lq : A≤q) :
    p+q ≤ A+p*q/A := by
  have cross : (p+q)*A≤p*q+A*A := by
    zify at lp lq ⊢
    nlinarith only [mul_nonneg (sub_nonneg.mpr lp) (sub_nonneg.mpr lq)]
  have divided := (Nat.le_div_iff_mul_le apos).mpr cross
  rwa [Nat.add_mul_div_right _ _ apos,Nat.add_comm (p*q/A)] at divided

/-- The true deficit lies in this half-open interval for all same-width odd pairs. -/
theorem contains {p q A : ℕ} (ap : 0<A) (even : Even A) (po : Odd p) (qo : Odd q)
    (pl : A≤p) (ql : A≤q) (pu : p<2*A) (qu : q<2*A) :
    lower (p*q) A ≤ p+q-1 ∧ p+q-1 < upper (p*q) A := by
  obtain ⟨a,ha⟩ := po
  obtain ⟨b,hb⟩ := qo
  obtain ⟨c,hc⟩ := even
  have sr : ceilSqrt (p*q) ≤ a+b+1 := ceilSqrt_le_iff.mpr (by
    rw [ha,hb]
    zify
    nlinarith only [sq_nonneg ((a:ℤ)-b)])
  have cap : p+q≤sumCap (p*q) A := le_min (left_cap ap pl ql)
    (CenteredSumQuartic.sum_upper rfl (by omega) (by omega) (by omega))
  dsimp only [lower,upper]
  omega

theorem dyadic {N A : ℕ} : upper N A ≤ 2*lower N A := by
  have lo := le_max_left (2*A+1) (2*ceilSqrt N-1)
  have hi := min_le_left (4*A) (2*(sumCap N A/2))
  dsimp only [upper,lower]
  omega

private theorem endpoint_step {N B : ℕ} (bp : 0<B) (size : N ≤ B*B) :
    B+N/B ≤ B+1+N/(B+1) := by
  have k : N/B ≤ B*B/B := Nat.div_le_div_right size
  rw [Nat.mul_div_cancel _ bp] at k
  have h := Nat.div_mul_le_self N B
  cases eq : N/B with
  | zero => exact (by omega : B+0≤B+1).trans (Nat.le_add_right ..)
  | succ j =>
    rw [eq] at k h
    have b := (Nat.le_div_iff_mul_le (Nat.succ_pos B)).mpr
      (show j*(B+1)≤N by nlinarith only [k,h])
    exact (by omega : B+j.succ=B+1+j).le.trans (Nat.add_le_add_left b _)

/-- A rational uniform width bound. Apart from endpoint rounding, at most
11/128 of the original dyadic band remains for every product in the square. -/
theorem length {N A : ℕ} (ap : 0<A) (lo : A*A≤N) (hi : N≤(2*A-1)^2) :
    64*(upper N A-lower N A) ≤ 11*A+64 := by
  let R := 2*ceilSqrt N
  let U := sumCap N A
  have rad : N≤(ceilSqrt N)^2 := ceilSqrt_le_iff.mp le_rfl
  have rsq : 4*N≤R^2 := by dsimp [R]; nlinarith only [rad]
  have ra : 2*A≤R := by
    have h : A≤ceilSqrt N := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      (show A^2≤(ceilSqrt N)^2 by simpa only [pow_two] using lo.trans rad)
    dsimp only [R]; omega
  have rb : R≤4*A := by
    have h := ceilSqrt_le_iff.mpr hi
    dsimp only [R]; omega
  have capA : U*A≤A^2+N := by
    have h := Nat.mul_le_mul_right A (min_le_left (A+N/A) ((2*A-1)+N/(2*A-1)))
    change U*A ≤ _ at h
    nlinarith only [h,Nat.div_mul_le_self N A]
  have capB : U*(2*A) ≤ (2*A)^2+N := by
    have pos : 0<2*A-1 := by omega
    have es := endpoint_step pos (show N≤(2*A-1)*(2*A-1) by simpa only [pow_two] using hi)
    rw [Nat.sub_add_cancel (show 1≤2*A by omega)] at es
    have bound : U≤2*A+N/(2*A) := (min_le_right _ _).trans es
    have h := Nat.mul_le_mul_right (2*A) bound
    nlinarith only [h,Nat.div_mul_le_self N (2*A)]
  have linear : 64*U≤64*R+11*A := by
    by_cases small : 64*R ≤ 181*A
    · have sq : (64*(R-2*A))^2≤(53*A)^2 := Nat.pow_le_pow_left (by omega) 2
      have eq := Nat.sub_add_cancel ra
      have result : (64*U)*A≤(64*R+11*A)*A := by
        rw [←eq] at rsq
        nlinarith only [sq,rsq,capA,congrArg (fun m : ℕ => m*A) eq]
      exact Nat.le_of_mul_le_mul_right result ap
    · have sq : (64*(4*A-R))^2≤(75*A)^2 := Nat.pow_le_pow_left (by omega) 2
      have eq := Nat.sub_add_cancel rb
      have result : (64*U)*A≤(64*R+11*A)*A := by
        nlinarith only [sq,rsq,capB,congrArg (fun m : ℕ => m*A) eq,
          congrArg (fun m : ℕ => m*R) eq,congrArg (fun m : ℕ => m*(4*A-R)) eq]
      exact Nat.le_of_mul_le_mul_right result ap
  have upper_le : upper N A≤U := (min_le_right ..).trans (by dsimp [U]; omega)
  have lower_le : R≤lower N A+1 := by dsimp [lower,R]; omega
  omega

/-- Splitting N into high and low digits in radix B+1 computes division by B
from an addition and at most two comparisons. Both digits fit in [0,B]. -/
theorem radix_quotient {N B h l : ℕ} (bp : 0<B) (split : N=h*(B+1)+l)
    (hh : h≤B) (lh : l≤B) :
    N/B=h+(if h+l<B then 0 else if h+l<2*B then 1 else 2) := by
  have eq : N=(h+l)+B*h := by rw [split]; ring
  rw [eq,Nat.add_mul_div_left _ _ bp,Nat.add_comm]
  congr 1
  split_ifs with first second
  · exact Nat.div_eq_of_lt first
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- Branch-free alternative for the remainder h+l. Division by B+1 is a bit
shift for a radix of two; r may range all the way to 2B. -/
theorem carry_shift {B r : ℕ} (bp : 0<B) (small : r≤2*B) :
    r/B=(r+1+r/(B+1))/(B+1) := by
  by_cases left : r<B
  · rw [Nat.div_eq_of_lt left,Nat.div_eq_of_lt (show r<B+1 by omega)]
    exact (Nat.div_eq_of_lt (show r+1+0<B+1 by omega)).symm
  by_cases middle : r<B+1
  · have eq : r=B := by omega
    subst r
    simp [Nat.div_self bp,Nat.div_eq_of_lt (Nat.lt_succ_self B)]
  have one : r/(B+1)=1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [one]
  by_cases below : r<2*B
  · rw [Nat.div_eq_of_lt_le (k:=1) (by omega) below]
    exact (Nat.div_eq_of_lt_le (k:=1) (by omega) (by omega)).symm
  · have eq : r=2*B := by omega
    subst r
    rw [Nat.mul_div_cancel _ bp]
    exact (Nat.div_eq_of_lt_le (k:=2) (by omega) (by omega)).symm

/-- Rounding the leading root digit requires a table lookup on N/s².
The slack in the inferred ceiling square root is at most s. -/
theorem leading_root {N s j : ℕ} (sp : 0<s) (left : j^2≤N/s^2)
    (right : N/s^2<(j+1)^2) :
    let m := j*s
    let r := m+(if m^2<N then 1 else 0)
    r≤ceilSqrt N ∧ ceilSqrt N≤r+s := by
  have ss : 0<s^2 := Nat.pow_pos sp
  have low : (j*s)^2≤N := by
    simpa only [mul_pow] using (Nat.le_div_iff_mul_le ss).mp left
  have high : N<((j+1)*s)^2 := by
    simpa only [mul_pow] using (Nat.div_lt_iff_lt_mul ss).mp right
  have ceil := ceilSqrt_le_iff.mpr high.le
  have sq := (ceilSqrt_le_iff (n:=N) (a:=ceilSqrt N)).mp le_rfl
  dsimp only
  split_ifs with strict
  · have lt := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp (strict.trans_le sq)
    rw [Nat.add_mul,one_mul] at ceil
    omega
  · have le := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (low.trans sq)
    rw [Nat.add_mul,one_mul] at ceil
    omega

/-- A lower estimate of the ceiling square root can safely be used in the band.
Integer endpoint loss compared to the exact band is at most twice the root error. -/
theorem relaxed {N A r s : ℕ} (low : r≤ceilSqrt N) (high : ceilSqrt N≤r+s) :
    let cheap := max (2*A+1) (2*r-1)
    cheap≤lower N A ∧ lower N A≤cheap+2*s := by
  dsimp [lower]
  omega

/-- Retaining eight leading root bits keeps at most 3/32 of the old
width plus one integer, including uncertainty from omitting the full square root. -/
theorem table_length {N A r s : ℕ} (ap : 0<A) (lo : A*A≤N) (hi : N≤(2*A-1)^2)
    (low : r≤ceilSqrt N) (high : ceilSqrt N≤r+s) (precision : 128*s≤A) :
    64*(upper N A - max (2*A+1) (2*r-1)) ≤ 12*A+64 := by
  have base := length ap lo hi
  have err := (relaxed (A:=A) low high).2
  omega

/-- Refine a leading square from j² to j²+e. The linear chord between
successive square-root values stays below the square root, even after truncation. -/
theorem chord {j e h v : ℕ} (hp : 0<h) (digit : e<2*j+1)
    (value : v=e*h/(2*j+1)) :
    (j*h+v)^2 ≤ (j^2+e)*h^2 ∧
      (0<e → (j*h+v)^2 < (j^2+e)*h^2) := by
  have den : 0<2*j+1 := by omega
  have price : v*(2*j+1) ≤ e*h := value ▸ Nat.div_mul_le_self _ _
  have vh : v<h := by
    rw [value,Nat.div_lt_iff_lt_mul den]
    simpa only [Nat.mul_comm h (2*j+1)] using Nat.mul_lt_mul_of_pos_right digit hp
  have base := Nat.mul_le_mul_right h price
  constructor
  · nlinarith only [base,Nat.mul_le_mul_left v vh.le]
  · intro ep
    by_cases zero : v=0
    · rw [zero,add_zero]
      nlinarith only [Nat.mul_pos ep (Nat.pow_pos hp (n:=2))]
    · nlinarith only [base,Nat.mul_lt_mul_of_pos_left vh (Nat.pos_of_ne_zero zero)]

/-- The chord digit can be computed entirely on the prefix. Scaling it back
to the product's width gives a public square below N, strictly below if e>0. -/
theorem scaled_chord {N j e h v s k : ℕ} (hp : 0<h) (kp : 0<k) (scale : s=h*k)
    (input : N/s^2=j^2+e) (digit : e<2*j+1) (value : v=e*h/(2*j+1)) :
    ((j*h+v)*k)^2≤N ∧ (0<e → ((j*h+v)*k)^2<N) := by
  have root := chord hp digit value
  have base := Nat.div_mul_le_self N (s^2)
  rw [input,scale,mul_pow] at base
  rw [mul_pow]
  constructor
  · exact (Nat.mul_le_mul_right (k^2) root.1).trans (by simpa only [Nat.mul_assoc] using base)
  · intro ep
    exact (Nat.mul_lt_mul_of_pos_right (root.2 ep) (Nat.pow_pos kp)).trans_le
      (by simpa only [Nat.mul_assoc] using base)

/-- With h≤2j the interpolation error is less than three refined cells,
even though the digits of N below the retained prefix are completely unknown. -/
theorem chord_error {N j e h v s k : ℕ} (hp : 0<h) (kp : 0<k) (precision : h≤2*j)
    (scale : s=h*k) (input : N/s^2=j^2+e) (digit : e<2*j+1) (value : v=e*h/(2*j+1)) :
    ceilSqrt N ≤ (j*h+v+3)*k := by
  have den : 0<2*j+1 := by omega
  have vh : v<h := by
    rw [value,Nat.div_lt_iff_lt_mul den]
    simpa only [Nat.mul_comm h (2*j+1)] using Nat.mul_lt_mul_of_pos_right digit hp
  have slack : e*h<(v+1)*(2*j+1) := (Nat.div_lt_iff_lt_mul den).mp (by rw [←value]; omega)
  have square : (j^2+e+1)*h^2≤(j*h+v+3)^2 := by
    nlinarith only [Nat.mul_lt_mul_of_pos_right slack hp,
      Nat.mul_le_mul_right h (show v+1≤h by omega),Nat.mul_le_mul_right h precision]
  have sp : 0<s := scale ▸ Nat.mul_pos hp kp
  have full : N<(j^2+e+1)*s^2 := (Nat.div_lt_iff_lt_mul (Nat.pow_pos sp)).mp (by rw [input]; omega)
  apply ceilSqrt_le_iff.mpr
  rw [scale,mul_pow] at full
  rw [mul_pow]
  exact full.le.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (k^2) square)

end PrimeFactors.ProductDeficitBand
