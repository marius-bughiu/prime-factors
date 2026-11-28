import PrimeFactors.CircleMarkChangedPrimeSum

/-! A lower bound on the variance of the unsigned change estimator at the
product-only prefix length. The proof uses integer square-root bounds and
rational inequalities. -/

namespace PrimeFactors.CircleMarkUnsignedVariance

open CircleMarkChangedPrimeSum

/-- One-draw variance when reading the prime sum in its original units. -/
noncomputable def variance (n : ℕ) [NeZero n] (d : ℕ) : ℚ :=
  (tally n d : ℚ) * ((n : ℚ) - tally n d) / (d : ℚ)^2

theorem length_square (n : ℕ) : 8*(publicLength n)^2 ≤ n := by
  have stage : 2*publicLength n ≤ (n/2).sqrt := by unfold publicLength; omega
  have sq := (Nat.pow_le_pow_left stage 2).trans (Nat.sqrt_le' (n/2))
  exact (Nat.le_div_iff_mul_le (by decide : 0<2)).mp sq |>.trans' (by ring_nf; exact le_rfl)

theorem length_square_succ (n : ℕ) : n < 8*(publicLength n+1)^2 := by
  have stage : (n/2).sqrt+1 ≤ 2*(publicLength n+1) := by unfold publicLength; omega
  have sq := (Nat.lt_succ_sqrt' (n/2)).trans_le (Nat.pow_le_pow_left stage 2)
  have fin := (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mp sq
  nlinarith only [fin]

/-- The matching upper estimate V/N < 2(1+1/d)² for the public prefix. -/
theorem public_upper (n : ℕ) [NeZero n] (pos : 0 < publicLength n) :
    let d := publicLength n
    variance n d * (d:ℚ)^2 < 2*(n:ℚ)*((d:ℚ)+1)^2 := by
  let d := publicLength n
  have cap : (n:ℚ)<8*((d:ℚ)+1)^2 := by exact_mod_cast length_square_succ n
  have dp : (d:ℚ)≠0 := by exact_mod_cast pos.ne'
  have N : (0:ℚ)<n := by exact_mod_cast NeZero.pos n
  change variance n d * (d:ℚ)^2 < _
  rw [variance, div_mul_cancel₀ _ (pow_ne_zero _ dp)]
  change (tally n d:ℚ)*((n:ℚ)-tally n d)<2*(n:ℚ)*((d:ℚ)+1)^2
  nlinarith only [mul_lt_mul_of_pos_left cap N, sq_nonneg ((n:ℚ)-2*(tally n d:ℚ))]

private theorem range_of_sum {p q : ℚ} (p3 : 3 ≤ p) (q5 : 5 ≤ q) (order : p < q)
    (bal : q < 2*p) : 2*(p*q) < (p+q-2)^2 ∧ 2*(p+q-2)^2 < 9*(p*q) := by
  have left : 3*(p+q) ≤ 4*(p+q-2) := by linarith
  have square := mul_self_le_mul_self (by linarith : 0≤3*(p+q)) left
  have pos := mul_pos (by linarith : 0<p) (by linarith : 0<q)
  have orderProduct := mul_pos (sub_pos.mpr bal) (by linarith : 0<2*q-p)
  constructor
  · nlinarith only [square, sq_nonneg (p-q),pos]
  · nlinarith only [orderProduct,p3,q5]

private theorem bound {n a d : ℚ} (dp : 0 < d) (ap : 0 ≤ a) (np : 0 < n)
    (length : 8*d^2 ≤ n) (lo : 2*n < a^2) (hi : 2*a^2 < 9*n) :
    15*n/8 < d*(a-d)*(n-d*(a-d))/d^2 := by
  have four : 4*d < a := by
    by_contra! bad
    have sq := mul_self_le_mul_self ap bad
    nlinarith only [sq,lo,length]
  have enough : 15*n*d < 8*(a-d)*(n-d*(a-d)) := by
    by_cases six : a < 6*d
    · have left := mul_nonneg (by linarith : 0≤8*a-23*d) (sub_nonneg.mpr length)
      have right := mul_pos (mul_pos dp (sub_pos.mpr four)) (sub_pos.mpr six)
      nlinarith only [left,right]
    · have product := mul_nonneg (by linarith : 0≤a-6*d) (by linarith : 0≤5*a-6*d)
      have misses : 3*n < 8*(n-d*(a-d)) := by nlinarith only [product,hi]
      have growth := mul_lt_mul_of_pos_left misses (by linarith : 0<a-d)
      have hits := mul_le_mul_of_nonneg_right (by linarith : 5*d≤a-d) np.le
      nlinarith only [growth,hits]
  apply (lt_div_iff₀ (sq_pos_of_pos dp)).mpr
  nlinarith only [mul_lt_mul_of_pos_right enough dp]

/-- For the public prefix, every balanced pair of distinct odd primes has
one-draw variance strictly larger than 15N/8. -/
theorem public_lower {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (order : p < q)
    (bal : q < 2*p) (op : p ≠ 2) (oq : q ≠ 2) :
    15*((p*q : ℕ) : ℚ)/8 < variance (p*q) (publicLength (p*q)) := by
  let d := publicLength (p*q)
  have p3 : 3 ≤ p := by have := hp.out.two_le; omega
  have q5 : 5 ≤ q := by
    obtain ⟨v,hv⟩ := hq.out.odd_of_ne_two oq
    omega
  obtain ⟨dp,cap⟩ := public_safe order bal op
  obtain ⟨lo,hi⟩ := range_of_sum (p:= (p:ℚ)) (q:= (q:ℚ)) (by exact_mod_cast p3)
    (by exact_mod_cast q5) (by exact_mod_cast order) (by exact_mod_cast bal)
  have length : 8*(d:ℚ)^2 ≤ (p:ℚ)*q := by exact_mod_cast (length_square (p*q))
  have pos : 0 < (d:ℚ) := by exact_mod_cast dp
  have P : 3 ≤ (p:ℚ) := by exact_mod_cast p3
  have Q : 5 ≤ (q:ℚ) := by exact_mod_cast q5
  have room : 2+d ≤ p+q := by change d≤(p-1)/2 at cap; omega
  have key := bound pos (by linarith : (0:ℚ) ≤ p+q-2) (by positivity) length lo hi
  change 15*((p*q : ℕ) : ℚ)/8 < variance (p*q) d
  rw [variance,tally_eq order op oq cap, show p+q-2-d=p+q-(2+d) by omega]
  push_cast [Nat.cast_sub room]
  convert key using 1
  ring

end PrimeFactors.CircleMarkUnsignedVariance
