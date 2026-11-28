import PrimeFactors.CircleMarkMidcutReadout

/-! A signed total known within one cutoff determines the smaller odd prime.
This gives a tolerance for a supplied count or for a normalized reading. -/
namespace PrimeFactors.CircleMarkMidcutPrecision

open Finset CircleMarkMidcutReadout

/-- Round the supplied total to the nearest even multiple of the cutoff,
then recover the corresponding odd candidate factor. -/
noncomputable def oddFactor (n : ℕ) (total : ℚ) : ℤ :=
  1+2*⌊total/(2*(cutoff n:ℚ))+1/2⌋

theorem correct {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) {x : ℚ}
    (err : |x-(imbalance (p*q):ℚ)| < (cutoff (p*q):ℚ)) :
    oddFactor (p*q) x = (p:ℤ) := by
  let k := cutoff (p*q)
  have P := hp.out.two_le
  have kp : 0<k := (show 0<(p-1)/2 by omega).trans_le (between order).1
  have den : 0<2*(k:ℚ) := by positivity
  obtain ⟨u,pu⟩ := hp.out.odd_of_ne_two op
  have mass : (imbalance (p*q):ℚ) = (k:ℚ)*((p:ℚ)-1) := by
    exact_mod_cast imbalance_eq order op oq
  have pp : (p:ℚ) = 2*u+1 := by exact_mod_cast pu
  rw [mass,pp] at err
  obtain ⟨lower,upper⟩ := abs_lt.mp err
  change -(k:ℚ)<_ at lower
  change _<(k:ℚ) at upper
  have lo : (u:ℚ)-1/2 < x/(2*k) := (lt_div_iff₀ den).mpr (by linarith only [lower])
  have hi : x/(2*k) < (u:ℚ)+1/2 := (div_lt_iff₀ den).mpr (by linarith only [upper])
  have rounded : ⌊x/(2*k)+1/2⌋=(u:ℤ) := by
    apply Int.floor_eq_iff.mpr
    push_cast
    exact ⟨by linarith,by linarith⟩
  change 1+2*⌊x/(2*k)+1/2⌋=(p:ℤ)
  rw [rounded,pu]
  push_cast
  ring

/-- The unchecked residue classes each change the total by at most one. -/
theorem omitted_bound (n : ℕ) [NeZero n] (seen : Finset (ZMod n)) :
    |(∑ t∈seen, score n t)-imbalance n| ≤ (seenᶜ.card:ℤ) := by
  have add := sum_add_sum_compl seen (score n)
  have diff : (∑ t∈seen, score n t)-imbalance n = -(∑ t∈seenᶜ,score n t) := by
    unfold imbalance
    linarith only [add]
  rw [diff,abs_neg]
  calc _ ≤ ∑ t∈seenᶜ,|score n t| := abs_sum_le_sum_abs ..
       _ ≤ ∑ _t∈seenᶜ,(1:ℤ) := by
         apply sum_le_sum
         intro t _
         unfold score
         split
         · decide
         · split <;> decide
       _ = _ := by simp

/-- Missing fewer than K residues preserves a deterministically certified rounding. -/
theorem omitted_recovery {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (seen : Finset (ZMod (p*q)))
    (few : seenᶜ.card < cutoff (p*q)) :
    oddFactor (p*q) (∑ t∈seen, (score (p*q) t:ℚ)) = (p:ℤ) := by
  apply correct order op oq
  have e := (omitted_bound (p*q) seen).trans_lt (Int.ofNat_lt.mpr few)
  exact_mod_cast e

set_option exponentiation.threshold 8192 in
/-- At full width, the signed total can be read from an all-residue average
with a scaling factor strictly below 2^1026. -/
theorem full_scale {p q : ℕ} [Fact p.Prime]
    (lower : 2^1023≤p) (order : p<q) (upper : q<2^1024) :
    ((p*q:ℕ):ℚ)*(1/2^1026)<(cutoff (p*q):ℚ) := by
  have big := (by decide +kernel : 2<2^1023).trans_le lower
  have K : 2^1022 ≤ cutoff (p*q) := by
    apply le_trans _ (between order).1
    have odd := Fact.out (p:=p.Prime) |>.odd_of_ne_two big.ne'
    obtain ⟨u,hu⟩ := odd
    have scale : (2:ℕ)^1023=2*2^1022 := by decide +kernel
    omega
  have cap : p*q < 2^2048 := (Nat.mul_lt_mul_of_pos_right (order.trans upper) (by omega)).trans_le
    ((Nat.mul_le_mul_left (2^1024) upper.le).trans_eq (by decide +kernel))
  have kk : (2:ℚ)^1022 ≤ (cutoff (p*q):ℚ) := by exact_mod_cast K
  have ncap : ((p*q:ℕ):ℚ)<2^2048 := by exact_mod_cast cap
  apply lt_of_lt_of_le _ kk
  rw [mul_one_div,div_lt_iff₀ (by positivity : (0:ℚ)<2^1026)]
  rw [←pow_add]
  exact ncap

set_option exponentiation.threshold 8192 in
/-- An absolute error below 2^-1026 in the average of the signed scores over
all residues suffices at two 1024-bit primes. -/
theorem full_reading {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lower : 2^1023≤p) (order : p<q) (upper : q<2^1024) {y : ℚ}
    (err : |y-(imbalance (p*q):ℚ)/(p*q:ℕ)| < 1/(2:ℚ)^1026) :
    oddFactor (p*q) (((p*q:ℕ):ℚ)*y) = (p:ℤ) := by
  have big := (by decide +kernel : 2<2^1023).trans_le lower
  have P : 0<(p*q:ℕ) := Nat.mul_pos (by omega) (by omega)
  have N : 0<((p*q:ℕ):ℚ) := by exact_mod_cast P
  have precision := full_scale lower order upper
  apply correct order big.ne' (big.trans order).ne'
  have base : ((p*q:ℕ):ℚ)*y-(imbalance (p*q):ℚ) =
      ((p*q:ℕ):ℚ)*(y-(imbalance (p*q):ℚ)/(p*q:ℕ)) := by
    rw [mul_sub,mul_comm ((p*q:ℕ):ℚ) (_ / _),div_mul_cancel₀ _ N.ne']
  rw [base,abs_mul,abs_of_pos N]
  exact (mul_lt_mul_of_pos_left err N).trans precision

/-- For 187 the exact total is 60 and K=6. An error of exactly six can
round to the next odd candidate. -/
theorem sharp_example : oddFactor 187 65 = 11 ∧ oddFactor 187 66 = 13 := by
  have k : cutoff 187=6 := by decide
  norm_num [oddFactor,k]

end PrimeFactors.CircleMarkMidcutPrecision
