import PrimeFactors.PrimitiveIntervalPrecision
import Mathlib.Data.Nat.Factorization.Basic

/-! Extrapolating the gcd mean of a whole period to the public interval gives
a biased reading of the signed aggregate. All sums and errors here are exact. -/
namespace PrimeFactors.PrimitiveIntervalPeriodMean

open Finset PrimitiveIntervalMoment PrimitiveIntervalPrecision

/-- The actual mean of the positive gcds in one complete period. -/
noncomputable def mean (n : ℕ) : ℚ := (∑ t ∈ Ioc 0 n, (n.gcd t : ℚ)) / n

/-- Substitute the full-period mean for the gcd at each of the B² pairs. -/
noncomputable def prediction (n b : ℕ) : ℚ := (b : ℚ)^2 * (2 - mean n)

private theorem local_gcd {p t : ℕ} (prime : p.Prime) :
    t.gcd p = if p ∣ t then p else 1 := by
  split_ifs with h
  · exact Nat.gcd_eq_right h
  · exact (prime.coprime_iff_not_dvd.mpr h).symm.gcd_eq_one

private theorem gcd_layers {p q t : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p ≠ q) :
    ((p*q).gcd t : ℚ) = 1 + (if p ∣ t then (p:ℚ)-1 else 0) +
      (if q ∣ t then (q:ℚ)-1 else 0) +
      (if p*q ∣ t then ((p:ℚ)-1)*((q:ℚ)-1) else 0) := by
  have cop := (Nat.coprime_primes pp qp).mpr ne
  have both : p*q ∣ t ↔ p ∣ t ∧ q ∣ t :=
    ⟨fun h => ⟨(dvd_mul_right ..).trans h,(dvd_mul_left ..).trans h⟩,
      fun h => cop.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  rw [Nat.gcd_comm, cop.gcd_mul,local_gcd pp,local_gcd qp]
  by_cases pd : p ∣ t <;> by_cases qd : q ∣ t <;> simp [both,pd,qd]
  ring

/-- In one full period the three divisibility corrections occur q, p and
one times, respectively. This proves the semiprime case of Pillai's sum. -/
theorem period_sum {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p ≠ q) :
    ∑ t ∈ Ioc 0 (p*q), ((p*q).gcd t : ℚ) = (2*(p:ℚ)-1)*(2*(q:ℚ)-1) := by
  simp_rw [gcd_layers pp qp ne, sum_add_distrib]
  simp only [←sum_filter,sum_const,Nat.Ioc_filter_dvd_card_eq_div,Nat.card_Ioc,
    Nat.sub_zero,nsmul_eq_mul,Nat.mul_div_cancel_left _ pp.pos,
    Nat.mul_div_cancel _ qp.pos,Nat.div_self (Nat.mul_pos pp.pos qp.pos),Nat.cast_one,
    Nat.cast_mul]
  ring

theorem mean_eq {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p ≠ q) :
    mean (p*q) = (2*(p:ℚ)-1)*(2*(q:ℚ)-1)/(p*q) := by
  rw [mean,period_sum pp qp ne,Nat.cast_mul]

/-- Even the complete-period mean depends on the unknown sum. -/
theorem mean_and_sum {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p ≠ q) :
    mean (p*q)*((p:ℚ)*q) = 4*((p:ℚ)*q)-2*(p+q)+1 := by
  have pos : 0 < (p:ℚ)*q := by exact_mod_cast Nat.mul_pos pp.pos qp.pos
  rw [mean_eq pp qp ne,div_mul_cancel₀ _ pos.ne']
  ring

theorem mean_lower {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p < q)
    (large : 11 ≤ p) : 7/2 ≤ mean (p*q) := by
  rw [mean_eq pp qp ord.ne, le_div_iff₀ (by exact_mod_cast Nat.mul_pos pp.pos qp.pos)]
  have hp : (11:ℚ) ≤ p := by exact_mod_cast large
  have hq : (11:ℚ) ≤ q := by exact_mod_cast large.trans ord.le
  nlinarith only [hp,hq,mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq)]

/-- Completing the squares at the two prime diagonals. -/
theorem value_squares (p q b : ℤ) :
    value (p*q) b (p+q) = (p-b-1)^2+(q-b-1)^2-b^2 := by unfold value; ring

theorem value_lower (p q b : ℤ) : -(b^2) ≤ value (p*q) b (p+q) := by
  rw [value_squares]
  linarith only [sq_nonneg (p-b-1),sq_nonneg (q-b-1)]

/-- The downward error is at least half the area. The public interval
value is the genuine signed aggregate by PrimitiveIntervalMoment.aggregate_value. -/
theorem shortfall {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p < q)
    (large : 11 ≤ p) (b : ℕ) :
    (b:ℚ)^2/2 ≤ (value (p*q) b (p+q) : ℚ) - prediction (p*q) b := by
  rw [value_squares,prediction]
  push_cast
  have h := mul_le_mul_of_nonneg_left (mean_lower pp qp ord large) (sq_nonneg (b:ℚ))
  nlinarith only [h,sq_nonneg ((p:ℚ)-b-1),sq_nonneg ((q:ℚ)-b-1)]

/-- The error exceeds the guaranteed public tolerance once B exceeds eight. -/
theorem exceeds_tolerance {p q b : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p < q)
    (large : 11 ≤ p) (length : 8 < b) :
    4*(b:ℚ) < (value (p*q) b (p+q) : ℚ) - prediction (p*q) b := by
  have hb : (8:ℚ) < b := by exact_mod_cast length
  apply lt_of_lt_of_le _ (shortfall pp qp ord large b)
  nlinarith only [mul_pos (sub_pos.mpr hb) (by linarith : (0:ℚ)<b)]

/-- Flooring the extrapolation gives a reading below the actual rounding
cell for every public cutoff of at least 24. -/
theorem floor_round_wrong {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p < q)
    (balanced : q < 2*p) (large : 11 ≤ p) (length : 24 ≤ cutoff (p*q)) :
    rounded (p*q) (cutoff (p*q)) ⌊prediction (p*q) (cutoff (p*q))⌋ ≠ p+q := by
  let b := cutoff (p*q)
  change 24 ≤ b at length
  change rounded (p*q) b ⌊prediction (p*q) b⌋ ≠ p+q
  obtain ⟨lo,hi⟩ := cutoff_bounds pp.pos balanced
  change b < p at lo
  change q ≤ 2*b+1 at hi
  have odd := (pp.odd_of_ne_two (by omega)).mul (qp.odd_of_ne_two (by omega))
  have c := SumIntervalExclusion.sum_congruence (Nat.odd_iff.mp odd)
  have residue : ((p:ℤ)+q)%4=(((p:ℤ)*q)+1)%4 := by exact_mod_cast c
  intro got
  have lower := ((round_iff (by omega) residue).mp got).1
  have lowerQ : -(4*((p:ℚ)+q-b-1)-8) ≤
      (⌊prediction (p*q) b⌋ : ℚ) - (value (p*q) b (p+q) : ℚ) := by exact_mod_cast lower
  have hi' : (p:ℚ)+q-b-1 ≤ 3*b := by exact_mod_cast (show (p:ℤ)+q-b-1 ≤ 3*b by omega)
  have hb : (24:ℚ) ≤ b := by exact_mod_cast length
  have square := mul_nonneg (sub_nonneg.mpr hb) (show (0:ℚ)≤b by positivity)
  linarith only [shortfall pp qp ord large b,Int.floor_le (prediction (p*q) b),lowerQ,hi',square]

set_option exponentiation.threshold 4096 in
theorem full_width_round_wrong {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p < q)
    (balanced : q < 2*p) (bits : 2^2047 ≤ p*q) :
    rounded (p*q) (cutoff (p*q)) ⌊prediction (p*q) (cutoff (p*q))⌋ ≠ p+q := by
  have length := (by decide +kernel : 24 ≤ 2^1023).trans (full_width_cutoff bits)
  have below := (cutoff_bounds pp.pos balanced).1
  exact floor_round_wrong pp qp ord balanced (by omega) length

/-- The exact reading at 143 is −44. Flooring the extrapolation gives −107,
which rounds to the wrong sum 20, four below 11+13. -/
theorem control143 :
    mean 143 = 525/143 ∧ prediction 143 8 = -15296/143 ∧
    value 143 8 24 = -44 ∧ ⌊prediction 143 8⌋ = -107 ∧ rounded 143 8 (-107) = 20 := by
  have m := mean_eq (p:=11) (q:=13) (by decide) (by decide) (by decide)
  norm_num at m
  rw [prediction,m]
  norm_num [value,rounded]

end PrimeFactors.PrimitiveIntervalPeriodMean
