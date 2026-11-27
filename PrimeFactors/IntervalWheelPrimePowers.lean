import PrimeFactors.IntervalWheelBand

/-! Prime powers at 2, 3 and 5 enlarge the diameter that an eight-modulus
factor-sum wheel can cover with fewer than one million square tests. -/
namespace PrimeFactors.IntervalWheelPrimePowers

open Finset IntervalWheelBand LocalSumMenu PrimitiveIntervalCandidateBand PrimitiveIntervalMoment

def modulus : ℕ := 16 * 9 * 25 * 7 * 11 * 13 * 17 * 19

private def sums16 (r : ZMod 16) : Finset (ZMod 16) :=
  univ.filter fun s => ∃ x : ZMod 16, x*(s-x) = r

/-- For each odd product at most two sums occur modulo sixteen. -/
theorem count_sixteen {n : ℕ} (odd : ¬ 2 ∣ n) : count n 16 ≤ 2 := by
  have parity : (n : ZMod 16).val % 2 = 1 := by
    rw [ZMod.val_natCast, Nat.mod_mod_of_dvd n (by decide : 2 ∣ 16)]
    omega
  have bound := (show ∀ r : ZMod 16, r.val % 2 = 1 → (sums16 r).card ≤ 2
    by decide +kernel) n parity
  let map (s : {s : ZMod 16 // AdmissibleSum (n : ZMod 16) s}) : sums16 n :=
    ⟨s.val, by
      obtain ⟨x, y, prod, sum⟩ := s.property
      exact mem_filter.mpr ⟨mem_univ _, x, by rw [← sum, add_sub_cancel_left, prod]⟩⟩
  have inject : Function.Injective map := fun _ _ h =>
    Subtype.ext (congrArg (fun s : sums16 (n : ZMod 16) => s.val) h)
  have bound' := Nat.card_le_card_of_injective map inject
  exact bound'.trans (by simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using bound)

private theorem odd_power_bound {n p k c : ℕ} (prime : p.Prime) (odd : p ≠ 2)
    (cop : p.Coprime n) (cap : ∀ sq : Bool, primePowerSumCount p sq (k+1) ≤ c) :
    count n (p^(k+1)) ≤ c := by
  classical
  letI : Fact p.Prime := ⟨prime⟩
  have nz := (ZMod.natCast_zmod_eq_zero_iff_dvd n p).mp.mt (prime.coprime_iff_not_dvd.mp cop)
  have eq : count n (p^(k+1)) = primePowerSumCount p (decide (IsSquare (n : ZMod p))) (k+1) := by
    simpa only [map_natCast] using card_primePower_admissibleSum odd k (n : ZMod (p^(k+1)))
      (by simpa only [map_natCast] using nz)
  exact eq.le.trans (cap _)

/-- CRT multiplies the eight local bounds. The modulus is 1,163,962,800. -/
theorem count_le {n : ℕ} (cop : modulus.Coprime n) : count n modulus ≤ 907200 := by
  have mul {a b : ℕ} (h : a.Coprime b) : count n (a*b) = count n a * count n b :=
    card_admissibleSum_crt h n
  have two := count_sixteen (Nat.prime_two.coprime_iff_not_dvd.mp
    (cop.of_dvd_left (by decide : 2 ∣ modulus)))
  calc
    count n modulus = count n 16 * count n 9 * count n 25 * count n 7 *
      count n 11 * count n 13 * count n 17 * count n 19 := by
        simp (disch := decide) only [modulus, mul]
    _ ≤ 2 * 3 * 10 * 4 * 6 * 7 * 9 * 10 := by
      gcongr
      · exact odd_power_bound (p:=3) (k:=1) (by decide) (by decide) (cop.of_dvd_left (by decide)) (by decide)
      · exact odd_power_bound (p:=5) (k:=1) (by decide) (by decide) (cop.of_dvd_left (by decide)) (by decide)
      · exact odd_power_bound (p:=7) (k:=0) (by decide) (by decide) (cop.of_dvd_left (by decide)) (by decide)
      · exact odd_power_bound (p:=11) (k:=0) (by decide) (by decide) (cop.of_dvd_left (by decide)) (by decide)
      · exact odd_power_bound (p:=13) (k:=0) (by decide) (by decide) (cop.of_dvd_left (by decide)) (by decide)
      · exact odd_power_bound (p:=17) (k:=0) (by decide) (by decide) (cop.of_dvd_left (by decide)) (by decide)
      · exact odd_power_bound (p:=19) (k:=0) (by decide) (by decide) (cop.of_dvd_left (by decide)) (by decide)
    _ = 907200 := by decide

/-- At the indicated full-width accuracy the whole sum band fits within a
single period. The bound holds for every supplied reading. -/
theorem full_width_907200 {n e : ℕ} (v : ℤ) (cop : modulus.Coprime n)
    (size : 2^2047 ≤ n) (error : e ≤ 2^1053) :
    (screened n (cutoff n) v e modulus).card ≤ 907200 := by
  have bound := count_blocks (n:=n) (b:=cutoff n) (e:=e) (v:=v) (w:=modulus) (d:=2^30)
    (by decide) (by
      intro s hs t ht ord
      have lower := full_width_cutoff size
      have dist := (ordered_diameter hs ht ord).trans error
      have cost := (Nat.mul_le_mul_right (t-s) (by omega : 2^1023 ≤ cutoff n+3)).trans dist
      rw [show (2:ℕ)^1053 = 2^1023*2^30 by rw [← pow_add]] at cost
      exact Nat.le_of_mul_le_mul_left cost (by positivity))
  rw [show (2:ℕ)^30/modulus + 1 = 1 by decide, one_mul] at bound
  exact bound.trans (count_le cop)

/-- Both prime factors in the comparison population exceed the wheel modulus. -/
theorem balanced_907200 {p q e : ℕ} (pp : p.Prime) (qp : q.Prime)
    (width : 2^1023 ≤ p) (ord : p ≤ q) (v : ℤ) (size : 2^2047 ≤ p*q) (error : e ≤ 2^1053) :
    (screened (p*q) (cutoff (p*q)) v e modulus).card ≤ 907200 := by
  have small : modulus < p := (by decide +kernel : modulus < 2^1023).trans_le width
  have pos : 0 < modulus := by decide
  have pc := pp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos small)
  have qc := qp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos (small.trans_le ord))
  exact full_width_907200 v (pc.symm.mul_right qc.symm) size error

end PrimeFactors.IntervalWheelPrimePowers
