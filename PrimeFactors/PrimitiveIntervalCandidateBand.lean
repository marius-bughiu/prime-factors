import PrimeFactors.PrimitiveIntervalPrecision

/-! The precision of a supplied interval reading bounds the number of
compatible sums even when the reading does not determine a unique answer. -/
namespace PrimeFactors.PrimitiveIntervalCandidateBand

open Finset PrimitiveIntervalMoment

/-- The sum interval, residue class and error allowance all use public inputs.
The integer reading is supplied independently. -/
noncomputable def candidates (n b : ℕ) (v : ℤ) (e : ℕ) : Finset ℕ :=
  (Icc (2*b+2) (4*b+2)).filter fun s =>
    s%4=(n+1)%4 ∧ |value n b s-v| ≤ e

theorem mem_candidates {n b s e : ℕ} {v : ℤ} :
    s ∈ candidates n b v e ↔
      (2*b+2 ≤ s ∧ s ≤ 4*b+2) ∧ s%4=(n+1)%4 ∧ |value n b s-v| ≤ e := by
  simp only [candidates,mem_filter,mem_Icc]

/-- The true sum survives whenever the input reading meets its claimed
absolute error. Balance, order and oddness suffice for the sum bounds. -/
theorem contains_sum {p q e : ℕ} {v : ℤ} (pos : 0 < p) (ord : p < q)
    (balanced : q < 2*p) (odd : (p*q)%2=1)
    (error : |value (p*q) (cutoff (p*q)) (p+q)-v| ≤ e) :
    p+q ∈ candidates (p*q) (cutoff (p*q)) v e := by
  obtain ⟨lo,hi⟩ := cutoff_bounds pos balanced
  exact mem_candidates.mpr ⟨⟨by omega,by omega⟩,SumIntervalExclusion.sum_congruence odd,
    by simpa only [Nat.cast_mul,Nat.cast_add] using error⟩

theorem contains_from_aggregate {p q e : ℕ} {v exactValue : ℤ}
    [Fact p.Prime] [Fact q.Prime] (ord : p < q) (balanced : q < 2*p) (odd : (p*q)%2=1)
    (reading : aggregate p q (cutoff (p*q))=(exactValue:ℂ))
    (error : |exactValue-v| ≤ e) : p+q ∈ candidates (p*q) (cutoff (p*q)) v e := by
  have eq : value (p*q) (cutoff (p*q)) (p+q)=exactValue := by
    exact_mod_cast (aggregate_value ord balanced).symm.trans reading
  exact contains_sum (Fact.out : p.Prime).pos ord balanced odd (eq ▸ error)

theorem value_difference (n b s t : ℤ) :
    value n b t - value n b s = (t-s)*(s+t-2*b-2) := by unfold value; ring

/-- Distinct surviving sums differ by at least four. Across that distance
the mean slope of the quadratic is at least 2(B+3). -/
theorem ordered_diameter {n b e s t : ℕ} {v : ℤ}
    (hs : s ∈ candidates n b v e) (ht : t ∈ candidates n b v e) (ord : s ≤ t) :
    (b+3)*(t-s) ≤ e := by
  rcases eq_or_lt_of_le ord with rfl|lt
  · simp
  obtain ⟨⟨sl,_⟩,sc,se⟩ := mem_candidates.mp hs
  obtain ⟨_,tc,te⟩ := mem_candidates.mp ht
  have gap : s+4 ≤ t := by omega
  have scale : 2*((b:ℤ)+3) ≤ (s:ℤ)+t-2*b-2 := by omega
  have lower := mul_le_mul_of_nonneg_left scale (show (0:ℤ) ≤ (t:ℤ)-s by omega)
  have upper : value n b t-value n b s ≤ 2*(e:ℤ) := by
    have a := (abs_le.mp te).2
    have b := (abs_le.mp se).1
    omega
  rw [value_difference] at upper
  zify [ord]
  nlinarith only [lower,upper]

theorem ordered_error_bound {n b e s t : ℕ} {v : ℤ}
    (hs : s ∈ candidates n b v e) (ht : t ∈ candidates n b v e) (ord : s ≤ t) :
    b*(t-s) ≤ e :=
  (Nat.mul_le_mul_right (t-s) (show b ≤ b+3 by omega)).trans (ordered_diameter hs ht ord)

theorem diameter {n b e s t : ℕ} {v : ℤ} (hs : s ∈ candidates n b v e)
    (ht : t ∈ candidates n b v e) : (b:ℤ)*|(s:ℤ)-t| ≤ e := by
  have ordered {x y : ℕ} (hx : x ∈ candidates n b v e) (hy : y ∈ candidates n b v e)
      (h : x ≤ y) : (b:ℤ)*((y:ℤ)-x) ≤ e := by
    have le := ordered_error_bound hx hy h
    zify [h] at le
    exact le
  rcases le_total s t with h|h
  · rw [abs_of_nonpos (by omega : (s:ℤ)-t≤0),neg_sub]
    exact ordered hs ht h
  · rw [abs_of_nonneg (by omega : (0:ℤ)≤(s:ℤ)-t)]
    exact ordered ht hs h

/-- Count by the number of four-unit steps above the least survivor.
The bound remains valid at B=0. -/
theorem card_bound (n b : ℕ) (v : ℤ) (e : ℕ) :
    (candidates n b v e).card ≤ e/(4*(b+3))+1 := by
  let S := candidates n b v e
  by_cases nonempty : S.Nonempty
  · let m := S.min' nonempty
    have hm := S.min'_mem nonempty
    change m ∈ candidates n b v e at hm
    let index (s : ℕ) := (s-m)/4
    have step {s : ℕ} (hs : s ∈ S) : s=m+4*index s := by
      have lo := S.min'_le s hs
      change m ≤ s at lo
      have sc := (mem_candidates.mp hs).2.1
      have mc := (mem_candidates.mp hm).2.1
      dsimp only [index]
      omega
    have into : Set.MapsTo index S (range (e/(4*(b+3))+1)) := by
      intro s hs
      have cost := ordered_diameter hm hs (S.min'_le s hs)
      have delta : s-m=4*index s := by have := step hs; omega
      rw [delta] at cost
      have h : index s ≤ e/(4*(b+3)) :=
        (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith only [cost])
      exact mem_range.mpr (by omega)
    have count := card_le_card_of_injOn index into (by
      intro x hx y hy eq
      have hx' := step hx
      have hy' := step hy
      omega)
    simpa only [card_range] using count
  · change S.card ≤ _
    simp [not_nonempty_iff_eq_empty.mp nonempty]

set_option exponentiation.threshold 4096 in
/-- A 2^(1025+k) error budget leaves at most 2^k candidate sums for a
2,048-bit product. The extra three in the slope makes the division strict. -/
theorem full_width {n e : ℕ} (v : ℤ) (k : ℕ) (bits : 2^2047 ≤ n) (error : e ≤ 2^(1025+k)) :
    (candidates n (cutoff n) v e).card ≤ 2^k := by
  have len := full_width_cutoff bits
  have denom : 2^1025 < 4*(cutoff n+3) := by
    rw [show (2:ℕ)^1025=4*2^1023 by decide +kernel]
    omega
  have powpos : (0:ℕ)<2^k := by positivity
  have strict : e < 2^k*(4*(cutoff n+3)) := by
    rw [pow_add,mul_comm] at error
    exact error.trans_lt (Nat.mul_lt_mul_of_pos_left denom powpos)
  exact (card_bound n (cutoff n) v e).trans
    (Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul (by omega)).mpr strict))

set_option exponentiation.threshold 4096 in
theorem full_width_20 {n e : ℕ} (v : ℤ) (bits : 2^2047 ≤ n) (error : e ≤ 2^1045) :
    (candidates n (cutoff n) v e).card ≤ 2^20 := full_width v 20 bits error

set_option exponentiation.threshold 4096 in
theorem full_width_32 {n e : ℕ} (v : ℤ) (bits : 2^2047 ≤ n) (error : e ≤ 2^1057) :
    (candidates n (cutoff n) v e).card ≤ 2^32 := full_width v 32 bits error

/-- At the midpoint between the values for sums 24 and 28, error 68
admits both. An allowance of 67 excludes both. -/
theorem control143 :
    candidates 143 8 24 68 = {24,28} ∧ candidates 143 8 24 67 = ∅ := by
  decide +kernel

end PrimeFactors.PrimitiveIntervalCandidateBand
