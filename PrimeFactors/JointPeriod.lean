import PrimeFactors.PowerSignature

namespace PrimeFactors

/-- A pair of power coordinates repeats precisely at multiples of its joint period. -/
theorem twoPowers_repeat_iff {G : Type*} [Group G] (x y : G) (s d : ℕ) :
    (x ^ (s + d) = x ^ s ∧ y ^ (s + d) = y ^ s) ↔
      Nat.lcm (orderOf x) (orderOf y) ∣ d := by
  rw [Nat.lcm_dvd_iff, orderOf_dvd_iff_pow_eq_one, orderOf_dvd_iff_pow_eq_one]
  simp [pow_add]

/-- If two powers agree in the original group, their projections also repeat.
A positive gap shorter than the joint period downstairs rules out the collision. -/
theorem twoPowers_separate_of_projected_period {G H : Type*} [Group G] [Group H]
    (π : G →* H) (x y : G) {s t : ℕ} (st : s < t)
    (short : t - s < Nat.lcm (orderOf (π x)) (orderOf (π y))) :
    ¬ (x ^ s = x ^ t ∧ y ^ s = y ^ t) := by
  rintro ⟨hx, hy⟩
  have repeats : (π x) ^ (s + (t - s)) = (π x) ^ s ∧
      (π y) ^ (s + (t - s)) = (π y) ^ s := by
    rw [Nat.add_sub_of_le st.le, ← map_pow, ← map_pow, ← map_pow, ← map_pow, hx, hy]
    exact ⟨rfl, rfl⟩
  have divides := (twoPowers_repeat_iff _ _ _ _).mp repeats
  exact (Nat.not_le_of_lt short) (Nat.le_of_dvd (Nat.sub_pos_of_lt st) divides)

/-- Two bases suffice when their projected joint period at the larger prime is
full. The hypothesis serves to analyze random choices; the target powers and
a candidate factorization can be calculated and checked knowing only `N`. -/
theorem twoPowers_iff_factorSum {p q s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (pq : p < q) (balance : q ≤ 2 * p) (x y : (ZMod (p * q))ˣ)
    (period : let π := ZMod.unitsMap (dvd_mul_left q p)
      Nat.lcm (orderOf (π x)) (orderOf (π y)) = q - 1)
    (lower : 4 * (p * q) ≤ s ^ 2) (upper : 2 * s ^ 2 ≤ 9 * (p * q)) :
    (x ^ s = x ^ (p * q + 1) ∧ y ^ s = y ^ (p * q + 1)) ↔ s = p + q := by
  have ⟨trueLower, trueUpper⟩ := balanced_factorSum_bounds pq.le balance
  have qlarge : 2 < q := lt_of_le_of_lt hp.two_le pq
  rw [← unit_pow_factorSum hp hq pq.ne x, ← unit_pow_factorSum hp hq pq.ne y]
  constructor
  · rintro ⟨hx, hy⟩
    rcases lt_trichotomy s (p + q) with h | h | h
    · have short := balanced_window_difference_lt hp.pos qlarge pq.le lower trueUpper h.le
      exact (twoPowers_separate_of_projected_period (ZMod.unitsMap (dvd_mul_left q p)) x y h
        (period.symm ▸ short) ⟨hx, hy⟩).elim
    · exact h
    · have short := balanced_window_difference_lt hp.pos qlarge pq.le trueLower upper h.le
      exact (twoPowers_separate_of_projected_period (ZMod.unitsMap (dvd_mul_left q p)) x y h
        (period.symm ▸ short) ⟨hx.symm, hy.symm⟩).elim
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- The cyclic-group generating-pair probability has one factor `1 − 1/r²` for
each distinct prime dividing the order. Even the product using every integer
from 2 through `m + 1` telescopes to the positive lower bound on the left. -/
theorem jointPeriod_eulerProduct_bound (m : ℕ) (P : Finset ℕ)
    (bounds : ∀ r ∈ P, 2 ≤ r ∧ r ≤ m + 1) :
    ((m : ℚ) + 2) / (2 * (m + 1)) ≤ ∏ r ∈ P, (1 - 1 / (r : ℚ) ^ 2) := by
  induction m generalizing P with
  | zero =>
    have empty : P = ∅ := by
      ext r
      simp
      intro hr
      obtain ⟨lo, hi⟩ := bounds r hr
      omega
    simp [empty]
  | succ m ih =>
    let c : ℚ := m
    have hc : 0 ≤ c := by dsimp [c]; positivity
    let weight := 1 - 1 / (c + 2) ^ 2
    have sq : 0 < (c + 2) ^ 2 := by positivity
    have hw : 0 ≤ weight := by
      dsimp [weight]
      apply sub_nonneg.mpr ((div_le_one₀ sq).mpr ?_)
      nlinarith [sq_nonneg c]
    have wh : weight ≤ 1 := by dsimp [weight]; linarith [one_div_nonneg.mpr sq.le]
    have ht : (c + 3) / (2 * (c + 2)) =
        (c + 2) / (2 * (c + 1)) * weight := by
      dsimp [weight]
      field_simp
      ring
    change (↑(m + 1) + 2 : ℚ) / (2 * (↑(m + 1) + 1)) ≤ _
    push_cast
    rw [show (m : ℚ) + 1 + 2 = c + 3 by dsimp [c]; ring,
        show (m : ℚ) + 1 + 1 = c + 2 by dsimp [c]; ring, ht]
    by_cases top : m + 2 ∈ P
    · have h := ih (P.erase (m + 2)) (by
        intro r hr
        obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hr
        obtain ⟨lo, hi⟩ := bounds r mem
        exact ⟨lo, by omega⟩)
      rw [← Finset.prod_erase_mul P (fun r => 1 - 1 / (r : ℚ) ^ 2) top]
      push_cast
      exact mul_le_mul_of_nonneg_right h hw
    · have h := ih P (by
        intro r hr
        obtain ⟨lo, hi⟩ := bounds r hr
        have ne : r ≠ m + 2 := fun he => top (he ▸ hr)
        exact ⟨lo, by omega⟩)
      have pos : 0 ≤ (c + 2) / (2 * (c + 1)) :=
        div_nonneg (by linarith) (mul_nonneg (by norm_num) (by linarith))
      exact (mul_le_of_le_one_right pos wh).trans h

/-- In particular the generating-pair product exceeds one half for every order.
This numerical statement uses no primality hypotheses and applies to its prime divisors. -/
theorem jointPeriod_eulerProduct_gt_half (m : ℕ) (P : Finset ℕ)
    (bounds : ∀ r ∈ P, 2 ≤ r ∧ r ≤ m + 1) :
    (1 / 2 : ℚ) < ∏ r ∈ P, (1 - 1 / (r : ℚ) ^ 2) := by
  apply lt_of_lt_of_le _ (jointPeriod_eulerProduct_bound m P bounds)
  apply (lt_div_iff₀ (by positivity)).mpr
  ring_nf
  linarith

end PrimeFactors
