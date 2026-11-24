import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace PrimeFactors

/-- In the first two base-p blocks of row pq, Lucas leaves just the entry q
at the positive index p modulo p. -/
private theorem pascal_digit {p q k : ℕ} (hp : p.Prime) (pos : 0 < k)
    (bound : k < 2*p) :
    (p*q).choose k ≡ (if k = p then q else 0) [MOD p] := by
  letI : Fact p.Prime := ⟨hp⟩
  have loc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p*q) (k := k) (p := p)
  rw [Nat.mul_mod_right, Nat.mul_div_cancel_left _ hp.pos] at loc
  split_ifs with eq
  · subst k
    simpa [Nat.div_self hp.pos] using loc
  · have rem : 0 < k % p := by
      apply Nat.pos_of_ne_zero
      intro zero
      have dvd := Nat.dvd_of_mod_eq_zero zero
      obtain ⟨a, ha⟩ := dvd
      have small : a < 2 := by
        apply Nat.lt_of_mul_lt_mul_left (a := p)
        rw [← ha, Nat.mul_comm p 2]
        exact bound
      have cases : a=0 ∨ a=1 := by omega
      rcases cases with rfl | rfl <;> simp_all
    simpa [Nat.choose_eq_zero_of_lt rem] using loc

/-- The low-degree part of row pq of Pascal's triangle has at most two
nonzero positive coefficients modulo the complete product. -/
theorem pascal_row_prefix {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p < q)
    (pos : 0 < k) (bound : k < 2*p) :
    (p*q).choose k ≡ (if k=p then q else 0) + (if k=q then p else 0) [MOD p*q] := by
  have P := pascal_digit (q := q) hp pos bound
  have Q := pascal_digit (q := p) hq pos (show k < 2*q by omega)
  rw [Nat.mul_comm q p] at Q
  apply (Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_primes hp hq).mpr lt.ne)).mp
  constructor
  · refine P.trans ?_
    by_cases h : k=q <;> simp [h, Nat.ModEq]
  · refine Q.trans ?_
    by_cases h : k=p <;> simp [h, Nat.ModEq]

private theorem pascal_signed_step {n : ℕ} (k : ℕ) (hn : 0 < n) :
    (-1 : ZMod n)^(k+1) * ((n-1).choose (k+1) : ℕ) =
      (-1 : ZMod n)^k * ((n-1).choose k : ℕ) +
      (-1 : ZMod n)^(k+1) * (n.choose (k+1) : ℕ) := by
  have pascal : n.choose (k+1) = (n-1).choose k + (n-1).choose (k+1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    exact Nat.choose_succ_succ _ _
  rw [pascal, Nat.cast_add, pow_succ]
  ring

/-- Taking the alternating prefix sum collapses the entire low row to one
binomial coefficient. The two threshold indicators correspond to the two
unknown primes. -/
theorem pascal_thresholds {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (po : Odd p) (qo : Odd q) (k : ℕ) (bound : k<2*p) :
    1 - (-1 : ZMod (p*q))^k * ((p*q-1).choose k : ℕ) =
      (if p ≤ k then (q : ZMod (p*q)) else 0) + (if q ≤ k then (p : ZMod (p*q)) else 0) := by
  induction k with
  | zero => simp [Nat.not_le.mpr hp.pos, Nat.not_le.mpr hq.pos]
  | succ k ih =>
    have before := ih (by omega)
    have row := (ZMod.natCast_eq_natCast_iff ..).mpr
      (pascal_row_prefix hp hq lt (Nat.succ_pos k) bound)
    rw [Nat.cast_add] at row
    push_cast at row
    have tick (r : ℕ) (odd : Odd r) (a : ZMod (p*q)) :
        (if r ≤ k then a else 0) - (-1 : ZMod (p*q))^(k+1) *
          (if k+1=r then a else 0) = (if r ≤ k+1 then a else 0) := by
      by_cases hit : k+1=r
      · have prev : ¬r≤k := by omega
        rw [if_neg prev, if_pos hit, if_pos (by omega), hit, odd.neg_one_pow]
        ring
      · have same : r≤k+1 ↔ r≤k := by omega
        simp [hit, same]
    rw [pascal_signed_step k (Nat.mul_pos hp.pos hq.pos), row, ← tick p po, ← tick q qo]
    linear_combination before

/-- For any odd cutoff between the factors below 2p, the canonical residue is exactly q−1. -/
theorem pascal_between {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (po : Odd p) (qo : Odd q) (ko : Odd k) (pk : p≤k) (kq : k<q) (short : k<2*p) :
    (p*q-1).choose k % (p*q) = q-1 := by
  have h := pascal_thresholds hp hq lt po qo k short
  simp only [ko.neg_one_pow, neg_one_mul, sub_neg_eq_add, if_pos pk,
    if_neg (Nat.not_le.mpr kq), add_zero] at h
  have congr : (p*q-1).choose k ≡ q-1 [MOD p*q] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    rw [Nat.cast_sub (by have := hq.pos; omega), Nat.cast_one]
    linear_combination h
  have qsmall : q-1 < p*q := by
    have := Nat.mul_le_mul_right q (show 1≤p by have := hp.pos; omega)
    simp at this
    omega
  simpa [Nat.ModEq, Nat.mod_eq_of_lt qsmall] using congr

/-- Before the first factor, an odd-index binomial has canonical residue N−1. -/
theorem pascal_before {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (po : Odd p) (qo : Odd q) (ko : Odd k) (small : k<p) :
    (p*q-1).choose k % (p*q) = p*q-1 := by
  have h := pascal_thresholds hp hq lt po qo k (by omega)
  simp only [ko.neg_one_pow, neg_one_mul, sub_neg_eq_add, if_neg (Nat.not_le.mpr small),
    if_neg (Nat.not_le.mpr (small.trans lt)), add_zero] at h
  have npos := Nat.mul_pos hp.pos hq.pos
  have congr : (p*q-1).choose k ≡ p*q-1 [MOD p*q] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    rw [Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_self]
    linear_combination h
  simpa [Nat.ModEq, Nat.mod_eq_of_lt (show p*q-1<p*q by omega)] using congr

/-- A single comparison of the canonical residue with half the modulus tells
which side of the smaller prime an odd cutoff occupies. -/
theorem pascal_half_test {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (po : Odd p) (qo : Odd q) (ko : Odd k) (kq : k<q) (short : k<2*p) :
    2*((p*q-1).choose k % (p*q)) < p*q ↔ p≤k := by
  have twice := Nat.mul_le_mul_right q hp.two_le
  have qpos := hq.pos
  by_cases pk : p≤k
  · rw [pascal_between hp hq lt po qo ko pk kq short]
    omega
  · rw [pascal_before hp hq lt po qo ko (by omega)]
    omega

/-- Multiplying the shifted residue by a public scale smaller than p produces
zero before the threshold and exactly scale·q after the threshold. -/
theorem pascal_scaled_phase {p q k a : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (po : Odd p) (qo : Odd q) (ko : Odd k) (kq : k<q) (short : k<2*p) (scale : a<p) :
    a*((p*q-1).choose k+1) % (p*q) = (if p≤k then a*q else 0) := by
  have qpos := hq.pos
  have npos := Nat.mul_pos hp.pos hq.pos
  by_cases hit : p≤k
  · have eq := pascal_between hp hq lt po qo ko hit kq short
    have c : (p*q-1).choose k ≡ q-1 [MOD p*q] := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt (show q-1<p*q by
        have := Nat.mul_le_mul_right q (show 1≤p by have := hp.pos; omega)
        simp at this
        omega)] using eq
    have r := (c.add_right 1).mul_left a
    rw [Nat.sub_add_cancel qpos] at r
    simpa [Nat.ModEq, hit, Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_right scale qpos)] using r
  · have eq := pascal_before hp hq lt po qo ko (Nat.lt_of_not_ge hit)
    have c : (p*q-1).choose k ≡ p*q-1 [MOD p*q] := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt (show p*q-1<p*q by omega)] using eq
    have r := (c.add_right 1).mul_left a
    rw [Nat.sub_add_cancel npos] at r
    simpa [Nat.ModEq, hit] using r

/-- If all phases a/x with L ≤ x ≤ U stay in a single gap between integers,
their uniform distance d from the integers has the indicated upper bound. -/
theorem pascal_phase_margin_bound {L U d a j : ℝ} (h : L≤U) (hj : 0≤j)
    (left : (j+d)*U≤a) (right : a≤(j+1-d)*L) : d*(L+U)≤L := by
  nlinarith only [left, right, mul_nonneg hj (sub_nonneg.mpr h)]

/-- The continuous public scale L·U/(L+U) achieves the optimal endpoint margin. -/
theorem pascal_phase_optimal_scale {L U : ℝ} (hL : 0<L) (hU : 0<U) :
    (L*U/(L+U))/U = L/(L+U) ∧ 1-(L*U/(L+U))/L = L/(L+U) := by
  constructor <;> field_simp [ne_of_gt hL, ne_of_gt hU, ne_of_gt (add_pos hL hU)] <;> ring

/-- All products with q < 4p have an odd public cutoff giving the larger prime. -/
theorem pascal_sqrt_readout {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (po : Odd p) (qo : Odd q) (balance : q<4*p) :
    (p*q-1).choose (2*((Nat.sqrt (p*q)-1)/2)+1) % (p*q) + 1 = q := by
  let k := 2*((Nat.sqrt (p*q)-1)/2)+1
  have low : p ≤ Nat.sqrt (p*q) := Nat.le_sqrt.mpr (Nat.mul_le_mul_left p lt.le)
  have below : Nat.sqrt (p*q)<q := Nat.sqrt_lt.mpr (Nat.mul_lt_mul_of_pos_right lt hq.pos)
  have short : Nat.sqrt (p*q)<2*p := Nat.sqrt_lt.mpr (by
    have := Nat.mul_lt_mul_of_pos_left balance hp.pos
    nlinarith only [this])
  have pp := hp.pos
  have top : k≤Nat.sqrt (p*q) := by dsimp [k]; omega
  have pk : p≤k := by obtain ⟨j,hj⟩ := po; dsimp [k]; omega
  rw [pascal_between hp hq lt po qo (show Odd k from ⟨_,rfl⟩) pk (by omega) (by omega)]
  have := hq.pos
  omega

/-- Above both factors, the same binomial returns their sum minus one. -/
theorem pascal_both {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (po : Odd p) (qo : Odd q) (ko : Odd k) (qk : q≤k) (short : k<2*p) :
    (p*q-1).choose k % (p*q) = p+q-1 := by
  have h := pascal_thresholds hp hq lt po qo k short
  simp only [ko.neg_one_pow, neg_one_mul, sub_neg_eq_add, if_pos (lt.le.trans qk),
    if_pos qk] at h
  have congr : (p*q-1).choose k ≡ p+q-1 [MOD p*q] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    rw [Nat.cast_sub (by have := hq.pos; omega), Nat.cast_one, Nat.cast_add]
    linear_combination h
  have small : p+q-1<p*q := by
    have twice := Nat.mul_le_mul_right q hp.two_le
    omega
  simpa [Nat.ModEq, Nat.mod_eq_of_lt small] using congr

/-- One fixed index for an entire bit width suffices. -/
theorem pascal_dyadic_sum {p q b : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (po : Odd p) (qo : Odd q) (lo : 2^b≤p) (hi : q<2^(b+1)) :
    (p*q-1).choose (2^(b+1)-1) % (p*q) + 1 = p+q := by
  rw [pow_succ] at hi ⊢
  have powpos : 0<2^b := by positivity
  have ko : Odd (2^b*2-1) := ⟨2^b-1, by omega⟩
  rw [pascal_both hp hq lt po qo ko (by omega) (by omega)]
  omega

/-- Any combination of the first d+1 binomial basis functions is determined
by its values on any d+1 consecutive natural numbers, over any commutative ring.
This includes the composite coefficient ring used for the public readout. -/
theorem pascal_window_independent {R : Type*} [CommRing R] (d a : ℕ) (c : ℕ → R)
    (vanish : ∀ i ≤ d, ∑ j ∈ Finset.range (d+1), c j * ((a+i).choose j : ℕ) = 0) :
    ∀ j ≤ d, c j = 0 := by
  induction d generalizing c with
  | zero =>
    intro j hj
    simpa [Nat.eq_zero_of_le_zero hj] using vanish 0 (Nat.zero_le _)
  | succ d ih =>
    have lower : ∀ i ≤ d, ∑ j ∈ Finset.range (d+1),
        c (j+1) * ((a+i).choose j : ℕ) = 0 := by
      intro i hi
      have left := vanish i (by omega)
      have right := vanish (i+1) (by omega)
      rw [Finset.sum_range_succ'] at left right
      simp only [Nat.choose_zero_right, Nat.cast_one, mul_one] at left right
      simp only [← Nat.add_assoc, Nat.choose_succ_succ, Nat.cast_add, mul_add,
        Finset.sum_add_distrib] at right
      linear_combination right - left
    have tails : ∀ j ≤ d, c (j+1) = 0 := ih (fun j => c (j+1)) lower
    intro j hj
    cases j with
    | zero =>
      have h := vanish 0 (Nat.zero_le _)
      rw [Finset.sum_range_succ'] at h
      rw [Finset.sum_eq_zero (fun t ht => by
        rw [tails t (Nat.le_of_lt_succ (Finset.mem_range.mp ht)), zero_mul])] at h
      simpa using h
    | succ j => exact tails j (by omega)

end PrimeFactors
