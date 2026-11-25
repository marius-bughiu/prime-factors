import PrimeFactors.FeasibleDivisorCover

/-! Determinant budgets for binomial-coordinate windows in dimension 24,576. -/

namespace PrimeFactors.BinomialDivisorScale

open FeasibleDivisorCover Finset

set_option exponentiation.threshold 16384
set_option maxRecDepth 8192

/-- Product of the coordinate bounds on the integer progression 0 through H. -/
noncomputable def weights (r H : ℕ) := ∏ i ∈ range r, H.choose i

private noncomputable def factorials (r : ℕ) := ∏ i ∈ range r, i.factorial

/-- At index t, a verified threshold collects one bit whenever x reaches it.
The e-th threshold must satisfy t^s ≥ 2^e. -/
private def valid (s e : ℕ) : List ℕ → Bool
  | [] => true
  | t :: ts => decide (2^(e+1) ≤ t^s) && valid s (e+1) ts

private def price (x : ℕ) (ts : List ℕ) := ts.countP (fun t => decide (t≤x))
private def runningBits (x : ℕ) (ts : List ℕ) := (ts.map (fun t => x+1-t)).sum
private def area (r : ℕ) (ts : List ℕ) := (ts.map (fun t => (r+1-t).choose 2)).sum

private lemma bits_at {s x e : ℕ} {ts : List ℕ} (ok : valid s e ts=true)
    (hit : price x ts ≠ 0) : 2^(e+price x ts)≤x^s := by
  induction ts generalizing e with
  | nil => simp [price] at hit
  | cons t ts ih =>
    obtain ⟨bound,tail⟩ := Bool.and_eq_true_iff.mp ok
    have b : 2^(e+1)≤t^s := of_decide_eq_true bound
    have step : price x (t::ts) = price x ts + if t≤x then 1 else 0 := by
      simp [price, List.countP_cons]
    rw [step] at hit ⊢
    by_cases h : price x ts=0
    · rw [h] at hit ⊢
      split_ifs at hit ⊢ with hx
      · simpa using b.trans (Nat.pow_le_pow_left hx s)
      · simp at hit
    · have tailBit := ih tail h
      apply le_trans _ tailBit
      apply Nat.pow_le_pow_right (by decide)
      split_ifs <;> omega

private lemma runningBits_step (n : ℕ) (ts : List ℕ) :
    runningBits (n+1) ts = runningBits n ts + price (n+1) ts := by
  induction ts with
  | nil => simp [runningBits,price]
  | cons t ts ih =>
    simp only [runningBits,List.map_cons,List.sum_cons] at ih ⊢
    simp only [price,List.countP_cons,decide_eq_true_eq] at ih ⊢
    split_ifs <;> omega

private lemma area_step (n : ℕ) (ts : List ℕ) : area (n+1) ts = area n ts + runningBits n ts := by
  induction ts with
  | nil => simp [area,runningBits]
  | cons t ts ih =>
    have h : (n+1+1-t).choose 2=(n+1-t).choose 2+(n+1-t) := by
      by_cases ht : t≤n+1
      · rw [show n+1+1-t=(n+1-t)+1 by omega, Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
      · rw [show n+1-t=0 by omega]
        rcases (show n+1+1-t=0 ∨ n+1+1-t=1 by omega) with h|h <;> rw [h] <;> decide
    simp only [area,runningBits,List.map_cons,List.sum_cons] at ih ⊢
    omega

private lemma factorial_bits (s : ℕ) (ts : List ℕ) (ok : valid s 0 ts=true)
    (start : runningBits 0 ts=0) (n : ℕ) : 2^(runningBits n ts)≤n.factorial^s := by
  induction n with
  | zero => simp [start]
  | succ n ih =>
    have atStep : 2^(price (n+1) ts)≤(n+1)^s := by
      by_cases h : price (n+1) ts=0
      · rw [h,pow_zero]; exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.succ_ne_zero _))
      · simpa using bits_at ok h
    rw [runningBits_step,pow_add,Nat.factorial_succ,mul_comm (n+1) _,mul_pow]
    exact Nat.mul_le_mul ih atStep

private lemma total_bits (s : ℕ) (ts : List ℕ) (ok : valid s 0 ts=true)
    (start : runningBits 0 ts=0) (zero : area 0 ts=0) (r : ℕ) :
    2^(area r ts) ≤ (factorials r)^s := by
  induction r with
  | zero => simp [zero,factorials]
  | succ r ih =>
    rw [area_step,pow_add,show factorials (r+1) = factorials r*r.factorial from prod_range_succ ..,mul_pow]
    exact Nat.mul_le_mul ih (factorial_bits s ts ok start r)

/-- The least integers whose sixteenth powers cross successive powers of two. -/
private def thresholds : List ℕ := [
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4,
  4, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 7,
  7, 7, 8, 8, 8, 8, 9, 9, 10, 10, 10, 11, 11, 12,
  12, 13, 13, 14, 15, 15, 16, 16, 17, 18, 19, 20, 20, 21,
  22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 34, 35, 37, 39,
  40, 42, 44, 46, 48, 50, 52, 54, 57, 59, 62, 64, 67, 70,
  73, 77, 80, 83, 87, 91, 95, 99, 104, 108, 113, 118, 123, 128,
  134, 140, 146, 153, 159, 166, 174, 182, 190, 198, 207, 216, 225, 235,
  246, 256, 268, 280, 292, 305, 318, 332, 347, 363, 379, 395, 413, 431,
  450, 470, 491, 512, 535, 559, 584, 609, 636, 664, 694, 725, 757, 790,
  825, 862, 900, 940, 981, 1024, 1070, 1117, 1167, 1218, 1272, 1328, 1387, 1449,
  1513, 1580, 1650, 1723, 1799, 1879, 1962, 2048, 2139, 2234, 2333, 2436, 2544, 2656,
  2774, 2897, 3025, 3159, 3299, 3445, 3597, 3757, 3923, 4096, 4278, 4467, 4665, 4871,
  5087, 5312, 5548, 5793, 6050, 6317, 6597, 6889, 7194, 7513, 7845, 8192, 8555, 8934,
  9329, 9742, 10174, 10624, 11095, 11586, 12099, 12634, 13194, 13778, 14388, 15025, 15690, 16384,
  17110, 17867, 18658, 19484, 20347, 21248, 22189, 23171, 24197]

private theorem combine_bits {k b s z w e a : ℕ} (sz : z*s≠0)
    (base : k^z ≤ 2^w) (bits : w*b*s≤e*z) (h : 2^e≤a^s) : k^b≤a := by
  apply (Nat.pow_le_pow_iff_left sz).mp
  calc
    (k^b)^(z*s) = ((k^z)^b)^s := by simp only [←pow_mul]; congr 1; ring
    _ ≤ (((2:ℕ)^w)^b)^s := Nat.pow_le_pow_left (Nat.pow_le_pow_left base _) _
    _ = 2^(w*b*s) := by simp only [←pow_mul]
    _ ≤ 2^(e*z) := Nat.pow_le_pow_right (by decide) bits
    _ = ((2:ℕ)^e)^z := pow_mul ..
    _ ≤ (a^s)^z := Nat.pow_le_pow_left h _
    _ = a^(z*s) := by rw [←pow_mul,Nat.mul_comm s z]

/-- The geometric mean of the factorial denominators, weighted by total degree,
exceeds 5360. The certificate uses small integer powers and 233 thresholds. -/
theorem factorial_budget : 5360^(dimension.choose 2) ≤ factorials dimension := by
  apply combine_bits (z:=1024) (s:=16) (w:=12686) (e:=area dimension thresholds)
  · decide
  · decide +kernel
  · rw [show area dimension thresholds = 59865523230 by
      simp only [area,Nat.choose_two_right]; decide +kernel]
    rw [Nat.choose_two_right]; decide +kernel
  · exact total_bits 16 thresholds (by decide +kernel) (by decide +kernel)
      (by decide +kernel) dimension

theorem choose_product_budget {r H U K : ℕ} (span : H≤K*U) (factor : K^(r.choose 2)≤factorials r) :
    weights r H ≤ U^(r.choose 2) := by
  have pos : 0<factorials r := Finset.prod_pos (fun i _ => Nat.factorial_pos i)
  apply (Nat.mul_le_mul_left_iff pos).mp
  calc
    factorials r * weights r H = ∏ i ∈ range r, (i.factorial*H.choose i) := (prod_mul_distrib ..).symm
    _ ≤ ∏ i ∈ range r, H^i := by
      apply prod_le_prod'; intro i _; rw [←Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.descFactorial_le_pow ..
    _ = H^(r.choose 2) := by rw [prod_pow_eq_pow_sum,Finset.sum_range_id,Nat.choose_two_right]
    _ ≤ (K*U)^(r.choose 2) := Nat.pow_le_pow_left span _
    _ ≤ factorials r*U^(r.choose 2) := by rw [mul_pow]; exact Nat.mul_le_mul_right _ factor

/-- The existing finite-search and LLL volume budgets both admit the enlarged span. -/
theorem rooms {n H : ℕ} (big : 2^2047≤n) (b : Bool) (span : H≤5360*radius b) :
    let m := multiplicity
    let r := dimension
    let D := divisorFloor n b
    let W := weights r H
    n^(m+m.choose 2)*(r^r*W) < (D^m)^r ∧
    r^(2*r)*2^((r-1)*r)*(n^(m+m.choose 2)*W)^4 < (D^m)^(4*r) := by
  have h := FeasibleDivisorCover.rooms big b
  have w := choose_product_budget span factorial_budget
  exact ⟨(Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ w)).trans_lt h.1,
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ w) _)).trans_lt h.2⟩

end PrimeFactors.BinomialDivisorScale
