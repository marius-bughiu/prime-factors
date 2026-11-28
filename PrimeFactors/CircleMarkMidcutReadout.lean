import PrimeFactors.CircleMarkTargetFrequency

/-! A public prefix between the two local half-periods. Its exact hit rate
and its signed population count each determine a prime of the product.
The population count is an aggregate over all residue classes. -/
namespace PrimeFactors.CircleMarkMidcutReadout

open Finset CircleMarkTargetFrequency
open scoped Classical

/-- Positive coordinates through half the integer square root of the product. -/
def cutoff (n : ℕ) : ℕ := n.sqrt / 2

noncomputable abbrev frequency (n : ℕ) [NeZero n] := rate n (Icc 1 (cutoff n))

/-- A hit contributes +1, an eligible miss contributes −1, and all other
residue classes contribute zero. -/
noncomputable def score (n : ℕ) [NeZero n] (t : ZMod n) : ℤ :=
  if t ∈ hits n (Icc 1 (cutoff n)) then 1 else if t ∈ targets n then -1 else 0

/-- One signed sum with no externally supplied target-population size. -/
noncomputable def imbalance (n : ℕ) [NeZero n] : ℤ := ∑ t : ZMod n, score n t

/-- The smaller prime's half-period has ended and the larger prime's
half-period still includes the public cutoff. -/
theorem between {p q : ℕ} (order : p < q) :
    (p-1)/2 ≤ cutoff (p*q) ∧ cutoff (p*q) ≤ (q-1)/2 := by
  have lo : p ≤ (p*q).sqrt := Nat.le_sqrt.mpr (Nat.mul_le_mul_left p order.le)
  have hi : (p*q).sqrt < q := Nat.sqrt_lt.mpr (Nat.mul_lt_mul_of_pos_right order (by omega))
  unfold cutoff
  omega

private theorem half (r : ℕ) (odd : Odd r) : 2*((r-1)/2)+1=r := by
  obtain ⟨k,h⟩ := odd
  omega

theorem frequency_eq {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) :
    frequency (p*q) = 1/2+(cutoff (p*q):ℚ)/((q:ℚ)-1) := by
  obtain ⟨lo,hi⟩ := between order
  rw [frequency,first_hit order.ne op oq,min_eq_right lo,min_eq_left hi]
  congr 1
  have h : 2*(((p-1)/2:ℕ):ℚ)+1=p := by exact_mod_cast half p (hp.out.odd_of_ne_two op)
  have den : (p:ℚ)-1≠0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.out.one_lt))
  field_simp
  linarith

/-- Hit count minus miss count, expressed using the two finite sets. -/
theorem imbalance_eq_counts (n : ℕ) [NeZero n] :
    imbalance n = 2*((hits n (Icc 1 (cutoff n))).card:ℤ) - (targets n).card := by
  let A := hits n (Icc 1 (cutoff n))
  have term (t : ZMod n) : score n t =
      (if t∈A then (2:ℤ) else 0) - (if t∈targets n then 1 else 0) := by
    change (if t∈A then 1 else if t∈targets n then -1 else 0) = _
    by_cases hit : t∈A
    · have eligible : t∈targets n := (mem_filter.mp hit).1
      simp [hit,eligible]
    · simp only [hit,if_false]
      split <;> norm_num
  unfold imbalance
  simp_rw [term]
  rw [sum_sub_distrib]
  simp [sum_ite_mem,A,mul_comm]

/-- Exact signed total of the three-valued public score. -/
theorem imbalance_eq {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) :
    imbalance (p*q) = (cutoff (p*q):ℤ)*((p:ℤ)-1) := by
  obtain ⟨lo,hi⟩ := between order
  obtain ⟨total,hit⟩ := counts order.ne op oq (Icc 1 (cutoff (p*q)))
  rw [prefix_cover op,prefix_cover oq,min_eq_right lo,min_eq_left hi] at hit
  rw [imbalance_eq_counts,hit,total]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have h : 2*(((p-1)/2:ℕ):ℤ)+1=p := by exact_mod_cast half p (hp.out.odd_of_ne_two op)
  linear_combination (cutoff (p*q):ℤ)*h

theorem cutoff_pos {p q : ℕ} [hp : Fact p.Prime] (order : p<q) (op : p≠2) :
    0 < cutoff (p*q) := by
  have := hp.out.two_le
  exact (show 0<(p-1)/2 by omega).trans_le (between order).1

/-- Inversion of one exact rational hit rate. -/
theorem read_larger {p q : ℕ} [Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) :
    1+(cutoff (p*q):ℚ)/(frequency (p*q)-1/2) = q := by
  rw [frequency_eq order op oq,add_sub_cancel_left]
  have cp : (cutoff (p*q):ℚ)≠0 := by exact_mod_cast (cutoff_pos order op).ne'
  have qp : (q:ℚ)-1≠0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hq.out.one_lt))
  field_simp

/-- Inversion of the single signed integer aggregate by exact division. -/
theorem read_smaller {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) :
    1 + imbalance (p*q)/(cutoff (p*q):ℤ) = p := by
  rw [imbalance_eq order op oq,Int.mul_ediv_cancel_left _
    (show (cutoff (p*q):ℤ)≠0 by exact_mod_cast (cutoff_pos order op).ne')]
  ring

end PrimeFactors.CircleMarkMidcutReadout
