import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PrimeFactors

open Finset

/-- For the orientation `h=q*u+1`, the opposite CRT sign at the odd prime `p`
forces the step of the reference grid to be a unit modulo `p`. -/
theorem phaseBlocks_unit {p q u : ℕ} (prime : p.Prime) (odd : p ≠ 2)
    (opposite : p ∣ q*u+2) : p.Coprime u := by
  apply prime.coprime_iff_not_dvd.mpr
  intro bad
  have prod := dvd_mul_of_dvd_right bad q
  have two : p ∣ 2 := (Nat.dvd_add_iff_right prod).mpr opposite
  exact odd (le_antisymm (Nat.le_of_dvd (by decide) two) prime.two_le)

private theorem phaseBlocks_spread {s : Finset ℕ} (v : ℕ → ℤ) (K : ℕ)
    (inj : Set.InjOn v s)
    (span : ∀ i ∈ s, ∀ j ∈ s, v i - v j ≤ K) : s.card ≤ K+1 := by
  classical
  by_cases h : s.Nonempty
  · let T := s.image v
    have hT : T.Nonempty := h.image _
    obtain ⟨j, hj, eq⟩ := mem_image.mp (min'_mem T hT)
    have sub : T ⊆ Icc (T.min' hT) (T.min' hT + K) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      have top := span i hi j hj
      rw [eq] at top
      exact mem_Icc.mpr ⟨min'_le T _ (mem_image_of_mem _ hi), by omega⟩
    have bound := card_le_card sub
    rw [Int.card_Icc] at bound
    rw [← card_image_of_injOn inj]
    change T.card ≤ _
    omega
  · simp [not_nonempty_iff_eq_empty.mp h]

/-- For any shifted half-circle, count a whole `p`-step block in integer coordinates.
`w i` is the period chosen to put a hit inside the same half-open lifted interval. -/
theorem phaseBlocks_half_card {p q u d : ℕ} (qPos : 0 < q) (pq : p ≤ q)
    (unit : p.Coprime (u*d)) (base start : ℤ) (w : ℕ → ℤ) (s : Finset ℕ)
    (indices : s ⊆ range p)
    (inside : ∀ i ∈ s,
      let coord := base + 4*((q:ℤ)*u+1)*d*i - 4*p*q*w i
      start ≤ coord ∧ coord < start + 2*p*q) :
    s.card ≤ p/2+d+1 := by
  let v (i : ℕ) : ℤ := (u:ℤ)*d*i - p*w i
  have inj : Set.InjOn v s := by
    intro i hi j hj eq
    have modEq : (u*d)*i ≡ (u*d)*j [MOD p] := by
      apply Int.natCast_modEq_iff.mp
      apply Int.modEq_iff_dvd.mpr
      use w j-w i
      push_cast
      change (u:ℤ)*d*i-p*w i = (u:ℤ)*d*j-p*w j at eq
      linear_combination -eq
    exact (Nat.ModEq.cancel_left_of_coprime unit modEq).eq_of_lt_of_lt
      (mem_range.mp (indices hi)) (mem_range.mp (indices hj))
  apply phaseBlocks_spread v _ inj
  intro i hi j hj
  have ai := (inside i hi).2
  have aj := (inside j hj).1
  have jj : j < q := (mem_range.mp (indices hj)).trans_le pq
  have dPos : 0 ≤ (d:ℤ) := Int.natCast_nonneg _
  have jBound : (d:ℤ)*j ≤ d*q := mul_le_mul_of_nonneg_left (by exact_mod_cast jj.le) dPos
  have iBound : 0 ≤ (d:ℤ)*i := mul_nonneg dPos (Int.natCast_nonneg _)
  have scaled : (q:ℤ)*(2*(v i-v j)) < q*((p:ℤ)+2*d) := by
    dsimp [v]
    linarith
  have raw := (mul_lt_mul_left (show (0:ℤ) < q by exact_mod_cast qPos)).mp scaled
  rw [Nat.cast_add]
  omega


/-- Exact integer half-open arcs give both sides of the discrepancy bound. Translating the
base admits a block that wraps around any number of times. -/
theorem phaseBlocks_imbalance {p q u d : ℕ} (pPos : 0 < p) (qPos : 0 < q) (pq : p ≤ q)
    (odd : p%2=1) (unit : p.Coprime (u*d)) (base start : ℤ) :
    let inArc := fun i : ℕ => (base+4*((q:ℤ)*u+1)*d*i-start) % (4*p*q) < 2*p*q
    |2 * (((range p).filter inArc).card : ℤ) - p| ≤ 1+2*d := by
  let m : ℤ := 4*p*q
  let half : ℤ := 2*p*q
  let coord (i : ℕ) : ℤ := base+4*((q:ℤ)*u+1)*d*i
  let w (i : ℕ) : ℤ := (coord i-start)/m
  let inArc (i : ℕ) := (coord i-start)%m < half
  change |2 * (((range p).filter inArc).card : ℤ) - p| ≤ 1+2*d
  have mPos : 0 < m := by dsimp [m]; positivity
  have split (i : ℕ) : coord i - m*w i = start + (coord i-start)%m := by
    have div := Int.emod_add_ediv (coord i-start) m
    dsimp [w]
    omega
  have yes := phaseBlocks_half_card qPos pq unit base start w ((range p).filter inArc)
    (filter_subset _ _) (by
      intro i hi
      change start ≤ coord i-m*w i ∧ coord i-m*w i < start+half
      rw [split]
      have upper : (coord i-start)%m < half := (mem_filter.mp hi).2
      have lower := Int.emod_nonneg (coord i-start) mPos.ne'
      omega)
  have no := phaseBlocks_half_card qPos pq unit base (start+half) w ((range p).filter (¬inArc ·))
    (filter_subset _ _) (by
      intro i hi
      change start+half ≤ coord i-m*w i ∧ coord i-m*w i < start+half+half
      rw [split]
      have lower : ¬ (coord i-start)%m < half := (mem_filter.mp hi).2
      have upper := Int.emod_lt_of_pos (coord i-start) mPos
      have eq : m = half+half := by dsimp [m, half]; ring
      omega)
  have parts := (range p).filter_card_add_filter_neg_card_eq_card inArc
  rw [card_range] at parts
  apply abs_le.mpr
  omega


/-- A row needs one bound per full block, plus its exact remainder length. -/
theorem phaseBlocks_partial (f : ℕ → ℤ) (p H : ℕ) (C : ℤ)
    (bounded : ∀ i, |f i| ≤ 1) (block : ∀ L, |∑ i ∈ range p, f (L+i)| ≤ C) :
    |∑ i ∈ range H, f i| ≤ (H/p : ℕ)*C+(H%p : ℕ) := by
  have full (k : ℕ) : |∑ i ∈ range (k*p), f i| ≤ (k:ℤ)*C := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, sum_range_add, Nat.cast_succ, add_mul, one_mul]
      exact (abs_add_le ..).trans (add_le_add ih (block _))
  have tail (L r : ℕ) : |∑ i ∈ range r, f (L+i)| ≤ (r:ℤ) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [sum_range_succ, Nat.cast_succ]
      exact (abs_add_le ..).trans (add_le_add ih (bounded _))
  have eq : H/p*p+H%p=H := by rw [Nat.mul_comm, Nat.add_comm, Nat.mod_add_div]
  calc
    _ = |∑ i ∈ range (H/p*p+H%p), f i| := by rw [eq]
    _ ≤ _ := by
      rw [sum_range_add]
      exact (abs_add_le ..).trans (add_le_add (full _) (tail _ _))

end PrimeFactors
