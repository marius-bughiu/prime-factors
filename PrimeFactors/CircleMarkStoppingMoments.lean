import PrimeFactors.CircleMarkTargetFrequency
import Mathlib.Algebra.BigOperators.Expect

/-! Moments of the first marked positive integer, for a uniformly selected
negative-Jacobi target at a fixed product. The observable uses the product
as its finite cutoff and counts the targets first reached at each step. -/
namespace PrimeFactors.CircleMarkStoppingMoments

open Finset CircleMarkTargetFrequency
open scoped BigOperators Classical

/-- Increase of the hit probability at positive coordinate `k`. -/
noncomputable def firstHitMass (n k : ℕ) [NeZero n] : ℚ :=
  rate n (Icc 1 k) - rate n (Icc 1 (k-1))

private theorem prefix_mono (n : ℕ) [NeZero n] {i j : ℕ} (h : i≤j) :
    hits n (Icc 1 i) ⊆ hits n (Icc 1 j) := by
  intro t ht
  obtain ⟨neg,x,xm,hx⟩ := mem_filter.mp ht
  exact mem_filter.mpr ⟨neg,x,Icc_subset_Icc_right h xm,hx⟩

/-- The finite difference counts exactly the targets newly hit at this step. -/
theorem firstHitMass_eq_count (n k : ℕ) [NeZero n] :
    firstHitMass n (k+1) =
      ((hits n (Icc 1 (k+1)) \ hits n (Icc 1 k)).card : ℚ) / (targets n).card := by
  have nested : hits n (Icc 1 k) ⊆ hits n (Icc 1 (k+1)) := prefix_mono n (Nat.le_succ k)
  rw [firstHitMass,Nat.add_sub_cancel,rate,rate,card_sdiff nested,
    Nat.cast_sub (card_le_card nested),sub_div]

/-- Raw moment of the first-hit step, summing all steps from 1 through n.
Both the target population and the prefix menus are specified by n. -/
noncomputable def rawMoment (n power : ℕ) [NeZero n] : ℚ :=
  ∑ k ∈ range n, ((k:ℚ)+1)^power * firstHitMass n (k+1)

/-- Least positive coordinate marking the given target within the public cutoff.
Zero records that the target was never hit. -/
noncomputable def rank (n : ℕ) [NeZero n] (t : ↥(targets n)) : ℕ :=
  if h : ∃ j, j≤n ∧ t.val∈hits n (Icc 1 j) then Nat.find h else 0

private theorem rank_le (n : ℕ) [NeZero n] (t : ↥(targets n)) : rank n t ≤ n := by
  unfold rank
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact Nat.zero_le _

theorem rank_eq_iff {n k : ℕ} [NeZero n] (t : ↥(targets n)) (kn : k<n) :
    rank n t = k+1 ↔ t.val ∈ hits n (Icc 1 (k+1)) \ hits n (Icc 1 k) := by
  rw [rank,mem_sdiff]
  split_ifs with existsHit
  · obtain ⟨_,first⟩ := Nat.find_spec existsHit
    constructor
    · intro eq
      refine ⟨eq ▸ first,fun early => ?_⟩
      have lower := Nat.find_min' existsHit (show k≤n ∧ t.val∈hits n (Icc 1 k) from ⟨kn.le,early⟩)
      omega
    · rintro ⟨now,prev⟩
      have upper := Nat.find_min' existsHit (show k+1≤n ∧ t.val∈hits n (Icc 1 (k+1)) from ⟨kn,now⟩)
      have low : ¬ Nat.find existsHit ≤ k := fun h => prev (prefix_mono n h first)
      omega
  · constructor
    · intro impossible
      exact impossible.elim
    · rintro ⟨now,_⟩
      exact (existsHit ⟨k+1,kn,now⟩).elim

private theorem rank_count {n k : ℕ} [NeZero n] (kn : k<n) :
    (univ.filter (fun t : ↥(targets n) => rank n t = k+1)).card =
      (hits n (Icc 1 (k+1)) \ hits n (Icc 1 k)).card := by
  apply card_bij (fun t _ => t.val)
  · intro t ht
    exact (rank_eq_iff t kn).mp (mem_filter.mp ht).2
  · intro t _ u _ eq
    exact Subtype.ext eq
  · intro t ht
    have eligible : t ∈ targets n := (mem_filter.mp (mem_sdiff.mp ht).1).1
    exact ⟨⟨t,eligible⟩,mem_filter.mpr ⟨mem_univ _,(rank_eq_iff ⟨t,eligible⟩ kn).mpr ht⟩,rfl⟩

/-- Each positive raw moment equals the average over the actual rank of
every eligible target, with an unhit target contributing zero. -/
theorem rawMoment_eq_target_mean (n power : ℕ) [NeZero n] (pos : 0<power) :
    rawMoment n power = 𝔼 t : ↥(targets n), (rank n t : ℚ)^power := by
  let f (k : ℕ) (t : ↥(targets n)) : ℚ := if rank n t = k+1 then ((k:ℚ)+1)^power else 0
  have steps (k : ℕ) (hk : k<n) :
      (∑ t, f k t) = ((hits n (Icc 1 (k+1)) \ hits n (Icc 1 k)).card:ℚ)*((k:ℚ)+1)^power := by
    simp only [f,←sum_filter,sum_const,nsmul_eq_mul,rank_count hk]
  have target (t : ↥(targets n)) : ∑ k∈range n, f k t = (rank n t:ℚ)^power := by
    cases r : rank n t with
    | zero => simp [f,r,zero_pow pos.ne']
    | succ j =>
      have hn : j<n := by have := rank_le n t; omega
      simp [f,r,hn]
  rw [Fintype.expect_eq_sum_div_card,Fintype.card_coe]
  calc
    _ = ∑ k∈range n, (∑ t, f k t)/(targets n).card := by
      apply sum_congr rfl
      intro k hk
      rw [steps k (mem_range.mp hk),firstHitMass_eq_count]
      ring
    _ = _ := by rw [←sum_div,sum_comm]; simp_rw [target]

private def component (r k : ℕ) : ℚ :=
  if k < (r-1)/2 then 1/((r:ℚ)-1) else 0

private theorem capped_step (r k : ℕ) :
    ((min (k+1) ((r-1)/2):ℕ):ℚ) / ((r:ℚ)-1)
      - ((min k ((r-1)/2):ℕ):ℚ) / ((r:ℚ)-1) = component r k := by
  by_cases low : k < (r-1)/2
  · rw [min_eq_left low,min_eq_left low.le,component,if_pos low,Nat.cast_add,Nat.cast_one]
    ring
  · rw [min_eq_right (by omega),min_eq_right (by omega),component,if_neg low,sub_self]

/-- The mass at k+1 contains one constant contribution from each prime whose
positive half-period has not yet been exhausted. -/
theorem mass_at {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (k : ℕ) :
    firstHitMass (p*q) (k+1) =
      (if k < (p-1)/2 then 1/((p:ℚ)-1) else 0) +
      (if k < (q-1)/2 then 1/((q:ℚ)-1) else 0) := by
  rw [firstHitMass,Nat.add_sub_cancel,first_hit diff op oq,first_hit diff op oq]
  change _ = component p k + component q k
  rw [←capped_step,←capped_step]
  ring

private def powerSum (power h : ℕ) : ℚ := ∑ k ∈ range h, ((k:ℚ)+1)^power

private theorem component_sum (n r power : ℕ) (bound : (r-1)/2 ≤ n) :
    ∑ k ∈ range n, ((k:ℚ)+1)^power * component r k =
      powerSum power ((r-1)/2) / ((r:ℚ)-1) := by
  have clipped : (range n).filter (fun k => k < (r-1)/2) = range ((r-1)/2) := by
    ext k
    simp only [mem_filter, mem_range]
    omega
  simp only [component, mul_ite, mul_one_div, mul_zero, ←sum_filter, clipped, powerSum, sum_div]

private theorem split_moment {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (power : ℕ) :
    rawMoment (p*q) power = powerSum power ((p-1)/2) / ((p:ℚ)-1) +
      powerSum power ((q-1)/2) / ((q:ℚ)-1) := by
  have pc : (p-1)/2 ≤ p*q := (Nat.div_le_self ..).trans
    ((Nat.sub_le p 1).trans (Nat.le_mul_of_pos_right p hq.out.pos))
  have qc : (q-1)/2 ≤ p*q := (Nat.div_le_self ..).trans
    ((Nat.sub_le q 1).trans (Nat.le_mul_of_pos_left q hp.out.pos))
  unfold rawMoment
  have step (k : ℕ) : firstHitMass (p*q) (k+1) = component p k + component q k :=
    mass_at diff op oq k
  simp_rw [step, mul_add]
  rw [sum_add_distrib, component_sum _ _ _ pc, component_sum _ _ _ qc]

private theorem sums (h : ℕ) :
    powerSum 1 h = (h:ℚ)*(h+1)/2 ∧
    powerSum 2 h = (h:ℚ)*(h+1)*(2*h+1)/6 := by
  induction h with
  | zero => norm_num [powerSum]
  | succ h ih =>
    have step (k : ℕ) : powerSum k (h+1) = powerSum k h + ((h:ℚ)+1)^k := sum_range_succ ..
    rw [step,step,ih.1,ih.2,Nat.cast_succ]
    constructor <;> ring

private theorem single_prime (r : ℕ) [hr : Fact r.Prime] (odd : r≠2) :
    powerSum 1 ((r-1)/2) / ((r:ℚ)-1) = (r+1)/8 ∧
    powerSum 2 ((r-1)/2) / ((r:ℚ)-1) = r*(r+1)/24 := by
  obtain ⟨k,rk⟩ := hr.out.odd_of_ne_two odd
  have half : (r-1)/2 = k := by omega
  have cast : (r:ℚ) = 2*(k:ℚ)+1 := by exact_mod_cast rk
  have den : (r:ℚ)-1 ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hr.out.one_lt))
  rw [half,(sums k).1,(sums k).2]
  constructor <;> field_simp <;> rw [cast] <;> ring

/-- At an odd semiprime every eligible target is reached by the public cutoff,
so its rank is an actual positive first-hit coordinate. -/
theorem rank_positive {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (t : ↥(targets (p*q))) :
    0 < rank (p*q) t := by
  have half (r : ℕ) [hr : Fact r.Prime] (odd : r≠2) (bound : r ≤ p*q) :
      ((min (p*q) ((r-1)/2):ℕ):ℚ)/((r:ℚ)-1) = 1/2 := by
    rw [min_eq_right ((Nat.div_le_self ..).trans ((Nat.sub_le r 1).trans bound))]
    obtain ⟨k,rk⟩ := hr.out.odd_of_ne_two odd
    rw [show (r-1)/2=k by omega]
    have cast : (r:ℚ)=2*(k:ℚ)+1 := by exact_mod_cast rk
    have den : (r:ℚ)-1 ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hr.out.one_lt))
    field_simp
    linarith
  have cdf := first_hit diff op oq (p*q)
  rw [half p op (Nat.le_mul_of_pos_right _ hq.out.pos),
    half q oq (Nat.le_mul_of_pos_left _ hp.out.pos)] at cdf
  norm_num at cdf
  have nonzero : ((targets (p*q)).card:ℚ) ≠ 0 := by
    exact_mod_cast (card_pos.mpr ⟨t.val,t.property⟩).ne'
  have total := (div_eq_one_iff_eq nonzero).mp cdf
  have allHits : hits (p*q) (Icc 1 (p*q)) = targets (p*q) :=
    eq_of_subset_of_card_le (filter_subset ..) (by exact_mod_cast total.ge)
  have existsHit : ∃ j, j≤p*q ∧ t.val∈hits (p*q) (Icc 1 j) :=
    ⟨p*q,le_rfl,allHits.symm ▸ t.property⟩
  rw [rank,dif_pos existsHit]
  obtain ⟨_,x,hx,_⟩ := mem_filter.mp (Nat.find_spec existsHit).2
  exact (mem_Icc.mp hx).1.trans (mem_Icc.mp hx).2

/-- Expected first-hit step for uniform negative-Jacobi targets. -/
theorem first_moment {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) :
    rawMoment (p*q) 1 = ((p:ℚ)+q+2)/8 := by
  rw [split_moment diff op oq,(single_prime p op).1,(single_prime q oq).1]
  ring

/-- Expected square of the first-hit step for the same finite population. -/
theorem second_moment {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) :
    rawMoment (p*q) 2 = ((p:ℚ)*(p+1)+q*(q+1))/24 := by
  rw [split_moment diff op oq,(single_prime p op).2,(single_prime q oq).2]
  ring

end PrimeFactors.CircleMarkStoppingMoments
