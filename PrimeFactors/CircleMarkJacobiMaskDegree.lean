import PrimeFactors.CircleMarkJacobiMask
import PrimeFactors.CircleMarkTargetFrequency

/-! Degree required for a complete sum weighted by the square of an integer
polynomial. The local contributions count the two signs among its roots. -/
namespace PrimeFactors.CircleMarkJacobiMaskDegree

open Finset Polynomial CircleMarkJacobiMask
open scoped Classical
open private PrimeFactors.CircleMarkTargetFrequency.plus PrimeFactors.CircleMarkTargetFrequency.minus
  PrimeFactors.CircleMarkTargetFrequency.local_cards PrimeFactors.CircleMarkTargetFrequency.sign_cases
  from PrimeFactors.CircleMarkTargetFrequency
open CircleMarkTargetFrequency (plus minus local_cards sign_cases)

abbrev half (r : ℕ) := (r-1)/2

/-- Roots of the given nonzero quadratic-character sign. -/
noncomputable def signedRoots (r : ℕ) [Fact r.Prime] (Q : ℤ[X]) (s : ℤ) : Finset (ZMod r) :=
  (rootSet r Q).filter fun t => quadraticChar (ZMod r) t=s

theorem local_difference {r : ℕ} [Fact r.Prime] (op : r≠2) (Q : ℤ[X]) :
    localSum r Q=((signedRoots r Q (-1)).card:ℤ)-(signedRoots r Q 1).card := by
  have term (x : ZMod r) : quadraticChar (ZMod r) x =
      (if quadraticChar (ZMod r) x=1 then (1:ℤ) else 0) -
      (if quadraticChar (ZMod r) x= -1 then (1:ℤ) else 0) := by
    by_cases z : x=0
    · simp [z,quadraticChar_zero]
    · rcases quadraticChar_dichotomy z with h|h <;> simp [h]
  rw [local_eq op Q, sum_congr rfl (fun x _ => term x),sum_sub_distrib,sum_boole,sum_boole]
  simp only [signedRoots,neg_sub]

private theorem sign_caps {r : ℕ} [Fact r.Prime] (op : r≠2) (Q : ℤ[X]) :
    (signedRoots r Q (-1)).card≤half r ∧ (signedRoots r Q 1).card≤half r := by
  have m : signedRoots r Q (-1)⊆minus r := fun _ hx => (sign_cases _).2.mpr (mem_filter.mp hx).2
  have p : signedRoots r Q 1⊆plus r := fun _ hx => (sign_cases _).1.mpr (mem_filter.mp hx).2
  exact ⟨(card_le_card m).trans_eq (local_cards r op).2,(card_le_card p).trans_eq (local_cards r op).1⟩

private theorem zero_sum {r : ℕ} [Fact r.Prime] (op : r≠2) {Q : ℤ[X]}
    (zero : Q.map (Int.castRingHom (ZMod r))=0) : localSum r Q=0 := by
  rw [local_eq op Q]
  have all : rootSet r Q=univ := by simp [CircleMarkJacobiMask.rootSet,zero]
  rw [all,quadraticChar_sum_zero (by rwa [ZMod.ringChar_zmod_n]),neg_zero]

private theorem degree_cap {r : ℕ} [Fact r.Prime] {Q : ℤ[X]} (nz : Q.map (Int.castRingHom (ZMod r))≠0) :
    (rootSet r Q).card≤Q.natDegree := by
  apply le_trans _ (natDegree_map_le (f:=Int.castRingHom (ZMod r)) (p:=Q))
  apply card_le_degree_of_subset_roots
  intro x hx
  exact (mem_roots nz).mpr (mem_filter.mp hx).2

/-- Both the number of available signs and the polynomial degree bound a local bias.
A polynomial that vanishes identically modulo the prime contributes zero. -/
theorem local_bound {r : ℕ} [Fact r.Prime] (op : r≠2) (Q : ℤ[X]) :
    |localSum r Q|≤(min (half r) Q.natDegree:ℕ) := by
  by_cases zero : Q.map (Int.castRingHom (ZMod r))=0
  · rw [zero_sum op zero,abs_zero]; exact Int.natCast_nonneg _
  have roots := degree_cap zero
  obtain ⟨a,b⟩ := sign_caps op Q
  have small (s : ℤ) : (signedRoots r Q s).card≤Q.natDegree :=
    (card_le_card (filter_subset ..)).trans roots
  have A := le_min a (small (-1))
  have B := le_min b (small 1)
  rw [local_difference op Q,abs_le]
  omega

/-- Bounds for the full complete sum at every polynomial, including reductions
that vanish identically at one or both primes. -/
theorem total_bound {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (op : p≠2) (oq : q≠2) (Q : ℤ[X]) :
    |globalSum (p*q) Q| ≤ ((min (half p) Q.natDegree * min (half q) Q.natDegree : ℕ):ℤ) := by
  rw [factorization diff Q,abs_mul,Nat.cast_mul]
  exact mul_le_mul (local_bound op Q) (local_bound oq Q) (abs_nonneg _) (Int.natCast_nonneg _)

/-- The prefix mask attains the exact maximum absolute complete sum among
all integer polynomial masks of degree at most d. -/
theorem maximum {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (op : p≠2) (oq : q≠2) (d : ℕ) :
    IsGreatest {a : ℤ | ∃ Q : ℤ[X], Q.natDegree≤d ∧ a=|globalSum (p*q) Q|}
      ((min (half p) d * min (half q) d : ℕ):ℤ) := by
  constructor
  · refine ⟨prefixMask d,(degree_prefix d).le,?_⟩
    rw [prefix_sum diff op oq,abs_of_nonneg (by positivity),Nat.cast_mul]
    simp only [half,min_comm]
  · rintro a ⟨Q,deg,rfl⟩
    exact (total_bound diff op oq Q).trans (by
      exact_mod_cast (Nat.mul_le_mul (min_le_min_left (half p) deg) (min_le_min_left (half q) deg)))

theorem linear_bound {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (op : p≠2) (oq : q≠2) (Q : ℤ[X]) :
    |globalSum (p*q) Q| ≤ ((half p * Q.natDegree : ℕ):ℤ) :=
  (total_bound diff op oq Q).trans (by
    exact_mod_cast (Nat.mul_le_mul (min_le_left (half p) Q.natDegree) (min_le_right (half q) Q.natDegree)))

/-- An error allowance E permits at most floor(E/u) degrees below the
requested amplitude K*u, where u is the smaller prime's half period. -/
theorem near_degree {p q K E : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (Q : ℤ[X])
    (near : |globalSum (p*q) Q-((half p*K:ℕ):ℤ)|≤E) :
    K≤Q.natDegree+E/(half p) := by
  have cap := (abs_le.mp (linear_bound order.ne op oq Q)).2
  have low := (abs_le.mp near).1
  have b : half p*K≤half p*Q.natDegree+E := by omega
  have pos : 0<half p := by have := hp.out.two_le; unfold half; omega
  have remainder : (K-Q.natDegree)*half p≤E := by
    rw [Nat.mul_comm,Nat.mul_sub]; omega
  have div := (Nat.le_div_iff_mul_le pos).mpr remainder
  omega

theorem exact_degree {p q K : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (Q : ℤ[X])
    (same : globalSum (p*q) Q=((half p*K:ℕ):ℤ)) : K≤Q.natDegree := by
  simpa using near_degree (K:=K) (E:=0) order op oq Q (by rw [same]; simp)

/-- Matching the square prefix at the public midpoint requires at least the
degree of that prefix, independently of the integer coefficients chosen. -/
theorem midcut_minimal {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (Q : ℤ[X])
    (same : globalSum (p*q) Q=globalSum (p*q) (prefixMask (CircleMarkMidcutReadout.cutoff (p*q)))) :
    CircleMarkMidcutReadout.cutoff (p*q)≤Q.natDegree := by
  apply exact_degree order op oq Q
  simpa only [midcut_sum order op oq,Nat.cast_mul,half,mul_comm] using same

/-- At positive equality in the linear bound, both local absolute values
saturate and the local contributions have matching signs. -/
theorem extreme_signs {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (Q : ℤ[X]) (dp : 0<Q.natDegree)
    (same : globalSum (p*q) Q=((half p*Q.natDegree:ℕ):ℤ)) :
    (localSum p Q=half p ∧ localSum q Q=Q.natDegree) ∨
      (localSum p Q= -(half p:ℤ) ∧ localSum q Q= -(Q.natDegree:ℤ)) := by
  let u := half p
  let d := Q.natDegree
  have pos : 0<u := by have := hp.out.two_le; dsimp [u,half]; omega
  have pe : |localSum p Q|≤(u:ℤ) :=
    (local_bound op Q).trans (by exact_mod_cast min_le_left (half p) Q.natDegree)
  have qe : |localSum q Q|≤(d:ℤ) :=
    (local_bound oq Q).trans (by exact_mod_cast min_le_right (half q) Q.natDegree)
  rw [factorization order.ne Q,Nat.cast_mul] at same
  have ap : |localSum p Q|=(u:ℤ) := by
    apply le_antisymm pe
    by_contra! small
    have less := (mul_le_mul_of_nonneg_left qe (abs_nonneg (localSum p Q))).trans_lt
      (mul_lt_mul_of_pos_right small (by exact_mod_cast dp : (0:ℤ)<d))
    rw [←abs_mul,same,abs_of_nonneg (by positivity)] at less
    exact lt_irrefl _ less
  have un : (u:ℤ)≠0 := by exact_mod_cast pos.ne'
  rcases (abs_eq (Int.natCast_nonneg u)).mp ap with h|h
  · rw [h] at same
    exact Or.inl ⟨h,mul_left_cancel₀ un same⟩
  · rw [h,neg_mul,neg_eq_iff_eq_neg,←mul_neg] at same
    exact Or.inr ⟨h,mul_left_cancel₀ un same⟩

/-- Reaching either positive local cap requires exactly c roots of the
winning sign and no roots of the opposite sign. A root at zero has weight zero. -/
theorem extreme_counts {r c : ℕ} [Fact r.Prime] (op : r≠2) (Q : ℤ[X])
    (cp : 0<c) (cap : c=half r ∨ c=Q.natDegree) :
    (localSum r Q=c ↔ (signedRoots r Q (-1)).card=c ∧ (signedRoots r Q 1).card=0) ∧
    (localSum r Q= -(c:ℤ) ↔ (signedRoots r Q 1).card=c ∧ (signedRoots r Q (-1)).card=0) := by
  by_cases z : Q.map (Int.castRingHom (ZMod r))=0
  · have a := local_difference op Q
    rw [zero_sum op z] at a ⊢
    omega
  · have limits : (signedRoots r Q (-1)).card≤c ∧ (signedRoots r Q 1).card≤c := by
      rcases cap with h|h <;> rw [h]
      · exact sign_caps op Q
      · exact ⟨(card_le_card (filter_subset ..)).trans (degree_cap z),
          (card_le_card (filter_subset ..)).trans (degree_cap z)⟩
    rw [local_difference op Q]
    omega

end PrimeFactors.CircleMarkJacobiMaskDegree
