import PrimeFactors.PeriodicSumRank
import PrimeFactors.ToyResidueOrderCost
import PrimeFactors.SumIntervalExclusion

/-! Exact cumulative counts of the modulo-4 and modulo-25 tests, from a
public lower bound through the target sum inclusive. -/

open private PrimeFactors.ProductDeficitBand.left_cap from PrimeFactors.ProductDeficitBand

namespace PrimeFactors.FactorSumPrefixCost

open Finset PeriodicSumRank
open scoped Classical

noncomputable def passingPrefix (n lo s : ℕ) : Finset ℕ :=
  (Ico lo (s+1)).filter fun x => passes (n%100) (x%100)=true

noncomputable def favoredPrefix (n lo s : ℕ) : Finset ℕ :=
  (passingPrefix n lo s).filter fun x => favored (n%100) (x%100)=true

private theorem split_card (P : ℕ → Prop) [DecidablePred P] {a b c : ℕ} (ab : a≤b) (bc : b≤c) :
    ((Ico a c).filter P).card = ((Ico a b).filter P).card + ((Ico b c).filter P).card := by
  rw [←Ico_union_Ico_eq_Ico ab bc,filter_union,card_union_of_disjoint]
  exact (Ico_disjoint_Ico_consecutive a b c).mono (filter_subset ..) (filter_subset ..)

private theorem whole_blocks (P : ℕ → Prop) [DecidablePred P] (c : ℕ)
    (full : ∀ a : ℕ, ((Ico a (a+100)).filter P).card=c) (lo k : ℕ) :
    ((Ico lo (lo+100*k)).filter P).card=c*k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show lo+100*(k+1)=lo+100*k+100 by omega,
      split_card P (by omega : lo≤lo+100*k) (by omega : lo+100*k≤lo+100*k+100),
      ih,full,Nat.mul_succ]

private theorem square_digit {n : ℕ} (sq : n%5=1 ∨ n%5=4) :
    (n%100)%5=1 ∨ (n%100)%5=4 := by
  simpa only [Nat.mod_mod_of_dvd n (by decide : 5∣100)] using sq

/-- When the target passes, its one-based ascending rank counts exactly
the passing integers through the target, including the final square test. -/
theorem ascending_card {n lo hi s : ℕ} (sq : n%5=1 ∨ n%5=4) (lower : lo≤s)
    (upper : s≤hi) (hit : passes (n%100) (s%100)=true) :
    (positions n lo hi s).1 = (passingPrefix n lo s).card := by
  let P (x : ℕ) := passes (n%100) (x%100)=true
  letI : DecidablePred P := fun x => inferInstanceAs (Decidable (passes (n%100) (x%100)=true))
  let k := (s-lo)/100
  let start := lo+100*k
  have inside : start≤s ∧ s<start+100 := by dsimp [start,k]; omega
  have paid := whole_blocks P 7 (fun a => by
    simpa only [window,P,show a+99+1=a+100 by omega,min_self] using
      complete_count (Nat.mod_lt n (by decide)) (square_digit sq) a) lo k
  have before : (window (n%100) start hi).filter (·<s) = (Ico start s).filter P := by
    ext x
    simp only [window,mem_filter,mem_Ico,lt_min_iff,P]
    constructor
    · intro h
      exact ⟨⟨h.1.1.1,h.2⟩,h.1.2⟩
    · intro h
      exact ⟨⟨⟨h.1.1,h.1.2.trans inside.2,Nat.lt_succ_of_le (h.1.2.le.trans upper)⟩,h.2⟩,h.1.2⟩
  have last : ((Ico s (s+1)).filter P).card=1 := by simp [filter_singleton,P,hit]
  change 7*k+(1+((window (n%100) start hi).filter (·<s)).card) = ((Ico lo (s+1)).filter P).card
  rw [before,split_card P (by dsimp [start]; omega : lo≤start) (by omega : start≤s+1),
    paid,split_card P inside.1 (Nat.le_succ s),last]
  omega

/-- Counting the first priority group across the entire prefix, including
any passing favored target. This identity also holds at an unfavored endpoint. -/
theorem favored_card {n lo s : ℕ} (sq : n%5=1 ∨ n%5=4) (lower : lo≤s) :
    firstGroupCost n lo s = (favoredPrefix n lo s).card := by
  let P (x : ℕ) := passes (n%100) (x%100)=true ∧ favored (n%100) (x%100)=true
  letI : DecidablePred P := fun x => inferInstanceAs
    (Decidable (passes (n%100) (x%100)=true ∧ favored (n%100) (x%100)=true))
  let k := (s-lo)/100
  let start := lo+100*k
  have inside : start≤s ∧ s<start+100 := by dsimp [start,k]; omega
  have size := (row_sizes ⟨n%100,Nat.mod_lt _ (by decide)⟩ (square_digit sq)).1
  have paid := whole_blocks P 2 (fun a => by
    simpa only [window,show a+99+1=a+100 by omega,min_self,filter_filter,P] using
      (complete_group (r:=n%100) a true).trans size) lo k
  unfold favoredPrefix passingPrefix firstGroupCost
  simp only [window,filter_filter]
  change 2*k + ((Ico start (min (start+100) (s+1))).filter P).card =
    ((Ico lo (s+1)).filter P).card
  rw [min_eq_right (by omega),split_card P (by dsimp [start]; omega : lo≤start)
    (by omega : start≤s+1),paid]

/-- With a favored target, the complete-prefix counts have slope two
against seven, with at most ten units of rounding after cross multiplication. -/
theorem favored_prefix_bound {n lo s : ℕ} (sq : n%5=1 ∨ n%5=4) (lower : lo≤s)
    (hit : passes (n%100) (s%100)=true) (special : favored (n%100) (s%100)=true) :
    0 < (favoredPrefix n lo s).card ∧
    7*(favoredPrefix n lo s).card ≤ 2*(passingPrefix n lo s).card+10 := by
  rw [←favored_card sq lower,←ascending_card sq lower (le_refl s) hit]
  exact favored_cost sq lower le_rfl hit special

theorem distant_prefix_bound {n lo s : ℕ} (sq : n%5=1 ∨ n%5=4) (far : lo+10000≤s)
    (hit : passes (n%100) (s%100)=true) (special : favored (n%100) (s%100)=true) :
    10*(favoredPrefix n lo s).card ≤ 3*(passingPrefix n lo s).card := by
  have lower : lo≤s := by omega
  rw [←favored_card sq lower,←ascending_card sq lower (le_refl s) hit]
  exact long_favored_cost sq far le_rfl hit special

/-- In the factor-width window, an integer passing the public residue tests
has square discriminant exactly when it is the true sum. -/
theorem pass_square_iff {p q A t : ℕ} (size : 2≤A) (pl : A≤p) (pq : p≤q)
    (pp : p.Prime) (qp : q.Prime) (low : ceilSqrt (4*(p*q))≤t)
    (high : t≤ProductDeficitBand.sumCap (p*q) A)
    (pass : passes ((p*q)%100) (t%100)=true) : IsSquare (t^2-4*(p*q)) ↔ t=p+q := by
  obtain ⟨four,localSum⟩ := (passes_iff (p*q) t).mp pass
  apply ToyResidueOrderCost.square_iff size pl pq pp qp
  apply List.mem_filter.mpr
  refine ⟨ToySumIsolation.mem_menu.mpr ⟨low,high,four⟩,?_⟩
  exact (ToyResidueOrderCost.residue_test ⟨(p*q)%25,Nat.mod_lt _ (by decide)⟩
    ⟨t%25,Nat.mod_lt _ (by decide)⟩).mpr (by simpa only [ZMod.natCast_mod] using localSum)

/-- For two distinct odd primes in the given width with favored true sum,
the square tests up to and including that sum contain exactly one success
in each traversal. The equalities count every test in the two prefixes. -/
theorem semiprime_prefixes {p q A : ℕ} (size : 3≤A) (pl : A≤p) (pq : p<q) (qu : q<2*A)
    (pp : p.Prime) (qp : q.Prime) (sq : (p*q)%5=1 ∨ (p*q)%5=4)
    (special : favored ((p*q)%100) ((p+q)%100)=true) :
    let n := p*q
    let lo := ceilSqrt (4*n)
    let hi := ProductDeficitBand.sumCap n A
    let s := p+q
    (positions n lo hi s).1 = (passingPrefix n lo s).card ∧
    firstGroupCost n lo s = (favoredPrefix n lo s).card ∧
    (passingPrefix n lo s).filter (fun t => IsSquare (t^2-4*n)) = {s} ∧
    (favoredPrefix n lo s).filter (fun t => IsSquare (t^2-4*n)) = {s} := by
  dsimp only
  have low := ceilSqrt_le_iff.mpr (balanced_factorSum_bounds pq.le (by omega : q≤2*p)).1
  have high : p+q ≤ ProductDeficitBand.sumCap (p*q) A := le_min
    (PrimeFactors.ProductDeficitBand.left_cap (by omega) pl (pl.trans pq.le))
    (CenteredSumQuartic.sum_upper rfl (by omega) (by omega) (by omega))
  have four := SumIntervalExclusion.sum_congruence (Nat.odd_iff.mp
    ((pp.odd_of_ne_two (by omega)).mul (qp.odd_of_ne_two (by omega))))
  have hit := (passes_iff (p*q) (p+q)).mpr ⟨four,admissibleSum_of_factor_pair 25 rfl⟩
  refine ⟨ascending_card sq low high hit,favored_card sq low,?_,?_⟩
  all_goals
    ext t
    simp only [favoredPrefix,passingPrefix,mem_filter,mem_Ico,mem_singleton]
    constructor
    · intro h
      have bound : t < p+q+1 := by tauto
      apply (pass_square_iff (by omega : 2≤A) pl pq.le pp qp (by tauto)
        (by omega) (by tauto)).mp (by tauto)
    · rintro rfl
      have success := (pass_square_iff (by omega : 2≤A) pl pq.le pp qp low high hit).mpr rfl
      have lt := Nat.lt_succ_self (p+q)
      tauto

/-- The public interval starts at 5387. Its first fourteen passing sums
include four in the favored group, with true sum 5586 last in both prefixes. -/
theorem worked_prefix :
    (passingPrefix 7253249 5387 5586).card=14 ∧
    favoredPrefix 7253249 5387 5586={5414,5486,5514,5586} := by decide +kernel

end PrimeFactors.FactorSumPrefixCost
