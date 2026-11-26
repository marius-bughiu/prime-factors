import PrimeFactors.TraceFoldedRight
import PrimeFactors.ResidueCount
import Mathlib.Data.Fintype.BigOperators

/-! Whole local sum menus can be assigned to either side of the CRT join.
The cost minimized here is the complete count of left rows. -/

namespace PrimeFactors.SumMenuPartition

open Finset TraceFoldedRight

/-- Coverage is unaffected by a partition: every true sum gives a choice
in each of the two Cartesian products. -/
theorem true_row (right : Finset ℕ) (left : Finset ℕ) {p q n : ℕ}
    (pair : p*q=n) :
    (∀ m∈left, AdmissibleSum (n : ZMod m) ((p+q : ℕ) : ZMod m)) ∧
    (∀ m∈right, AdmissibleSum (n : ZMod m) ((p+q : ℕ) : ZMod m)) :=
  ⟨fun m _ => admissibleSum_of_factor_pair m pair, fun m _ => admissibleSum_of_factor_pair m pair⟩

/-- Cartesian row counts multiply to the total, independently of the partition. -/
theorem row_counts {ι α : Type*} [DecidableEq ι] (localMenus : ι → Finset α)
    (all right : Finset ι) (sub : right⊆all) :
    ((all\right).pi (fun i => localMenus i)).card * (right.pi (fun i => localMenus i)).card =
    (all.pi (fun i => localMenus i)).card := by
  simp only [Finset.card_pi]
  exact Finset.prod_sdiff sub

/-- A zero-fixed-point right table at capacity B covers 2B raw positions.
Every eligible assignment of the same menus needs at least as many left rows. -/
theorem optimal_at_cap {cap stored fixed raw otherLeft bestLeft : ℕ}
    (pos : 0<cap) (orbit : 2*stored=raw+fixed) (fits : stored≤cap)
    (sameTotal : bestLeft*(2*cap)=otherLeft*raw) : bestLeft≤otherLeft := by
  have raw_le : raw≤2*cap := by omega
  apply (Nat.mul_le_mul_right_iff (by omega : 0<2*cap)).mp
  exact sameTotal.le.trans (Nat.mul_le_mul_left _ raw_le)

/-- For N ≡ 1 mod 3, every admissible sum mod 3 differs from its negative. -/
theorem mod_three_not_fixed {s : ZMod 3} (ok : AdmissibleSum 1 s) : s≠-s := by
  obtain ⟨x,y,mul,add⟩ := ok
  rw [← add]
  exact (show ∀ x y : ZMod 3, x*y=1 → x+y≠-(x+y) by decide +kernel) x y mul

theorem half_of_mod_three {α : Type*} [LinearOrder α] (S : Finset α) (mate : α→α)
    (project : α→ZMod 3) (stable : ∀ x∈S, mate x∈S)
    (inv : ∀ x∈S, mate (mate x)=x)
    (allowed : ∀ x∈S, AdmissibleSum 1 (project x))
    (opposite : ∀ x∈S, project (mate x) = -project x) :
    2*(representatives S mate).card=S.card := by
  have empty : S.filter (fun x => x=mate x) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x mem
    obtain ⟨inside,eq⟩ := Finset.mem_filter.mp mem
    exact mod_three_not_fixed (allowed x inside) ((congrArg project eq).trans (opposite x inside))
  simpa only [empty, Finset.card_empty, Nat.add_zero] using orbit_count S mate stable inv

/-- Cardinality of the local menu at an odd prime, for evaluating selected right moduli. -/
noncomputable def primeChoices (n m : ℕ) : ℕ :=
  if h : m.Prime then
    letI : Fact m.Prime := ⟨h⟩
    (factorSumResidues m ((n%m : ℕ) : ZMod m)).card
  else 0

theorem primeChoices_square {n m r : ℕ} (prime : m.Prime) (odd : m≠2) (value : n%m=r)
    (nz : (r : ZMod m)≠0) (sq : IsSquare (r : ZMod m)) :
    primeChoices n m = (m+1)/2 := by
  letI : Fact m.Prime := ⟨prime⟩
  rw [primeChoices, dif_pos prime, value]
  exact card_factorSumResidues_of_square m odd _ nz sq

theorem primeChoices_nonsquare {n m r : ℕ} (prime : m.Prime) (value : n%m=r)
    (nz : (r : ZMod m)≠0) (nsq : ∀ t : ZMod m, (r : ZMod m)≠t*t) :
    primeChoices n m = (m-1)/2 := by
  letI : Fact m.Prime := ⟨prime⟩
  rw [primeChoices, dif_pos prime, value]
  exact card_factorSumResidues_of_nonsquare m _ nz (fun ⟨t,h⟩ => nsq t h)

end PrimeFactors.SumMenuPartition
