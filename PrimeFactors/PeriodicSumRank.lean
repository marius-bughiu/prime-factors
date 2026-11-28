import PrimeFactors.PrimePower
import PrimeFactors.ProductDeficitBand
import PrimeFactors.Certificate
import Mathlib.Tactic

/-! The cost of prioritizing the two singular sum residues inside each
successive block of 100 integers. The appended blocks retain their order.
The entire change in work on one product occurs in the block of the true sum. -/
namespace PrimeFactors.PeriodicSumRank

open Finset

private def square25 (x : ℕ) := [0,1,4,6,9,11,14,16,19,21,24].contains (x%25)

/-- Public modulo-four and modulo-25 tests on the two residue representatives. -/
def passes (r s : ℕ) : Bool :=
  (s%4 == (r+1)%4) && square25 ((s%25)^2+100-4*(r%25))

def favored (r s : ℕ) : Bool := (s*s)%5 == 4*r%5

noncomputable def row (r : ℕ) (high : Bool) :=
  (range 100).filter fun s => passes r s = true ∧ favored r s = high

theorem row_sizes : ∀ r : Fin 100, r.val%5=1 ∨ r.val%5=4 →
    (row r.val true).card=2 ∧ (row r.val false).card=5 := by decide +kernel

/-- The finite lookup computes precisely the modular factor-sum criterion. -/
theorem lookup : ∀ r s : Fin 25, square25 (s.val^2+100-4*r.val) = true ↔
    AdmissibleSum (r.val : ZMod 25) (s.val : ZMod 25) := by
  have two : IsUnit (2 : ZMod 25) := (ZMod.isUnit_iff_coprime _ _).mpr (by decide)
  simp only [admissibleSum_iff_isSquare_of_two_unit two,isSquare_iff_exists_sq]
  decide +kernel

theorem passes_iff (n s : ℕ) : passes (n%100) (s%100)=true ↔
    s%4=(n+1)%4 ∧ AdmissibleSum (n : ZMod 25) (s : ZMod 25) := by
  have r25 := Nat.mod_mod_of_dvd n (by decide : 25∣100)
  have s25 := Nat.mod_mod_of_dvd s (by decide : 25∣100)
  have s4 := Nat.mod_mod_of_dvd s (by decide : 4∣100)
  have n4 : (n%100+1)%4=(n+1)%4 := by omega
  have eq := lookup ⟨n%25,Nat.mod_lt _ (by decide)⟩ ⟨s%25,Nat.mod_lt _ (by decide)⟩
  simp only [ZMod.natCast_mod] at eq
  simp only [passes,Bool.and_eq_true,beq_iff_eq,r25,s25,s4,n4,eq]

/-- The candidates in a block of up to 100 consecutive sums, clipped at the
inclusive upper end of the public factor-width window. -/
noncomputable def window (r l hi : ℕ) : Finset ℕ :=
  (Ico l (min (l+100) (hi+1))).filter (fun x => passes r (x%100)=true)

theorem complete_group {r : ℕ} (l : ℕ) (high : Bool) :
    ((window r l (l+99)).filter (fun x => favored r (x%100)=high)).card=(row r high).card := by
  have mem {x : ℕ} : x∈window r l (l+99) ↔ l≤x ∧ x<l+100 ∧ passes r (x%100)=true := by
    simp only [window,mem_filter,mem_Ico,show l+99+1=l+100 by omega,min_self,and_assoc]
  refine card_bij' (fun x _ => x%100) (fun a _ => l+(a+100-l%100)%100) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨inside,cls⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),(mem.mp inside).2.2,cls⟩
  · intro a ha
    obtain ⟨small,pass,cls⟩ := mem_filter.mp ha
    have bound := mem_range.mp small
    have residue : (l+(a+100-l%100)%100)%100=a := by omega
    change l+(a+100-l%100)%100 ∈ _
    exact mem_filter.mpr ⟨mem.mpr ⟨by omega,by omega,by rwa [residue]⟩,by rwa [residue]⟩
  · intro x hx
    obtain ⟨lo,hi,_⟩ := mem.mp (mem_filter.mp hx).1
    change l+(x%100+100-l%100)%100=x
    omega
  · intro a ha
    have small := mem_range.mp (mem_filter.mp ha).1
    change (l+(a+100-l%100)%100)%100=a
    omega

theorem complete_count {r : ℕ} (rlt : r<100) (square : r%5=1 ∨ r%5=4) (l : ℕ) :
    (window r l (l+99)).card=7 := by
  have counts := row_sizes ⟨r,rlt⟩ square
  have split := filter_card_add_filter_neg_card_eq_card (s:=window r l (l+99))
    (fun x => favored r (x%100)=true)
  rw [←split]
  simp only [Bool.not_eq_true,complete_group,counts.1,counts.2]

/-- Counting the members of an arbitrary truncated block by their residues
modulo 100 is injective. The lower endpoint need not be a multiple of 100. -/
private theorem block_bound {r l : ℕ} {S : Finset ℕ} (hi : Bool)
    (inside : ∀ x∈S, l≤x ∧ x<l+100 ∧ passes r (x%100)=true) :
    (S.filter (fun x => favored r (x%100)=hi)).card ≤ (row r hi).card := by
  apply card_le_card_of_injOn (fun x : ℕ => x%100)
  · intro x hx
    obtain ⟨mem,cls⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),(inside x mem).2.2,cls⟩
  · intro x hx y hy eq
    obtain ⟨xl,xh,_⟩ := inside x (mem_filter.mp hx).1
    obtain ⟨yl,yh,_⟩ := inside y (mem_filter.mp hy).1
    exact le_antisymm (Nat.ModEq.le_of_lt_add eq (by omega))
      (Nat.ModEq.le_of_lt_add (Nat.ModEq.symm eq) (by omega))

/-- Position within one block, starting at one, for a true sum s. -/
noncomputable def ascending (S : Finset ℕ) (s : ℕ) := 1+(S.filter (·<s)).card

/-- All favored sums first, and numerical order within each group. -/
noncomputable def priority (S : Finset ℕ) (r s : ℕ) :=
  let prior := S.filter (·<s)
  if favored r (s%100) then
    1+(prior.filter (fun x => favored r (x%100)=true)).card
  else
    1+(S.filter (fun x => favored r (x%100)=true)).card+
      (prior.filter (fun x => favored r (x%100)=false)).card

/-- The target can move earlier by at most five visits, or later by at most
two. The same common count of visits paid for all earlier blocks cancels. -/
theorem rank_window {S : Finset ℕ} {r l : ℕ} (rlt : r<100) (square : r%5=1 ∨ r%5=4)
    (inside : ∀ x∈S, l≤x ∧ x<l+100 ∧ passes r (x%100)=true) (s paid : ℕ) :
    paid+ascending S s ≤ paid+priority S r s+5 ∧
    paid+priority S r s ≤ paid+ascending S s+2 := by
  let prior := S.filter (·<s)
  let flag := fun x => favored r (x%100)
  have parts : (prior.filter (fun x => flag x=true)).card+(prior.filter (fun x => flag x=false)).card=prior.card := by
    simpa only [Bool.not_eq_true] using filter_card_add_filter_neg_card_eq_card (s:=prior) (fun x => flag x=true)
  have counts := row_sizes ⟨r,rlt⟩ square
  have h := (block_bound true inside).trans_eq counts.1
  have lp := (block_bound false (S:=prior) (fun x hx => inside x (mem_filter.mp hx).1)).trans_eq counts.2
  have mono : (prior.filter (fun x => flag x=true)).card≤(S.filter (fun x => flag x=true)).card :=
    card_le_card (filter_subset_filter _ (filter_subset _ _))
  change (S.filter (fun x => flag x=true)).card≤2 at h
  change (prior.filter (fun x => flag x=false)).card≤5 at lp
  unfold ascending priority
  change paid+(1+prior.card)≤paid+(if flag s then _ else _)+5 ∧ _
  cases f : flag s <;> dsimp only [flag,prior] at * <;>
    simp only [f,Bool.false_eq_true,if_false,if_true] <;> omega

/-- Count from the lower end of the interval, including the successful
test. Every complete earlier block contains seven admissible sums. -/
noncomputable def positions (n lo hi s : ℕ) : ℕ×ℕ :=
  let blocks := (s-lo)/100
  let S := window (n%100) (lo+100*blocks) hi
  (7*blocks + ascending S s, 7*blocks + priority S (n%100) s)

theorem both_extremes :
    positions 7253249 5387 5589 5586=(14,9) ∧
    positions 7688801 5546 5802 5790=(17,19) ∧
    positions 6296551 5019 5122 5120=(8,8) := by decide +kernel

/-- When sums from the favored classes are searched first over the entire
interval, a favored target is reached after two checks per complete block
plus its favored position in the target block. -/
noncomputable def firstGroupCost (n lo s : ℕ) :=
  let blocks := (s-lo)/100
  let prior := (window (n%100) (lo+100*blocks) s).filter (fun x => favored (n%100) (x%100)=true)
  2*blocks + prior.card

/-- Across the whole interval, a favored target needs two visits per
complete block and at most two more in the target block. The additive
ten accounts for the phase of the final block. -/
theorem favored_cost {n lo hi s : ℕ} (square : n%5=1 ∨ n%5=4)
    (lower : lo≤s) (upper : s≤hi)
    (hit : passes (n%100) (s%100)=true) (special : favored (n%100) (s%100)=true) :
    0<firstGroupCost n lo s ∧ 7*firstGroupCost n lo s ≤ 2*(positions n lo hi s).1+10 := by
  let k := (s-lo)/100
  let start := lo+100*k
  have val : start≤s ∧ s<start+100 := by dsimp [start,k]; omega
  have mod5 := Nat.mod_mod_of_dvd n (by decide : 5∣100)
  have count := row_sizes ⟨n%100,Nat.mod_lt _ (by decide)⟩ (by simpa only [mod5] using square)
  let W := window (n%100) start s
  let earlier := (window (n%100) start hi).filter (·<s)
  let chosen := W.filter (fun x => favored (n%100) (x%100)=true)
  have inside (x : ℕ) (hx : x∈W) : start≤x ∧ x<start+100 ∧ passes (n%100) (x%100)=true := by
    obtain ⟨h,pass⟩ := mem_filter.mp hx
    obtain ⟨l,u⟩ := mem_Ico.mp h
    exact ⟨l,u.trans_le (min_le_left ..),pass⟩
  have two : chosen.card≤2 := (block_bound true inside).trans_eq count.1
  have target : s∈W := mem_filter.mpr ⟨mem_Ico.mpr ⟨val.1,lt_min val.2 (Nat.lt_succ_self _)⟩,hit⟩
  have nonempty : 0<chosen.card := card_pos.mpr ⟨s,mem_filter.mpr ⟨target,special⟩⟩
  have sub : chosen ⊆ insert s earlier := by
    intro x hx
    obtain ⟨range,pass⟩ := mem_filter.mp (mem_filter.mp hx).1
    obtain ⟨bot,top⟩ := mem_Ico.mp range
    have last := top.trans_le (min_le_right ..)
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ last) with eq|lt
    · exact mem_insert.mpr (Or.inl eq)
    · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ico.mpr
        ⟨bot,lt_min (top.trans_le (min_le_left ..)) (by omega)⟩,pass⟩,lt⟩)
  have shared : chosen.card≤earlier.card+1 := (card_le_card sub).trans (card_insert_le ..)
  change 0<2*k+chosen.card ∧ 7*(2*k+chosen.card) ≤ 2*(7*k+(1+earlier.card))+10
  omega

/-- A first-phase hit costs at most 30% of the ascending checks once the
target follows one hundred complete blocks. -/
theorem long_favored_cost {n lo hi s : ℕ} (square : n%5=1 ∨ n%5=4)
    (far : lo+10000≤s) (upper : s≤hi)
    (hit : passes (n%100) (s%100)=true) (special : favored (n%100) (s%100)=true) :
    10*firstGroupCost n lo s ≤ 3*(positions n lo hi s).1 := by
  have ratio := (favored_cost square (by omega : lo≤s) upper hit special).2
  have size : 700≤(positions n lo hi s).1 := by
    dsimp only [positions]
    omega
  omega

theorem worked_products :
    ExactFactorization 7253249 [2053,3533] ∧ ExactFactorization 7688801 [2063,3727] ∧
    ExactFactorization 6296551 [2053,3067] := by norm_num [ExactFactorization]

end PrimeFactors.PeriodicSumRank
