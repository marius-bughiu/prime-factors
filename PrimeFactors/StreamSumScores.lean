import PrimeFactors.ScoreSumOrder
import PrimeFactors.AllResidueSumCost

/-! Congruence classes and finite differences used by the bounded score-stream
experiment. The ordering and coverage theorems apply to any position of each
progression inside the stated window. -/

namespace PrimeFactors.StreamSumScores

open Finset PeriodicSumRank ScoreSumOrder

/-- First sum at or above the lower endpoint in a prescribed residue class. -/
def seed (lo : ℕ) (r : Fin 100) : ℕ := lo+(r.val+100-lo%100)%100

def term (lo : ℕ) (r : Fin 100) (j : ℕ) : ℕ := seed lo r+100*j

theorem seed_spec (lo : ℕ) (r : Fin 100) :
    lo≤seed lo r ∧ seed lo r<lo+100 ∧ (seed lo r)%100=r.val := by
  have := r.isLt
  unfold seed
  omega

theorem term_spec (lo : ℕ) (r : Fin 100) (j : ℕ) :
    lo≤term lo r j ∧ (term lo r j)%100=r.val ∧ (term lo r j-lo)/100=j := by
  obtain ⟨a,b,c⟩ := seed_spec lo r
  unfold term
  omega

/-- A residue and a nonnegative progression index identify each passing sum
exactly once. Clipping the upper endpoint also covers an empty interval. -/
theorem partition (n lo hi s : ℕ) :
    (lo≤s ∧ s≤hi ∧ passes (n%100) (s%100)=true) ↔
    s≤hi ∧ ∃! e : Fin 100 × ℕ, passes (n%100) e.1.val=true ∧ term lo e.1 e.2=s := by
  constructor
  · rintro ⟨l,u,pass⟩
    let r : Fin 100 := ⟨s%100,Nat.mod_lt _ (by decide)⟩
    let j := (s-lo)/100
    have step := term_spec lo r j
    have reach : term lo r j=s := by
      change lo≤_ ∧ _%100=s%100 ∧ (_-lo)/100=(s-lo)/100 at step
      omega
    refine ⟨u,⟨r,j⟩,⟨pass,reach⟩,?_⟩
    rintro ⟨r',j'⟩ ⟨_,ok⟩
    have id := term_spec lo r' j'
    change term lo r' j'=s at ok
    rw [ok] at id
    exact Prod.ext (Fin.ext id.2.1.symm) id.2.2.symm
  · rintro ⟨u,⟨⟨r,j⟩,⟨pass,eq⟩,_⟩⟩
    change term lo r j=s at eq
    have step := term_spec lo r j
    rw [eq] at step
    exact ⟨step.1,u,step.2.1 ▸ pass⟩

/-- The initial heap contains exactly the nonempty progressions' first sums. -/
theorem initial_heads (n lo hi s : ℕ) :
    s∈window (n%100) lo hi ↔
      ∃ r : Fin 100, passes (n%100) r.val=true ∧ seed lo r=s ∧ s≤hi := by
  constructor
  · intro ok
    obtain ⟨range,pass⟩ := mem_filter.mp ok
    obtain ⟨l,u⟩ := mem_Ico.mp range
    have b := lt_min_iff.mp u
    let r : Fin 100 := ⟨s%100,Nat.mod_lt _ (by decide)⟩
    have ⟨a,c,d⟩ := seed_spec lo r
    change (seed lo r)%100=s%100 at d
    exact ⟨r,pass,by omega,by omega⟩
  · rintro ⟨r,pass,rfl,upper⟩
    have ⟨l,u,m⟩ := seed_spec lo r
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨l,lt_min u (by omega)⟩,m ▸ pass⟩

private theorem initial_subset (n lo hi : ℕ) :
    window (n%100) lo hi⊆(Ico lo (lo+100)).filter (fun t => passes (n%100) (t%100)=true) := by
  unfold window
  exact filter_subset_filter _ (Ico_subset_Ico_right (min_le_left ..))

theorem seven_heads {n : ℕ} (square : n%5=1 ∨ n%5=4) (lo hi : ℕ) :
    (window (n%100) lo hi).card ≤ 7 := by
  have mod5 := Nat.mod_mod_of_dvd n (by decide : 5∣100)
  have size := complete_count (Nat.mod_lt n (by decide : 0<100)) (by simpa only [mod5] using square) lo
  simp only [window,show lo+99+1=lo+100 by omega,min_self] at size
  exact (card_le_card (initial_subset n lo hi)).trans_eq size

theorem ten_heads {n : ℕ} (squareless : n%5=2 ∨ n%5=3) (lo hi : ℕ) :
    (window (n%100) lo hi).card ≤ 10 :=
  (card_le_card (initial_subset n lo hi)).trans_eq (AllResidueSumCost.complete_count squareless lo)

def disc (n s : ℕ) : ℕ := s^2-4*n
def difference (s : ℕ) : ℕ := 200*s+10000

/-- One advance needs additions to the sum, its discriminant and its next
difference. The lower bound ensures natural subtraction is exact. -/
theorem advance {n s : ℕ} (low : ceilSqrt (4*n)≤s) :
    disc n (s+100)=disc n s+difference s ∧ difference (s+100)=difference s+20000 ∧
    (s+100)%100=s%100 := by
  have base := ceilSqrt_le_iff.mp low
  have step : (s+100)^2=s^2+(200*s+10000) := by ring
  unfold disc difference
  constructor
  · rw [step]
    omega
  · constructor <;> omega

/-- Numeric order on every progression is exactly inclusive score order,
including its tie rule. -/
theorem ordered (n lo : ℕ) (r : Fin 100) (i j : ℕ) :
    before n (term lo r i) (term lo r j) ↔ i≤j := by
  have same : (term lo r i)%100=(term lo r j)%100 :=
    (term_spec lo r i).2.1.trans (term_spec lo r j).2.1.symm
  rw [same_group (congrArg (favored (n%100)) same)]
  unfold term
  omega

private theorem before_trans {n a b c : ℕ} (ab : before n a b) (bc : before n b c) :
    before n a c := by
  unfold before at *
  omega

/-- If each progression has already consumed its first `next r` terms, a
minimum among its remaining heads precedes every remaining passing sum. -/
theorem minimum_of_heads {n lo hi winner : ℕ} (next : Fin 100 → ℕ)
    (least : ∀ r : Fin 100, passes (n%100) r.val=true → term lo r (next r)≤hi →
      before n winner (term lo r (next r))) {r : Fin 100} {j : ℕ}
    (pass : passes (n%100) r.val=true) (unseen : next r≤j) (inside : term lo r j≤hi) :
    before n winner (term lo r j) := by
  have avail : term lo r (next r)≤hi := by unfold term at *; omega
  exact before_trans (least r pass avail) ((ordered ..).mpr unseen)

private theorem prefix_direct (n lo hi s : ℕ) :
    ScoreSumOrder.«prefix» n lo hi s =
      (Icc lo hi).filter fun t => passes (n%100) (t%100)=true ∧
        (key n t<key n s ∨ (key n t=key n s ∧ t≤s)) := by
  ext t
  simp only [mem_prefix,mem_filter,mem_Icc,before]

/-- In the complete 9-bit census this product takes three scored square
tests and four ascending ones. The exact factors certify the hit. -/
theorem control :
    (ScoreSumOrder.«prefix» 132289 728 769 766).card=3 ∧
    (FactorSumPrefixCost.passingPrefix 132289 728 766).card=4 ∧
    ExactFactorization 132289 [263,503] := by
  rw [prefix_direct]
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  norm_num [ExactFactorization]

end PrimeFactors.StreamSumScores
