import PrimeFactors.FavoredSumWork
import PrimeFactors.GlobalSumOrderCost

/-! Merging two ascending lists of admissible sums using the discriminant
and local multiplicities. This order uses integer keys and ties by smaller
sum. No factor information is used to order candidates. -/

namespace PrimeFactors.ScoreSumOrder

open Finset PeriodicSumRank FactorSumPrefixCost
open private PrimeFactors.ProductDeficitBand.left_cap from PrimeFactors.ProductDeficitBand

/-- The common positive denominator has been cleared from Δ/weight². -/
def key (n s : ℕ) := (if favored (n%100) (s%100) then 4 else 25)*(s^2-4*n)

/-- Inclusive order on candidate keys, with ties settled by integer sum. -/
def before (n t s : ℕ) := key n t<key n s ∨ (key n t=key n s ∧ t≤s)

noncomputable def «prefix» (n lo hi s : ℕ) : Finset ℕ := by
  classical
  exact (Icc lo hi).filter fun t => passes (n%100) (t%100)=true ∧ before n t s

theorem mem_prefix {n lo hi t s : ℕ} : t∈«prefix» n lo hi s ↔
    (lo≤t ∧ t≤hi) ∧ passes (n%100) (t%100)=true ∧ before n t s := by
  classical
  simp only [«prefix»,mem_filter,mem_Icc]

theorem key_le {n t s : ℕ} (h : before n t s) : key n t≤key n s := h.elim Nat.le_of_lt (·.1.le)

private theorem disc_mono (n : ℕ) {x y : ℕ} (h : x≤y) :
    x^2-4*n≤y^2-4*n := Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) _

private theorem disc_strict {n x y : ℕ} (low : ceilSqrt (4*n)≤x) (h : x<y) :
    x^2-4*n<y^2-4*n := by
  have a := ceilSqrt_le_iff.mp low
  have b : x^2<y^2 := Nat.pow_lt_pow_left h (by decide)
  omega

theorem same_group {n t s : ℕ} (phase : favored (n%100) (t%100)=favored (n%100) (s%100)) :
    before n t s ↔ t≤s := by
  unfold before key
  rw [phase]
  constructor
  · rintro (lt|⟨_,h⟩)
    · by_contra! wrong
      exact (not_lt_of_ge (Nat.mul_le_mul_left _ (disc_mono n wrong.le))) lt
    · exact h
  · intro le
    exact (Nat.mul_le_mul_left _ (disc_mono n le)).lt_or_eq.imp_right (fun eq => ⟨eq,le⟩)

theorem favored_not_later {n lo hi s : ℕ} (start : ceilSqrt (4*n)≤lo)
    (target : favored (n%100) (s%100)=true) (ins : lo≤s) :
    «prefix» n lo hi s ⊆ passingPrefix n lo s := by
  intro t member
  obtain ⟨⟨l,_⟩,pass,ord⟩ := mem_prefix.mp member
  have le : t≤s := by
    by_contra! fail
    have small := disc_strict (start.trans ins) fail
    have k := key_le ord
    unfold key at k
    simp only [target,ite_true] at k
    cases branch : favored (n%100) (t%100) <;> simp [branch] at k <;> omega
  exact mem_filter.mpr ⟨mem_Ico.mpr ⟨l,by omega⟩,pass⟩

theorem favored_first_le {n lo hi s : ℕ} (upper : s≤hi)
    (target : favored (n%100) (s%100)=true) :
    favoredPrefix n lo s ⊆ «prefix» n lo hi s := by
  intro t member
  obtain ⟨m,phase⟩ := mem_filter.mp member
  obtain ⟨bounds,pass⟩ := mem_filter.mp m
  obtain ⟨lo,top⟩ := mem_Ico.mp bounds
  have le : t≤s := by omega
  exact mem_prefix.mpr ⟨⟨lo,le.trans upper⟩,pass,(same_group (phase.trans target.symm)).mpr le⟩

/-- Ordinary hits cannot move earlier than in numeric order. -/
theorem ordinary_not_earlier {n lo hi s : ℕ} (upper : s≤hi)
    (target : favored (n%100) (s%100)=false) :
    passingPrefix n lo s ⊆ «prefix» n lo hi s := by
  intro t member
  obtain ⟨bounds,ok⟩ := mem_filter.mp member
  obtain ⟨low,top⟩ := mem_Ico.mp bounds
  have le : t≤s := by omega
  have disc := disc_mono n le
  have k : key n t≤key n s := by
    unfold key
    cases branch : favored (n%100) (t%100) <;> simp [branch,target] <;> omega
  exact mem_prefix.mpr ⟨⟨low,le.trans upper⟩,ok,k.lt_or_eq.imp_right (fun eq => ⟨eq,le⟩)⟩

/-- The score-ordered search stops exactly at the true factor sum, whether
or not its residue belongs to the group with larger local weight. -/
theorem unique_hit {p q A : ℕ} (size : 3≤A) (pl : A≤p) (ord : p<q) (qu : q<2*A)
    (pp : p.Prime) (qp : q.Prime) :
    let n := p*q
    let s := p+q
    («prefix» n (ceilSqrt (4*n)) (ProductDeficitBand.sumCap n A) s).filter
      (fun t => IsSquare (t^2-4*n))={s} := by
  classical
  dsimp only
  have known := (GlobalSumOrderCost.semiprime_unique size pl ord qu pp qp).1
  have member : p+q ∈ passingPrefix (p*q) (ceilSqrt (4*(p*q))) (p+q) ∧
      IsSquare ((p+q)^2-4*(p*q)) :=
    mem_filter.mp (known.symm ▸ mem_singleton_self _)
  have low := (mem_Ico.mp (mem_filter.mp member.1).1).1
  have pass := (mem_filter.mp member.1).2
  have upper : p+q≤ProductDeficitBand.sumCap (p*q) A :=
    le_min (PrimeFactors.ProductDeficitBand.left_cap (by omega) pl (pl.trans ord.le))
      (CenteredSumQuartic.sum_upper rfl (by omega) (by omega) (by omega))
  ext t
  simp only [mem_filter,mem_prefix,mem_singleton]
  constructor
  · rintro ⟨⟨⟨lt,ut⟩,pt,_⟩,square⟩
    exact (pass_square_iff (by omega : 2≤A) pl ord.le pp qp lt ut pt).mp square
  · rintro rfl
    exact ⟨⟨⟨low,upper⟩,pass,Or.inr ⟨rfl,le_rfl⟩⟩,member.2⟩

end PrimeFactors.ScoreSumOrder
