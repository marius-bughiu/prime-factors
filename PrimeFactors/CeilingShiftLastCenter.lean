import PrimeFactors.CeilingShiftDistances

/-! An existence reading over a suffix of the search is exactly a comparison
with the true midpoint. Individual positions need not give a monotone reading. -/
namespace PrimeFactors.CeilingShiftLastCenter

open Finset CeilingShiftPopulation CeilingShiftDistances
open scoped Classical

/-- The least odd integer above both the start of the search and a
specified lower bound, allowing equality. -/
def firstOdd (n k : ℕ) :=
  let lo := max (ceilSqrt n) k
  lo+(lo+1)%2

private theorem odd_properties (n k : ℕ) :
    ceilSqrt n≤firstOdd n k ∧ k≤firstOdd n k ∧ Odd (firstOdd n k) ∧
    ∀ m, ceilSqrt n≤m → k≤m → Odd m → firstOdd n k≤m := by
  simp only [firstOdd,Nat.odd_iff]
  refine ⟨by omega,by omega,by omega,?_⟩
  intro m start lower odd
  omega

theorem odd_center {p q m a : ℕ} (op : Odd p) (oq : Odd q) (hit : Hit p q m a) : Odd m := by
  have reduced : (((p+a)%2)*((q+a)%2))%2=(((m+a)%2)*((m+a)%2))%2 := calc
    _ = ((p+a)*(q+a))%2 := (Nat.mul_mod ..).symm
    _ = ((m+a)*(m+a))%2 := by rw [hit.2,pow_two]
    _ = _ := Nat.mul_mod ..
  have po := Nat.odd_iff.mp op
  have qo := Nat.odd_iff.mp oq
  rw [Nat.add_mod p a,Nat.add_mod q a,Nat.add_mod m a,po,qo] at reduced
  apply Nat.odd_iff.mpr
  by_contra! ne
  have ev : m%2=0 := by omega
  rcases Nat.mod_two_eq_zero_or_one a with h|h <;> rw [h,ev] at reduced <;> contradiction

/-- There is a successful center at or after k exactly when the first
available odd position at or after k precedes the true prime midpoint. -/
theorem suffix {p q k : ℕ} (op : Odd p) (oq : Odd q) (ns : ∀ j : ℕ, p*q≠j^2) :
    (∃ m∈centers p q, k≤m) ↔ firstOdd (p*q) k < (p+q)/2 := by
  let M := (p+q)/2
  have mid : p+q=2*M := by obtain ⟨a,h⟩ := op; obtain ⟨b,i⟩ := oq; dsimp [M]; omega
  obtain ⟨start,aboveK,⟨u,hu⟩,least⟩ := odd_properties (p*q) k
  constructor
  · rintro ⟨m,hm,km⟩
    obtain ⟨bound,a,ha⟩ := mem_filter.mp hm
    obtain ⟨lo,hi⟩ := mem_Ico.mp bound
    exact (least m lo km (odd_center op oq ha)).trans_lt hi
  · intro inside
    change firstOdd (p*q) k<M at inside
    let m := 2*((M-2)/2)+1
    have lower : firstOdd (p*q) k≤m := by dsimp [m]; omega
    have last : M=m+1 ∨ M=m+2 := by dsimp [m]; omega
    have om : Odd m := ⟨_,rfl⟩
    have lo := start.trans lower
    have gt := (ceilSqrt_le_iff.mp lo).lt_of_ne (ns m)
    exact ⟨m,mem_filter.mpr ⟨mem_Ico.mpr ⟨lo,by change m<M; omega⟩,last_odd op oq om mid last gt⟩,
      aboveK.trans lower⟩

/-- The greatest successful center is either one or two below the true
midpoint. The product modulo four determines which. -/
theorem recover_from_last {p q m : ℕ} (op : Odd p) (oq : Odd q) (ns : ∀ j : ℕ, p*q≠j^2)
    (found : m∈centers p q) (last : ∀ j∈centers p q, j≤m) :
    (p+q)/2=m+(if p*q%4=3 then 1 else 2) := by
  obtain ⟨bounds,a,hit⟩ := mem_filter.mp found
  obtain ⟨lo,hi⟩ := mem_Ico.mp bounds
  have parity := Nat.odd_iff.mp (odd_center op oq hit)
  have stopped : ¬∃ j∈centers p q, m+1≤j := by rintro ⟨j,hj,le⟩; have := last j hj; omega
  have next := (suffix op oq ns (k:=m+1)).not.mp stopped
  simp only [firstOdd] at next
  obtain ⟨x,px⟩ := op
  obtain ⟨y,qy⟩ := oq
  have mul : p*q=4*(x*y)+2*(x+y)+1 := by rw [px,qy]; ring
  split <;> omega

end PrimeFactors.CeilingShiftLastCenter
