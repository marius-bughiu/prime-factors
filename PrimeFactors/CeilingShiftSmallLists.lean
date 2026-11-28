import PrimeFactors.CeilingShiftDistances

/-! Exact small lists, computed from the proved divisor criterion. -/
namespace PrimeFactors.CeilingShiftSmallLists
open Finset CeilingShiftDistances CeilingShiftPopulation
open scoped Classical

/-- With the half-gap supplied, successful centers can be enumerated with
finite integer divisions. This form is used to check the small controls. -/
theorem divisor_test {p d m b : ℕ} (bp : 0<b) (center : m+b=p+d)
    (above : p*(p+2*d)<m^2) :
    (∃ a, Hit p (p+2*d) m a) ↔ b∣d^2 ∧ Even (b+d^2/b) := by
  rw [at_distance center above]
  constructor
  · rintro ⟨c,eqn,parity⟩
    exact ⟨⟨c,eqn.symm⟩,by rwa [←eqn,Nat.mul_div_cancel_left _ bp]⟩
  · rintro ⟨dvd,parity⟩
    exact ⟨_,Nat.mul_div_cancel' dvd,parity⟩

private theorem mem_at {p q d n r m : ℕ} (pair : p+2*d=q) (product : p*q=n)
    (lower : r^2<n) (upper : n<(r+1)^2) :
    m∈centers p q ↔ (r+1≤m ∧ m<p+d) ∧
      (p+d-m)∣d^2 ∧ Even (p+d-m+d^2/(p+d-m)) := by
  have cap := ceilSqrt_le_iff.mpr upper.le
  have base := (ceilSqrt_le_iff.not).mpr (not_le_of_gt lower)
  have root : ceilSqrt n=r+1 := by omega
  have mid : (p+q)/2=p+d := by omega
  simp only [centers,interval,mem_filter,mem_Ico,product,root,mid]
  apply and_congr_right
  rintro ⟨lo,hi⟩
  have above : p*q<m^2 := product ▸ upper.trans_le (Nat.pow_le_pow_left lo 2)
  rw [←pair] at above ⊢
  exact divisor_test (p:=p) (d:=d) (m:=m) (b:=p+d-m) (by omega) (by omega) above

theorem small_sets : centers 67 127={95} ∧ centers 73 127={97,99} := by
  constructor
  · ext m
    rw [mem_at (p:=67) (q:=127) (m:=m) (d:=30) (n:=8509) (r:=92) (by decide) (by decide) (by decide) (by decide),
      mem_singleton]
    by_cases inside : 93≤m ∧ m<97
    · obtain rfl|rfl|rfl|rfl : m=93 ∨ m=94 ∨ m=95 ∨ m=96 := by omega
      all_goals decide +kernel
    · change ((93≤m ∧ m<97) ∧ _) ↔ m=95
      simp only [inside,false_and,false_iff]
      omega
  · ext m
    rw [mem_at (p:=73) (q:=127) (m:=m) (d:=27) (n:=9271) (r:=96) (by decide) (by decide) (by decide) (by decide),
      mem_insert,mem_singleton]
    by_cases inside : 97≤m ∧ m<100
    · obtain rfl|rfl|rfl : m=97 ∨ m=98 ∨ m=99 := by omega
      all_goals decide +kernel
    · change ((97≤m ∧ m<100) ∧ _) ↔ m=97 ∨ m=99
      simp only [inside,false_and,false_iff]
      omega

end PrimeFactors.CeilingShiftSmallLists
