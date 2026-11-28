import PrimeFactors.CircleCoordinateFibers
import PrimeFactors.QuarticLocalSquareCriterion

/-! Information in the exact number of ordered pairs of points on the norm-one
circle with the same first coordinate. The count includes pairs of identical
points. The arithmetic readouts below assume the count is supplied. -/
namespace PrimeFactors.CircleCollisionReadout

open CircleCoordinateFibers SphereCircleIdentity ThreeSquareRadiusCounts

noncomputable def count (n : ℕ) [NeZero n] : ℕ := collisions (ZMod n) 1

private theorem count_congr {m n : ℕ} [NeZero m] [NeZero n] (eqn : m=n) :
    count m=count n := by subst n; rfl

private theorem factor_count {p : ℕ} [hp : Fact p.Prime] (odd : p≠2) :
    2*(circle (ZMod p) 1).card-2=2*(if p%4=1 then p-2 else p) := by
  have eqn := prime_unit odd (1:ZMod p) one_ne_zero
  have low := hp.out.two_le
  by_cases h : p%4=1 <;> simp [sign,h] at eqn ⊢ <;> omega

/-- The quarter-count is a product of ordinary integers. A prime congruent
to one modulo four contributes that prime minus two. -/
theorem formula {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) :
    count (p*q)=4*((if p%4=1 then p-2 else p)*(if q%4=1 then q-2 else q)) := by
  rw [count,norm_one_collisions ((Nat.coprime_primes hp.out hq.out).mpr diff) op oq,
    factor_count op,factor_count oq]
  ring

private theorem classes {p : ℕ} [hp : Fact p.Prime] (op : p≠2) : p%4=1 ∨ p%4=3 := by
  obtain ⟨k,h⟩ := hp.out.odd_of_ne_two op
  omega

/-- The product remainder detects precisely the mixed case. -/
theorem mixed_iff {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (op : p≠2) (oq : q≠2) :
    (p*q)%4=3 ↔ (p%4=1 ∧ q%4=3) ∨ (p%4=3 ∧ q%4=1) := by
  rw [Nat.mul_mod]
  rcases classes op with a|a <;> rcases classes oq with b|b <;> norm_num [a,b]

private theorem mixed_identity {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (a : p%4=1) (b : q%4=3) :
    count (p*q)/4+2*q=p*q := by
  have hc := formula diff op oq
  simp only [a,b,if_true,if_false,show ¬(3:ℕ)=1 by decide] at hc
  rw [hc,Nat.mul_div_cancel_left _ (by decide)]
  have shift : p-2+2=p := Nat.sub_add_cancel hp.out.two_le
  rw [←Nat.add_mul,shift]

/-- At a mixed product the supplied count identifies the unique prime
congruent to three modulo four. -/
theorem mixed {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (h : (p*q)%4=3) :
    let r := (p*q-count (p*q)/4)/2
    (r=p ∨ r=q) ∧ r%4=3 := by
  dsimp only
  rcases (mixed_iff op oq).mp h with ⟨a,b⟩|⟨a,b⟩
  · have eqn := mixed_identity diff op oq a b
    have r : (p*q-count (p*q)/4)/2=q := by omega
    exact ⟨Or.inr r,(congrArg (·%4) r).trans b⟩
  · have eqn := mixed_identity diff.symm oq op b a
    rw [count_congr (Nat.mul_comm q p),Nat.mul_comm q p] at eqn
    have r : (p*q-count (p*q)/4)/2=p := by omega
    exact ⟨Or.inl r,(congrArg (·%4) r).trans a⟩

private theorem one_identity {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (a : p%4=1) (b : q%4=1) :
    count (p*q)/4+2*(p+q)=p*q+4 := by
  have hc := formula diff op oq
  simp only [a,b,if_true] at hc
  rw [hc,Nat.mul_div_cancel_left _ (by decide)]
  have h := congrArg₂ Nat.mul (Nat.sub_add_cancel hp.out.two_le) (Nat.sub_add_cancel hq.out.two_le)
  have P := Nat.sub_add_cancel hp.out.two_le
  have Q := Nat.sub_add_cancel hq.out.two_le
  nlinarith only [h,P,Q]

theorem both_one {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (a : p%4=1) (b : q%4=1) :
    (p*q+4-count (p*q)/4)/2=p+q := by
  have eqn := one_identity diff op oq a b
  omega

theorem both_three {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (a : p%4=3) (b : q%4=3) :
    count (p*q)=4*(p*q) := by
  simpa [a,b] using formula diff op oq

/-- Among all the branches only the two primes congruent to three give the
baseline four times the product. -/
theorem baseline_iff {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) :
    count (p*q)=4*(p*q) ↔ p%4=3 ∧ q%4=3 := by
  refine ⟨fun base => ?_,fun h => both_three diff op oq h.1 h.2⟩
  have half : count (p*q)/4=p*q := by rw [base,Nat.mul_div_cancel_left _ (by decide)]
  have P := hp.out.two_le
  have Q := hq.out.two_le
  rcases classes op with a|a <;> rcases classes oq with b|b
  · have h := one_identity diff op oq a b
    omega
  · have h := mixed_identity diff op oq a b
    omega
  · have h := mixed_identity diff.symm oq op b a
    rw [count_congr (Nat.mul_comm q p),Nat.mul_comm q p] at h
    omega
  · exact ⟨a,b⟩

theorem nonbaseline_iff {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) :
    count (p*q)≠4*(p*q) ↔ p%4=1 ∨ q%4=1 := by
  rw [ne_eq,baseline_iff diff op oq]
  have P := classes op
  have Q := classes oq
  omega

/-- The remaining two cases can also be distinguished by a predicate on the
product. Determining whether a square root exists is a separate computation. -/
theorem square_iff {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (op : p≠2) (oq : q≠2) :
    IsSquare (-1 : ZMod (p*q)) ↔ p%4=1 ∧ q%4=1 := by
  rw [QuarticLocalSquareCriterion.square_iff ((hp.out.odd_of_ne_two op).mul (hq.out.odd_of_ne_two oq))]
  refine ⟨fun h => ⟨h p hp.out (dvd_mul_right p q),h q hq.out (dvd_mul_left q p)⟩,?_⟩
  rintro ⟨a,b⟩ r prime divides
  rcases prime.dvd_mul.mp divides with div|div
  · exact ((Nat.prime_dvd_prime_iff_eq prime hp.out).mp div) ▸ a
  · exact ((Nat.prime_dvd_prime_iff_eq prime hq.out).mp div) ▸ b

/-- The last two examples have identical products modulo 32, with different
collision behavior. -/
theorem controls : count 15=36 ∧ count 65=132 ∧ count 161=644 ∧ 65%32=161%32 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  letI : Fact (Nat.Prime 23) := ⟨by decide⟩
  exact ⟨formula (p:=3) (q:=5) (by decide) (by decide) (by decide),
    formula (p:=5) (q:=13) (by decide) (by decide) (by decide),
    formula (p:=7) (q:=23) (by decide) (by decide) (by decide),by decide⟩

end PrimeFactors.CircleCollisionReadout
