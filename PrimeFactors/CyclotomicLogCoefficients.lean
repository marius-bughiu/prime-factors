import PrimeFactors.InverseCyclotomicMeasurements
import PrimeFactors.PartitionRecurrence
import Mathlib.RingTheory.PowerSeries.Inverse

/-! The formal series −X T′/T for the scaled inverse cyclotomic polynomial.
Positive indices below the semiprime contribute only when their gcd with
the product already supplies a prime. At a positive multiple of the whole
product, the coefficient is instead the unknown prime sum. -/
namespace PrimeFactors.CyclotomicLogCoefficients

open PowerSeries Finset
open scoped PowerSeries

noncomputable def polySeries (n : ℕ) : PowerSeries ℤ :=
  (InverseCyclotomicMeasurements.polynomial n : PowerSeries ℤ)

noncomputable def logSeries (n : ℕ) : PowerSeries ℤ :=
  -(derivative ℤ (polySeries n)*X) * invOfUnit (polySeries n) 1

theorem binary_series {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q) :
    logSeries (p*q)=partitionMultiples ℤ p+partitionMultiples ℤ q := by
  have eq : polySeries (p*q)=(1-X^p)*(1-X^q) := by
    simp only [polySeries,InverseCyclotomicMeasurements.sparse hp hq order,
      Polynomial.coe_mul,Polynomial.coe_sub,Polynomial.coe_one,Polynomial.coe_pow,Polynomial.coe_X]
  have constant : constantCoeff ℤ (polySeries (p*q))=(1 : ℤˣ) := by
    simp [eq,hp.ne_zero,hq.ne_zero]
  have law := finitePartition_log_equation (R:=ℤ) {p,q} (by
    intro d hd
    rcases (show d=p ∨ d=q by simpa using hd) with rfl|rfl
    · exact hp.pos
    · exact hq.pos)
  simp only [prod_insert (by simpa using order.ne : p∉({q}:Finset ℕ)),
    sum_insert (by simpa using order.ne : p∉({q}:Finset ℕ)),prod_singleton,sum_singleton] at law
  rw [←eq] at law
  rw [logSeries,←law,mul_right_comm,mul_invOfUnit _ _ constant,one_mul]

theorem coefficient {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q) (pos : 0<m) :
    coeff ℤ m (logSeries (p*q))=
      (if p∣m then (p:ℤ) else 0)+(if q∣m then (q:ℤ) else 0) := by
  simp only [binary_series hp hq order,map_add,partitionMultiples,coeff_mk,pos,true_and]

/-- A lookup at the public index N gives the sum if we have a coefficient
oracle. The same holds at every positive multiple of N. -/
theorem at_multiple {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q) (pos : 0<m)
    (multiple : p*q∣m) : coeff ℤ m (logSeries (p*q))=(p:ℤ)+q := by
  rw [coefficient hp hq order pos,if_pos ((dvd_mul_right p q).trans multiple),
    if_pos ((dvd_mul_left q p).trans multiple)]

/-- A positive index not divisible by N has exactly three possible
coefficient/gcd pairs. Coprime indices contribute zero. -/
theorem classes {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q) (pos : 0<m)
    (proper : ¬p*q∣m) :
    ((p*q).gcd m=1 ∧ coeff ℤ m (logSeries (p*q))=0) ∨
    ((p*q).gcd m=p ∧ coeff ℤ m (logSeries (p*q))=p) ∨
    ((p*q).gcd m=q ∧ coeff ℤ m (logSeries (p*q))=q) := by
  rw [coefficient hp hq order pos]
  by_cases pm : p∣m <;> by_cases qm : q∣m
  · exact False.elim (proper ((hp.coprime_iff_not_dvd.mpr
      (fun d => order.ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp d))).mul_dvd_of_dvd_of_dvd pm qm))
  · refine Or.inr (Or.inl ⟨?_,by simp [pm,qm]⟩)
    rw [Nat.mul_comm p q]
    exact Nat.gcd_mul_of_coprime_of_dvd (hq.coprime_iff_not_dvd.mpr qm) pm
  · exact Or.inr (Or.inr ⟨Nat.gcd_mul_of_coprime_of_dvd (hp.coprime_iff_not_dvd.mpr pm) qm,
      by simp [pm,qm]⟩)
  · exact Or.inl ⟨(Nat.coprime_mul_iff_left.mpr
      ⟨hp.coprime_iff_not_dvd.mpr pm,hq.coprime_iff_not_dvd.mpr qm⟩).gcd_eq_one,by simp [pm,qm]⟩

theorem at_proper {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q) (pos : 0<m)
    (proper : ¬p*q∣m) :
    coeff ℤ m (logSeries (p*q))=if (p*q).gcd m=1 then 0 else ((p*q).gcd m : ℤ) := by
  rcases classes hp hq order pos proper with h|h|h
  · simp [h.1,h.2]
  · simp [h.1,h.2,hp.ne_one]
  · simp [h.1,h.2,hq.ne_one]

theorem sampled_hit {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q)
    (indices : Finset ℕ) (weight : ℕ→ℤ)
    (below : ∀ m∈indices, 0<m ∧ m<p*q)
    (nonzero : (∑ m∈indices, weight m * coeff ℤ m (logSeries (p*q)))≠0) :
    ∃ m∈indices, (p*q).gcd m=p ∨ (p*q).gcd m=q := by
  by_contra! miss
  apply nonzero
  apply sum_eq_zero
  intro m hm
  obtain ⟨pos,lt⟩ := below m hm
  have proper : ¬p*q∣m := fun hd => (Nat.not_le_of_gt lt) (Nat.le_of_dvd pos hd)
  rcases classes hp hq order pos proper with h|h|h
  · rw [h.2,mul_zero]
  · exact False.elim ((miss m hm).1 h.1)
  · exact False.elim ((miss m hm).2 h.1)

/-- At the proper indices, the value gives a gcd or zero. At 551 both
prime contributions coincide in one coefficient. -/
theorem control_551 :
    coeff ℤ 18 (logSeries 551)=0 ∧ coeff ℤ 38 (logSeries 551)=19 ∧
    coeff ℤ 58 (logSeries 551)=29 ∧ coeff ℤ 551 (logSeries 551)=48 := by
  have at_index {m : ℕ} (hm : 0<m) : coeff ℤ m (logSeries 551)=
      (if 19∣m then (19:ℤ) else 0)+(if 29∣m then (29:ℤ) else 0) := by
    rw [←show 19*29=551 by decide]
    exact coefficient (by decide : Nat.Prime 19) (by decide : Nat.Prime 29) (by decide) hm
  simp only [at_index (by decide : 0<18),at_index (by decide : 0<38),
    at_index (by decide : 0<58),at_index (by decide : 0<551)]
  decide

/-- The first 128 gcd probes on the second control see no nonunit.
Both primes have appeared by index 251. -/
theorem control_32881 :
    ((Icc 1 128).filter fun m => Nat.gcd 32881 m≠1)=∅ ∧
    ((Icc 1 251).filter fun m => Nat.gcd 32881 m≠1)={131,251} :=
  by decide +kernel

end PrimeFactors.CyclotomicLogCoefficients
