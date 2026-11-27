import PrimeFactors.JacobiPeriodSquareClass

/-!
# Lower bounds on successful predecessor-square scales from partial valuations

A prime occurring to odd order in the product of the two predecessors must
divide every positive scale that returns the factor sum. The two divisibility
checks below certify the valuation without factoring the rest of that product.
-/

namespace PrimeFactors.JacobiScaleValuations

/-- A correct sum gives a square quotient for the product of the predecessors. -/
theorem scale_square {p q t : ℕ} (hp : 1 < p) (le : p ≤ q) (balanced : q ≤ 2*p)
    (tp : 0<t) (hit : predecessorSquareSum (p*q) t = p+q) :
    ∃ y : ℕ, t*y^2=(p-1)*(q-1) := by
  have p1 := hp.le
  have q1 := p1.trans le
  have iff := JacobiPeriodScales.sum_iff_square (P:=p-1) (Q:=q-1)
    (Nat.sub_pos_of_lt hp) (Nat.sub_le_sub_right le 1)
    (by simpa only [Nat.sub_add_cancel p1,Nat.sub_add_cancel q1] using balanced) tp
  simp only [Nat.sub_add_cancel p1,Nat.sub_add_cancel q1] at iff
  exact iff.mp hit

/-- Exact odd valuation 2k+1 forces its prime into any multiplicative square coefficient. -/
theorem odd_valuation_forces {r k F t y : ℕ} (prime : r.Prime) (rep : t*y^2=F)
    (yes : r^(2*k+1) ∣ F) (no : ¬ r^(2*k+2) ∣ F) : r ∣ t := by
  have nz : F≠0 := fun z => no (z ▸ dvd_zero _)
  have both := mul_ne_zero_iff.mp (rep.trans_ne nz)
  have value := (prime.pow_dvd_iff_le_factorization nz).mp yes
  have upper := mt (prime.pow_dvd_iff_le_factorization nz).mpr no
  by_contra miss
  have zero := Nat.factorization_eq_zero_of_not_dvd miss
  rw [←rep, Nat.factorization_mul both.1 both.2, Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.smul_apply, zero, zero_add, smul_eq_mul] at value upper
  omega

/-- The same certificate applies to the squarefree part c of the least period,
or to the first successful scale through its verified square representation. -/
theorem divides_first {p q c z r k : ℕ} (prime : r.Prime)
    (eqn : JacobiPeriodCount.residualProduct p q = c*z^2)
    (yes : r^(2*k+1) ∣ (p-1)*(q-1)) (no : ¬ r^(2*k+2) ∣ (p-1)*(q-1)) : r ∣ c := by
  let g := (p-1).gcd (q-1)
  have left : g*((p-1)/g)=p-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have right : g*((q-1)/g)=q-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have rep : c*(g*z)^2=(p-1)*(q-1) := calc
    c*(g*z)^2 = g^2*(c*z^2) := by ring
    _ = (g*((p-1)/g))*(g*((q-1)/g)) := by rw [←eqn]; unfold JacobiPeriodCount.residualProduct; dsimp [g]; ring
    _ = _ := by rw [left,right]
  exact odd_valuation_forces prime rep yes no

end PrimeFactors.JacobiScaleValuations
