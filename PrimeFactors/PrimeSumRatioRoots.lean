import PrimeFactors.FactorSum
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! Reduced denominators and integer polynomial roots of the squared prime
sum divided by the product. The ratio uses the true sum. -/

namespace PrimeFactors.PrimeSumRatioRoots

open Polynomial

/-- The square makes this ratio invariant under common scaling of both factors. -/
noncomputable def ratio (p q : ℕ) : ℚ := ((p+q)^2 : ℕ) / (p*q : ℕ)

theorem den_of_coprime {p q : ℕ} (pos : 0<p*q) (cop : p.Coprime q) :
    (ratio p q).den=p*q := by
  have reduced : ((p+q)^2).Coprime (p*q) :=
    (Nat.coprime_mul_iff_right.mpr
      ⟨Nat.coprime_self_add_left.mpr cop.symm,Nat.coprime_add_self_left.mpr cop⟩).pow_left 2
  have zpos : 0<((p*q : ℕ) : ℤ) := by exact_mod_cast pos
  apply Int.ofNat_inj.mp
  simpa only [ratio,Int.cast_natCast] using
    Rat.den_div_eq_of_coprime zpos (by simpa only [Int.natAbs_natCast] using reduced :
      (((p+q)^2 : ℕ) : ℤ).natAbs.Coprime ((p*q : ℕ) : ℤ).natAbs)

theorem den {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q) :
    (ratio p q).den=p*q :=
  den_of_coprime (Nat.mul_pos pp.pos qp.pos) ((Nat.coprime_primes pp qp).mpr ne)

private theorem rat_den_dvd_leadingCoeff {r : ℚ} {H : ℤ[X]} (root : aeval r H=0) :
    (r.den : ℤ) ∣ H.leadingCoeff := by
  let a := IsFractionRing.num ℤ r
  let b : ℤ := IsFractionRing.den ℤ r
  have frac : Rat.divInt a b=r := by
    rw [Rat.divInt_eq_div]
    exact IsFractionRing.mk'_num_den' ℤ r
  exact (frac ▸ Rat.den_dvd a b).trans (den_dvd_of_is_root root)

/-- The rational root theorem forces the entire semiprime into the
leading coefficient of any integer polynomial vanishing at its ratio. -/
theorem product_dvd_leadingCoeff {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) {H : ℤ[X]} (root : aeval (ratio p q) H=0) :
    ((p*q : ℕ) : ℤ) ∣ H.leadingCoeff := by
  simpa only [den pp qp ne] using rat_den_dvd_leadingCoeff root

theorem monic_ne_zero {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    {H : ℤ[X]} (monic : H.Monic) : aeval (ratio p q) H≠0 := by
  intro root
  have div := product_dvd_leadingCoeff pp qp ne root
  rw [monic.leadingCoeff] at div
  have eq : p*q=1 := Nat.dvd_one.mp (by exact_mod_cast div)
  exact pp.ne_one (Nat.dvd_one.mp (eq ▸ dvd_mul_right p q))

/-- Equality of reduced denominators determines the sorted prime pair. -/
theorem eq_iff {p q r s : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime) (sp : s.Prime)
    (pq : p<q) (rs : r<s) : ratio p q=ratio r s ↔ p=r ∧ q=s := by
  constructor
  · intro same
    have prod := congrArg Rat.den same
    rw [den pp qp pq.ne,den rp sp rs.ne] at prod
    exact ordered_semiprime_pair_unique rp sp rs.le pq.le pp.one_lt prod
  · rintro ⟨rfl,rfl⟩
    rfl

end PrimeFactors.PrimeSumRatioRoots
