import Mathlib.Data.Nat.Factorization.Basic

/-! Below the public cutoff N/m, nonunits are disjoint positive multiples
of either prime. Counting them records the two integer quotients on dividing
the primes by m. The correction uses their ordinary residue representatives. -/
namespace PrimeFactors.FractionalNonunitPrefix

open Finset
open scoped Classical

noncomputable def nonunits (n L : ℕ) : Finset ℕ :=
  (Ioc 0 L).filter fun z => ¬z.Coprime n

noncomputable abbrev prefixCount (n m : ℕ) := (nonunits n (n/m)).card

private theorem times (p r : ℕ) (h : p.Prime) : ¬r.Coprime p ↔ p∣r := by
  rw [Nat.coprime_comm,h.coprime_iff_not_dvd,not_not]

theorem count_to {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q)
    (L : ℕ) (short : L<p*q) : (nonunits (p*q) L).card=L/p+L/q := by
  let P := (Ioc 0 L).filter fun z => p∣z
  let Q := (Ioc 0 L).filter fun z => q∣z
  have sets : nonunits (p*q) L=P∪Q := by
    ext z
    simp only [nonunits,P,Q,mem_filter,mem_union,Nat.coprime_mul_iff_right,not_and_or,times _ _ hp,times _ _ hq]
    tauto
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro z hzP hzQ
    obtain ⟨lim,a⟩ := mem_filter.mp hzP
    have b := (mem_filter.mp hzQ).2
    have dv := ((Nat.coprime_primes hp hq).mpr diff).mul_dvd_of_dvd_of_dvd a b
    exact (not_le.mpr short) ((Nat.le_of_dvd (mem_Ioc.mp lim).1 dv).trans (mem_Ioc.mp lim).2)
  rw [sets,card_union_of_disjoint dis]
  exact congrArg₂ Nat.add (Nat.Ioc_filter_dvd_card_eq_div L p) (Nat.Ioc_filter_dvd_card_eq_div L q)

theorem quotient_sum {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q) (proper : 1<m) :
    prefixCount (p*q) m=p/m+q/m := by
  rw [prefixCount,count_to hp hq diff _ (Nat.div_lt_self (Nat.mul_pos hp.pos hq.pos) proper)]
  have swap (n a b : ℕ) : n/a/b=n/b/a := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm a b,←Nat.div_div_eq_div_mul]
  rw [swap _ m p,swap _ m q,Nat.mul_div_cancel_left _ hp.pos,Nat.mul_div_cancel _ hq.pos,Nat.add_comm]

/-- The two ordinary remainders are precisely the missing correction. -/
theorem scaled {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q) (proper : 1<m) :
    m*prefixCount (p*q) m+(p%m+q%m)=p+q := by
  rw [quotient_sum hp hq diff proper,Nat.mul_add]
  have P := Nat.mod_add_div p m
  have Q := Nat.mod_add_div q m
  omega

/-- In particular the correction is strictly less than 2m. -/
theorem window {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q) (proper : 1<m) :
    m*prefixCount (p*q) m ≤ p+q ∧ p+q < m*prefixCount (p*q) m+2*m := by
  have e := scaled hp hq diff proper
  have P := Nat.mod_lt p (by omega : 0<m)
  have Q := Nat.mod_lt q (by omega : 0<m)
  omega

/-- Every nonunit encountered before the end of the period gives a proper divisor. -/
theorem witness {n L z : ℕ} (short : L < n) (hz : z ∈ nonunits n L) :
    1 < z.gcd n ∧ z.gcd n < n := by
  obtain ⟨lim,bad⟩ := mem_filter.mp hz
  obtain ⟨pos,le⟩ := mem_Ioc.mp lim
  have g := Nat.gcd_pos_of_pos_left n pos
  have cap := Nat.le_of_dvd pos (Nat.gcd_dvd_left z n)
  change ¬z.gcd n = 1 at bad
  omega

theorem first {p q L : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q) :
    (nonunits (p*q) L).Nonempty ↔ p≤L := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨lim,bad⟩ := mem_filter.mp hz
    obtain ⟨pos,le⟩ := mem_Ioc.mp lim
    rw [Nat.coprime_mul_iff_right,not_and_or,times _ _ hp,times _ _ hq] at bad
    rcases bad with a|b
    · exact (Nat.le_of_dvd pos a).trans le
    · exact order.le.trans ((Nat.le_of_dvd pos b).trans le)
  · intro h
    refine ⟨p,mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp.pos,h⟩,?_⟩⟩
    rw [Nat.coprime_mul_iff_right,not_and_or,times _ _ hp]
    exact Or.inl (dvd_refl p)

/-- Directly check the three positions in the shortened period for 2183. -/
theorem example_positions : nonunits 2183 90 = {37, 59, 74} := by
  decide +kernel

end PrimeFactors.FractionalNonunitPrefix
