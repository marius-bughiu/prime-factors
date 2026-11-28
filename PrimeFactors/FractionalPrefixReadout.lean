import PrimeFactors.FractionalNonunitPrefix
import PrimeFactors.FractionalPrefixResidues

/-! A constant ordinary residue correction turns a public nonunit count into the prime sum. -/
namespace PrimeFactors.FractionalPrefixReadout

open FractionalNonunitPrefix FractionalPrefixResidues

/-- The residue correction of the actual prime pair uses only their ordinary remainders. -/
theorem correction_pair {p q m : ℕ} (pc : p.Coprime m) (qc : q.Coprime m) :
    let a := ZMod.unitOfCoprime p pc
    let b := ZMod.unitOfCoprime q qc
    correction (a*b) a = p%m+q%m := by
  simp only [correction, mul_div_cancel_left, ZMod.coe_unitOfCoprime, ZMod.val_natCast]

private theorem product_neg_iff {n m : ℕ} (cop : n.Coprime m) :
    ZMod.unitOfCoprime n cop = -1 ↔ m ∣ n+1 := by
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.cast_add, Nat.cast_one, add_eq_zero_iff_eq_neg,
    Units.ext_iff, ZMod.coe_unitOfCoprime, Units.val_neg, Units.val_one]

/-- Exactly the divisors of gcd(24,N+1) have a correction constant for every possible unit pair. -/
theorem constant_iff_dvd_gcd {n m : ℕ} [NeZero m] (hm : 2 ≤ m) (cop : n.Coprime m) :
    (∃ c : ℕ, ∀ x, correction (ZMod.unitOfCoprime n cop) x = c) ↔ m ∣ Nat.gcd 24 (n+1) := by
  rw [constant_iff hm, product_neg_iff, Nat.dvd_gcd_iff, and_comm]

/-- Every eligible denominator dividing both 24 and pq+1 gives the prime sum directly. -/
theorem sum_eq {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p ≠ q)
    (hm : 2 ≤ m) (d24 : m ∣ 24) (residue : m ∣ p*q+1) :
    p+q = m*(prefixCount (p*q) m+1) := by
  letI : NeZero m := ⟨by omega⟩
  have whole : (p*q).Coprime m := (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)).of_dvd_right residue
  have pc := whole.of_dvd_left (dvd_mul_right p q)
  have qc := whole.of_dvd_left (dvd_mul_left q p)
  let a := ZMod.unitOfCoprime p pc
  let b := ZMod.unitOfCoprime q qc
  have ab : a*b = ZMod.unitOfCoprime (p*q) whole := by
    apply Units.ext
    simp only [a, b, Units.val_mul, ZMod.coe_unitOfCoprime, Nat.cast_mul]
  have corr := correction_pair pc qc
  change correction (a*b) a = p%m+q%m at corr
  rw [ab, (product_neg_iff whole).mpr residue, correction_of_dvd hm d24] at corr
  have scale := scaled hp hq diff hm
  rw [← corr] at scale
  simpa only [Nat.mul_add, Nat.mul_one] using scale.symm

/-- For odd input the greatest admissible denominator is at least two and bounded by 24. -/
theorem greatest {n : ℕ} (odd : Odd n) :
    let g := Nat.gcd 24 (n+1)
    2 ≤ g ∧ g ∣ 24 ∧ g ∣ n+1 ∧ ∀ m, m ∣ 24 → m ∣ n+1 → m ≤ g := by
  let g := Nat.gcd 24 (n+1)
  have pos : 0 < g := Nat.gcd_pos_of_pos_left _ (by decide : 0 < 24)
  refine ⟨Nat.le_of_dvd pos (Nat.dvd_gcd (by decide) odd.add_one.two_dvd),
          Nat.gcd_dvd_left .., Nat.gcd_dvd_right .., ?_⟩
  exact fun _ a b => Nat.le_of_dvd pos (Nat.dvd_gcd a b)

theorem greatest_sum {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p ≠ q)
    (odd : Odd (p*q)) :
    let g := Nat.gcd 24 (p*q+1)
    p+q = g*(prefixCount (p*q) g+1) :=
  sum_eq hp hq diff (greatest odd).1 (greatest odd).2.1 (greatest odd).2.2.1

/-- At 2183, denominator 24 gives three positive nonunits and hence prime sum 96. -/
theorem example_2183 :
    Nat.gcd 24 (2183+1)=24 ∧ prefixCount 2183 24=3 ∧ 24*(prefixCount 2183 24+1)=96 := by
  have count := quotient_sum (p := 37) (q := 59) (m := 24) (by decide) (by decide) (by decide) (by decide)
  change prefixCount 2183 24 = 3 at count
  exact ⟨by decide, count, by rw [count]⟩

end PrimeFactors.FractionalPrefixReadout
