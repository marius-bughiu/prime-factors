import PrimeFactors.FactorClueSumPrecision

/-! Express the exact precision of the fixed sum remainder in terms of the
actual factor gap. This diagnoses when a supplied clue gains extra digits. -/
namespace PrimeFactors.FactorClueSumGap

open FactorClueSumPrecision

private def period (m : ℕ) := if 2∣m then 2*m else m

private theorem cap_eq (m : ℕ) : cap m=m*period m := by
  unfold cap period
  split_ifs <;> ring

private theorem cop_period {p m : ℕ} (cop : p.Coprime m) : p.Coprime (period m) := by
  unfold period
  split_ifs with even
  · exact (cop.of_dvd_right even).mul_right cop
  · exact cop

private theorem first_difference {a p q m : ℕ} (clue : ∃ t,p=a+m*t) :
    ((a : ℤ)^2-p*q+a*m) ≡ (p : ℤ)*(p-q+m) [ZMOD (period m : ℕ)] := by
  obtain ⟨t,rfl⟩ := clue
  apply Int.modEq_iff_dvd.mpr
  push_cast
  obtain ⟨b,hb⟩ := Int.even_mul_succ_self (t : ℤ)
  have eq : ((a : ℤ)+m*t)*((a+m*t)-q+m)-(a^2-(a+m*t)*q+a*m) =
      (2*m)*(a*t+m*b) := by linear_combination (m : ℤ)^2*hb
  rw [eq]
  apply dvd_mul_of_dvd_left
  unfold period
  split_ifs <;> push_cast <;> simp

/-- For an even clue modulus the extra multiplier is gcd(p−q+m,2m).
For an odd clue modulus it is gcd(p−q,m). The supplied class is
the only factor information used in the product-side formula. -/
theorem gap_formula {p q a m : ℕ} (cop : a.Coprime m) (clue : ∃ t,p=a+m*t) :
    greatest (p*q) a m = m * (if 2∣m then Int.gcd ((p : ℤ)-q+m) (2*m)
      else Int.gcd ((p : ℤ)-q) m) := by
  have pc : p.Coprime m := by
    obtain ⟨t,rfl⟩ := clue
    exact (Nat.coprime_add_mul_left_left a m t).mpr cop
  rw [greatest,cap_eq,Nat.cast_mul,Nat.cast_mul,Int.gcd_mul_left,Int.natAbs_natCast,
    FactorClueSumPrecision.gcd_of_congruent (first_difference (q:=q) clue)]
  have cancel : Int.gcd ((p : ℤ)*(p-q+m)) (period m) =
      Int.gcd ((p : ℤ)-q+m) (period m) := by
    simp only [Int.gcd,Int.natAbs_mul,Int.natAbs_natCast]
    exact Nat.Coprime.gcd_mul_left_cancel _ (cop_period pc)
  rw [cancel]
  unfold period
  split_ifs <;> push_cast
  · rfl
  · congr 1
    exact FactorClueSumPrecision.gcd_of_congruent (Int.add_modEq_right)

/-- For an even positive modulus, the entire possible gain occurs exactly
when the factors differ by one copy of m modulo 2m. -/
theorem even_maximum {p q a m : ℕ} (pos : 0<m) (even : 2∣m)
    (cop : a.Coprime m) (clue : ∃ t,p=a+m*t) :
    greatest (p*q) a m=2*m^2 ↔ p ≡ q+m [MOD 2*m] := by
  rw [gap_formula cop clue,if_pos even,show 2*m^2=m*(2*m) by ring,
    Nat.mul_right_inj pos.ne']
  have criterion {d : ℤ} {n : ℕ} : Int.gcd d n=n ↔ (n : ℤ)∣d := by
    change Nat.gcd d.natAbs n=n ↔ _
    rw [Nat.gcd_eq_right_iff_dvd]
    exact Int.natCast_dvd.symm
  rw [show (2*(m : ℤ))=((2*m : ℕ) : ℤ) by push_cast; rfl,criterion]
  rw [←Int.natCast_modEq_iff,Int.modEq_iff_dvd]
  push_cast
  constructor <;> rintro ⟨b,hb⟩ <;> exact ⟨1-b,by linarith⟩

/-- For k positive, the (2k+1)-bit outcome occurs exactly when the primes
agree in their low k bits and differ in the next bit. -/
theorem dyadic_maximum {p q k : ℕ} (pos : 0<k) (odd : Odd p) :
    greatest (p*q) (p%2^k) (2^k)=2^(2*k+1) ↔ p ≡ q+2^k [MOD 2^(k+1)] := by
  have even : 2∣2^k := dvd_pow_self 2 pos.ne'
  have cop := (Nat.coprime_two_right.mpr odd).pow_right k
  have clue : ∃ t, p=p%2^k+2^k*t := ⟨p/2^k,(Nat.mod_add_div ..).symm⟩
  have reduced : (p%2^k).Coprime (2^k) := by
    change (p%2^k).gcd (2^k)=1
    rw [←Nat.gcd_rec]
    exact cop.symm
  have eq := even_maximum (q:=q) (by positivity : 0<2^k) even reduced clue
  rw [show 2*(2^k)^2=2^(2*k+1) by rw [←pow_mul,pow_succ]; ac_rfl,
    show 2*2^k=2^(k+1) by rw [pow_succ]; ac_rfl] at eq
  exact eq

end PrimeFactors.FactorClueSumGap
