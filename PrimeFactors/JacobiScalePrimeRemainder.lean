import PrimeFactors.JacobiSquareScaleGcd

/-! A squarefree successful scale constrains the two factor residues modulo
one higher prime power than a given divisor of N−1. -/
namespace PrimeFactors.JacobiScalePrimeRemainder

open Finset

/-- If l divides the true squarefree scale and l^k divides N−1, one factor
is 1 modulo l^(k+1) and the other agrees with N. This includes k=0. -/
theorem factor_classes {p q t y l k : ℕ} (hp : 1 < p) (hq : 1 < q)
    (free : Squarefree t) (hit : t*y^2=(p-1)*(q-1)) (prime : l.Prime) (lt : l ∣ t)
    (known : l^k ∣ p*q-1) :
    (p ≡ 1 [MOD l^(k+1)] ∧ q ≡ p*q [MOD l^(k+1)]) ∨
    (q ≡ 1 [MOD l^(k+1)] ∧ p ≡ p*q [MOD l^(k+1)]) := by
  have pg := Nat.sub_pos_of_lt hp
  have qg := Nat.sub_pos_of_lt hq
  have root := JacobiSquareScaleGcd.divides_root hp hq free hit known (pow_dvd_pow_of_dvd lt k)
  have enough : l^(2*k+1) ∣ (p-1)*(q-1) := by
    rw [←hit,show l^(2*k+1) = l*(l^k)^2 by rw [pow_succ,Nat.mul_comm 2 k,pow_mul]; ring]
    exact Nat.mul_dvd_mul lt (pow_dvd_pow_of_dvd root 2)
  have count := (prime.pow_dvd_iff_le_factorization (Nat.mul_pos pg qg).ne').mp enough
  rw [Nat.factorization_mul pg.ne' qg.ne',Finsupp.add_apply] at count
  by_cases divides : l^(k+1) ∣ p-1
  · have one := ((Nat.modEq_iff_dvd' hp.le).mpr divides).symm
    exact Or.inl ⟨one,by simpa only [one_mul] using one.symm.mul (Nat.ModEq.refl q)⟩
  · have upper := mt (prime.pow_dvd_iff_le_factorization pg.ne').mpr divides
    have dq : l^(k+1) ∣ q-1 := (prime.pow_dvd_iff_le_factorization qg.ne').mpr (by omega)
    have one := ((Nat.modEq_iff_dvd' hq.le).mpr dq).symm
    exact Or.inr ⟨one,by simpa only [mul_one] using (Nat.ModEq.refl p).mul one.symm⟩

/-- If p≤q≤2p the smaller factor lies between the ceiling of sqrt(N/2)
and the floor of sqrt(N), including both endpoints. -/
noncomputable def balancedBand (N : ℕ) : Finset ℕ := Icc (((N-1)/2).sqrt+1) N.sqrt

theorem in_band {p q : ℕ} (hp : 0 < p) (le : p ≤ q) (bal : q ≤ 2*p) :
    p ∈ balancedBand (p*q) := by
  have prod := Nat.mul_pos hp (hp.trans_le le)
  have top : p*q ≤ p^2*2 := (Nat.mul_le_mul_left p bal).trans_eq (by ring)
  have low := Nat.sqrt_lt'.mpr ((Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
    (show p*q-1 < p^2*2 by omega))
  exact mem_Icc.mpr ⟨Nat.succ_le_of_lt low,Nat.le_sqrt.mpr (Nat.mul_le_mul_left p le)⟩

/-- An interval with neither residue excludes all squarefree successful scales divisible by l.
The supplied set can be a smaller interval or the odd members of one, provided it contains p. -/
theorem exclude {p q t l k : ℕ} (box : Finset ℕ) (inside : p ∈ box)
    (hp : 1 < p) (le : p ≤ q) (bal : q ≤ 2*p) (prime : l.Prime) (known : l^k ∣ p*q-1)
    (empty : ∀ x ∈ box, ¬ (x ≡ 1 [MOD l^(k+1)] ∨ x ≡ p*q [MOD l^(k+1)]))
    (free : Squarefree t) (lt : l ∣ t) : predecessorSquareSum (p*q) t ≠ p+q := by
  intro sum
  have p1 := hp.le
  have q1 := p1.trans le
  have h := JacobiPeriodScales.sum_iff_square (P:=p-1) (Q:=q-1)
    (Nat.sub_pos_of_lt hp) (Nat.sub_le_sub_right le 1)
    (by simpa only [Nat.sub_add_cancel p1,Nat.sub_add_cancel q1] using bal) (Nat.pos_of_ne_zero free.ne_zero)
  simp only [Nat.sub_add_cancel p1,Nat.sub_add_cancel q1] at h
  obtain ⟨y,hit⟩ := h.mp sum
  obtain ⟨pOne,_⟩ | ⟨_,pN⟩ := factor_classes hp (hp.trans_le le) free hit prime lt known
  · exact empty p inside (Or.inl pOne)
  · exact empty p inside (Or.inr pN)

/-- At 2627 the lower-bound height test passes at scale 13. Neither 1 nor 92
modulo 169 occurs in [37,51], so the complete class of multiples of 13 is excluded. -/
theorem control_2627 :
    balancedBand 2627 = Icc 37 51 ∧ 2627%169=92 ∧ 13*13^2<2627 ∧
    ∀ t : ℕ, Squarefree t → 13∣t → predecessorSquareSum 2627 t ≠ 37+71 := by
  have low : 36 = Nat.sqrt ((2627-1)/2) := Nat.eq_sqrt.mpr (by decide)
  have high : 51 = Nat.sqrt 2627 := Nat.eq_sqrt.mpr (by decide)
  have band : balancedBand 2627 = Icc 37 51 := by
    unfold balancedBand
    rw [←low,←high]
  refine ⟨band,by decide,by decide,?_⟩
  intro t free div
  apply exclude (p:=37) (q:=71) (l:=13) (k:=1) (Icc 37 51)
    (mem_Icc.mpr ⟨by decide,by decide⟩) (by decide) (by decide) (by decide)
    (by decide) (by decide) _ free div
  intro x hx
  rw [mem_Icc] at hx
  change ¬ (x%169=1 ∨ x%169=92)
  rw [Nat.mod_eq_of_lt (by omega : x < 169)]
  omega

end PrimeFactors.JacobiScalePrimeRemainder
