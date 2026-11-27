import PrimeFactors.ShortRootNorm

namespace PrimeFactors.ShortRootNormPositive

/-- A single supplied square root of 2 gives a positive representation of A
with norm +A. A negative norm is reversed by the unit 1+√2. -/
theorem two {A : ℕ} (ha : 2≤A) (root : IsSquare (2 : ZMod A)) :
    ∃ x t : ℕ, 0<x ∧ 0<t ∧ x^2=A+2*t^2 := by
  letI : NeZero A := ⟨by omega⟩
  obtain ⟨r,hr⟩ := root
  have rr : ((r.val:ℕ):ZMod A)^2=(2:ℕ) := by simpa [pow_two] using hr.symm
  have ns : ¬IsSquare (2:ℕ) := Nat.prime_two.prime.not_isSquare
  let v := ShortRootNorm.reduce A r.val
  have bp : 0<v.2 := (ShortRootNorm.bounds r.val ha).1
  have aeq : (v.1.natAbs:ℤ)^2=v.1^2 := by rw [Int.natCast_natAbs,sq_abs]
  rcases ShortRootNorm.norm ha (by decide : 2≤3) ns rr with pos|neg
  · have h : (v.1.natAbs:ℤ)^2=(A:ℤ)+2*v.2^2 := by
      rw [aeq]
      change v.1^2-(2:ℤ)*(v.2:ℤ)^2=A at pos
      linarith
    have nat : v.1.natAbs^2=A+2*v.2^2 := by exact_mod_cast h
    refine ⟨v.1.natAbs,v.2,?_,bp,nat⟩
    by_contra! z
    have : v.1.natAbs=0 := by omega
    rw [this] at nat
    omega
  · refine ⟨v.1.natAbs+2*v.2,v.1.natAbs+v.2,by omega,by omega,?_⟩
    change v.1^2-(2:ℤ)*(v.2:ℤ)^2= -(A:ℤ) at neg
    exact_mod_cast (show ((v.1.natAbs:ℤ)+2*v.2)^2=A+2*((v.1.natAbs:ℤ)+v.2)^2 by
      nlinarith only [aeq,neg])

end PrimeFactors.ShortRootNormPositive
