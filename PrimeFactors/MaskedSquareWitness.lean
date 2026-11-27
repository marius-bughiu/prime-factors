import PrimeFactors.PrimePower
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorization.Basic

/-! A square multiplier can hide a quadratic nonresidue at a prime. This
determines the first power at which the original nonresidue reappears. -/

open private PrimeFactors.square_iff_integer_root from PrimeFactors.PrimePower

namespace PrimeFactors.MaskedSquareWitness

/-- Exactly cancel a common square scale from both the tested integer and
the modulus. No coprimality between the scale and the modulus is required. -/
theorem scale_iff {c : ℕ} (nz : c ≠ 0) (m : ℕ) (d : ℤ) :
    IsSquare ((d*(c:ℤ)^2:ℤ) : ZMod (c^2*m)) ↔ IsSquare (d : ZMod m) := by
  rw [PrimeFactors.square_iff_integer_root,PrimeFactors.square_iff_integer_root]
  push_cast
  constructor
  · rintro ⟨y,k,eq⟩
    have dvd : (c:ℤ)^2 ∣ y^2 := ⟨d-m*k,by linear_combination -eq⟩
    obtain ⟨z,rfl⟩ := (Int.pow_dvd_pow_iff (by decide : 2≠0)).mp dvd
    refine ⟨z,k,?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 2 (by exact_mod_cast nz : (c:ℤ)≠0))
    linear_combination eq
  · rintro ⟨y,k,eq⟩
    exact ⟨c*y,k,by linear_combination (c:ℤ)^2*eq⟩

/-- A square unit can also be removed while keeping the same modulus. -/
theorem unit_iff {u m : ℕ} (cop : u.Coprime m) (d : ℤ) :
    IsSquare ((d*(u:ℤ)^2:ℤ) : ZMod m) ↔ IsSquare (d : ZMod m) := by
  let z := ZMod.unitOfCoprime u cop
  have val : (z : ZMod m)=(u:ZMod m) := ZMod.coe_unitOfCoprime u cop
  push_cast
  rw [←val]
  constructor
  · intro sq
    have cancel := sq.mul (IsSquare.sq ((z⁻¹ : (ZMod m)ˣ) : ZMod m))
    simpa only [mul_assoc,←mul_pow,Units.mul_inv,one_pow,mul_one] using cancel
  · exact fun sq => sq.mul (IsSquare.sq _)

/-- Strip the indicated a powers of p from the multiplier. The unit
remainder may be arbitrary; the residual test can use any prime-power depth. -/
theorem at_depth {p a u : ℕ} (nz : p ≠ 0) (cop : u.Coprime p) (k : ℕ) (d : ℤ) :
    IsSquare ((d*((p^a*u:ℕ):ℤ)^2:ℤ) : ZMod (p^(2*a+k))) ↔ IsSquare (d : ZMod (p^k)) := by
  have power : p^(2*a+k)=(p^a)^2*p^k := by rw [pow_add,←pow_mul]; congr 2; omega
  have target : d*((p^a*u:ℕ):ℤ)^2=(d*(u:ℤ)^2)*((p^a:ℕ):ℤ)^2 := by push_cast; ring
  rw [power,target,scale_iff (pow_ne_zero _ nz),unit_iff (cop.pow_right k)]

private theorem project {m n : ℕ} {D : ℤ} (dvd : m∣n) (h : IsSquare (D : ZMod n)) :
    IsSquare (D : ZMod m) := by
  simpa only [map_intCast] using IsSquare.map (ZMod.castHom dvd (ZMod m)) h

/-- For a nonresidue modulo p, multiplication by an integer of valuation a
hides it at precisely the powers p^k with k ≤ 2a. The first rejection is
therefore p^(2a+1), even if the product is zero modulo p. -/
theorem square_depth_iff {p x : ℕ} (prime : p.Prime) (nz : x≠0) {d : ℤ}
    (miss : ¬IsSquare (d : ZMod p)) (k : ℕ) :
    IsSquare ((d*(x:ℤ)^2:ℤ) : ZMod (p^k)) ↔ k ≤ 2*x.factorization p := by
  let a := x.factorization p
  let u := x/p^a
  have eq : p^a*u=x := Nat.ordProj_mul_ordCompl_eq_self x p
  have cop : u.Coprime p := (Nat.coprime_ordCompl prime nz).symm
  change _ ↔ k ≤ 2*a
  constructor
  · intro sq
    by_contra! high
    have seen := project (pow_dvd_pow p (show 2*a+1≤k by omega)) sq
    rw [←eq] at seen
    have hidden := (at_depth prime.ne_zero cop 1 d).mp seen
    exact miss ((congrArg (fun m : ℕ => IsSquare (d : ZMod m)) (pow_one p)).mp hidden)
  · intro low
    rw [PrimeFactors.square_iff_integer_root]
    refine ⟨0,?_⟩
    simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,sub_zero,Nat.cast_pow]
    have power : (p:ℤ)^(2*a) ∣ (x:ℤ)^2 := by
      rw [←eq,Nat.cast_mul,Nat.cast_pow,mul_pow,←pow_mul, Nat.mul_comm a 2]
      exact dvd_mul_right ..
    exact ((pow_dvd_pow (p:ℤ) low).trans power).trans (dvd_mul_left ..)

theorem first_rejection {p x : ℕ} (prime : p.Prime) (nz : x≠0) {d : ℤ}
    (miss : ¬ IsSquare (d : ZMod p)) :
    ¬ IsSquare ((d*(x:ℤ)^2:ℤ) : ZMod (p^(2*x.factorization p+1))) :=
  (square_depth_iff prime nz miss _).not.mpr (by omega)

/-- Both signs of a signed multiplier give the same threshold. -/
theorem signed_first_rejection {p : ℕ} (prime : p.Prime) {x d : ℤ} (nz : x≠0)
    (miss : ¬IsSquare (d : ZMod p)) :
    ¬IsSquare ((d*x^2:ℤ) : ZMod (p^(2*x.natAbs.factorization p+1))) := by
  simpa only [Int.natAbs_sq] using first_rejection prime (Int.natAbs_ne_zero.mpr nz) miss

/-- When d ≡ 5 mod 8, stripping the power of two and the odd multiplier
reduces rejection to the three low bits. -/
theorem dyadic_first_rejection {a u : ℕ} (odd : Odd u) {d : ℤ} (five : d%8=5) :
    ¬IsSquare ((d*((2^a*u:ℕ):ℤ)^2:ℤ) : ZMod (2^(2*a+3))) := by
  have cop : u.Coprime 2 := (Nat.coprime_two_left.mpr odd).symm
  rw [at_depth (by decide : 2≠0) cop 3 d]
  change ¬IsSquare (d : ZMod 8)
  have eq : (d : ZMod 8)=5 := ((ZMod.intCast_eq_intCast_iff_dvd_sub 5 d 8).mpr
    (show (8:ℤ) ∣ d-5 from ⟨d/8,by omega⟩)).symm
  rw [eq]
  rintro ⟨y,hy⟩
  exact (by decide +kernel : ∀ t : ZMod 8, 5≠t*t) y hy

/-- For this dyadic class the threshold is sharp as well: modulo four
the remaining unit is one, and its root lifts back with the square scale. -/
theorem dyadic_depth_iff {a u : ℕ} (odd : Odd u) {d : ℤ} (five : d%8=5) (k : ℕ) :
    IsSquare ((d*((2^a*u:ℕ):ℤ)^2:ℤ) : ZMod (2^k)) ↔ k ≤ 2*a+2 := by
  constructor
  · intro h
    by_contra! high
    exact dyadic_first_rejection odd five (project (pow_dvd_pow 2 (show 2*a+3≤k by omega)) h)
  · intro lo
    apply project (pow_dvd_pow 2 lo)
    rw [at_depth (by decide : 2≠0) (Nat.coprime_two_left.mpr odd).symm 2 d]
    change IsSquare (d : ZMod 4)
    have eq : (d : ZMod 4)=1 := ((ZMod.intCast_eq_intCast_iff_dvd_sub 1 d 4).mpr
      (show (4:ℤ) ∣ d-1 from ⟨(d-1)/4,by omega⟩)).symm
    rw [eq]
    exact ⟨1,by simp⟩

/-- At 3 and 9 the residue 18 is zero; its first rejection is at 27. -/
theorem control18 : IsSquare (18 : ZMod 3) ∧ IsSquare (18 : ZMod 9) ∧ ¬IsSquare (18 : ZMod 27) := by
  have no : ¬IsSquare (2 : ZMod 3) := by
    rintro ⟨y,hy⟩
    exact (by decide +kernel : ∀ t : ZMod 3, 2≠t*t) y hy
  refine ⟨⟨0,by decide⟩,⟨0,by decide⟩,?_⟩
  have exp : 3^(2*(3:ℕ).factorization 3+1)=27 := by
    rw [Nat.prime_three.factorization_self]
    decide
  have h := (congrArg (fun m : ℕ => ¬ IsSquare (((2:ℤ)*3^2:ℤ) : ZMod m)) exp).mp
    (first_rejection (x:=3) (d:=2) Nat.prime_three (by decide) no)
  norm_num at h ⊢
  exact h

end PrimeFactors.MaskedSquareWitness
