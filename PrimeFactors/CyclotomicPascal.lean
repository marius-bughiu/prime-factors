import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

namespace PrimeFactors.CyclotomicPascal

/-- The scalar recurrence comes from powering in the real quadratic subfield. -/
theorem odd_power {R : Type*} [CommRing R] (z zi : R) (unit : z*zi=1) (e : ℕ) :
    (1+z)^(2*e+1) = (1+z)*z^e*(2+z+zi)^e := by
  have h : (1+z)^2 = z*(2+z+zi) := by linear_combination -unit
  rw [pow_succ,pow_mul,h,mul_pow]
  ring

theorem quadratic_expansion {R : Type*} [CommRing R] (f : ℕ → R) (v w : R)
    (step : ∀ n, f (n+2) = (v+w)*f (n+1) - v*w*f n) (e : ℕ) :
    (v-w)*f e = (f 1-w*f 0)*v^e + (v*f 0-f 1)*w^e := by
  induction e using Nat.twoStepInduction with
  | zero => simp; ring
  | one => simp; ring
  | more n h₀ h₁ =>
    rw [step]
    simp only [pow_succ] at h₁ ⊢
    linear_combination (v+w)*h₁ - v*w*h₀

/-- All zero coordinates from the same orientation must give the same power
of the eigenvalue ratio, unless that coordinate vanishes identically. -/
theorem two_zeros {F : Type*} [Field F] (f : ℕ → F) {v w : F}
    (roots : v ≠ w) (wn : w ≠ 0) (nontrivial : f 0 ≠ 0 ∨ f 1 ≠ 0)
    (step : ∀ n, f (n+2) = (v+w)*f (n+1)-v*w*f n)
    {i j : ℕ} (fi : f i = 0) (fj : f j = 0) : (v/w)^i = (v/w)^j := by
  let A := f 1-w*f 0
  let B := v*f 0-f 1
  have vanish (k : ℕ) (zero : f k = 0) : A*(v/w)^k = -B := by
    have h := quadratic_expansion f v w step k
    rw [zero,mul_zero] at h
    rw [div_pow]
    field_simp [wn]
    dsimp [A,B]
    linear_combination -h
  have ai := vanish i fi
  have an : A ≠ 0 := by
    intro az
    have bz : B = 0 := by simpa [az] using ai.symm
    have z0 : (v-w)*f 0=0 := by dsimp [A] at az; dsimp [B] at bz; linear_combination az+bz
    have z := (mul_eq_zero.mp z0).resolve_left (sub_ne_zero.mpr roots)
    rcases nontrivial with h | h
    · exact h z
    · exact h (by simpa [A,z] using az)
  exact mul_left_cancel₀ an (ai.trans (vanish j fj).symm)

/-- The integer sequence used to count primes of short ratio order. -/
def lucasU (trace norm : ℤ) (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | 1 => 1
  | n+2 => trace * lucasU trace norm (n+1) - norm * lucasU trace norm n

theorem lucasU_identity {R : Type*} [CommRing R] (v w : R) {t s : ℤ}
    (tr : (t:R)=v+w) (nm : (s:R)=v*w) (e : ℕ) :
    (v-w)*(lucasU t s e : R) = v^e-w^e := by
  have h := quadratic_expansion (fun n => (lucasU t s n : R)) v w (by
    intro n
    simp only [lucasU, Int.cast_sub, Int.cast_mul,tr,nm]) e
  simpa [lucasU, sub_eq_add_neg] using h

/-- The m=12 polynomial gives the real quadratic v=2+2z-z³. -/
theorem twelfth_quadratic {R : Type*} [CommRing R] (z : R) (h : z^4-z^2+1=0) :
    z*(z-z^3)=1 ∧ (2+2*z-z^3)^2-4*(2+2*z-z^3)+1=0 := by
  constructor
  · linear_combination -h
  · linear_combination (z^2-3)*h

/-- A whole polynomial-remainder certificate over any ring modulo 143. -/
theorem example_projection {R : Type*} [CommRing R] (z : R)
    (rel : z^4-z^2+1=0) (modulus : (143:R)=0) :
    (1+z)^143 = 26+26*z+131*z^2+129*z^3 := by
  have p2 : (1+z)^2 = 1+2*z+z^2 := by
    ring
  have p4 : (1+z)^4 = 4*z+7*z^2+4*z^3 := by
    rw [show 4 = 2*2 by decide, pow_mul, p2]
    linear_combination (1)*rel
  have p8 : (1+z)^8 = 46-56*z-46*z^2-31*z^3 := by
    rw [show 8 = 4*2 by decide, pow_mul, p4]
    linear_combination (97+56*z+16*z^2)*rel + (-1+z^2+z^3)*modulus
  have p17 : (1+z)^17 = -4+4*z+67*z^2+63*z^3 := by
    rw [show 17 = 8*2+1 by decide, pow_succ, pow_mul, p8]
    linear_combination (11701+9401*z+3813*z^2+961*z^3)*rel + (-67-87*z+11*z^2+67*z^3)*modulus
  have p35 : (1+z)^35 = 26+26*z+40*z^2-66*z^3 := by
    rw [show 35 = 17*2+1 by decide, pow_succ, pow_mul, p17]
    linear_combination (17436+17404*z+12411*z^2+3969*z^3)*rel + (-122-122*z+31*z^2+91*z^3)*modulus
  have p71 : (1+z)^71 = 65+65*z+66*z^2+12*z^3 := by
    rw [show 71 = 35*2+1 by decide, pow_succ, pow_mul, p35]
    linear_combination (-4108-2756*z-924*z^2+4356*z^3)*rel + (33+33*z+6*z^2-40*z^3)*modulus
  rw [show 143 = 71*2+1 by decide, pow_succ, pow_mul, p71]
  linear_combination (17784+7644*z+1728*z^2+144*z^3)*rel + (-95+35*z+260*z^2+212*z^3)*modulus

theorem example_factors : Nat.gcd 26 143 = 13 ∧ Nat.Prime 11 ∧ Nat.Prime 13 ∧
    (11:ℕ)*13=143 := by decide

end PrimeFactors.CyclotomicPascal
