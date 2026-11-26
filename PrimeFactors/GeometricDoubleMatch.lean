import PrimeFactors.SumSignatureCost
import PrimeFactors.Fermat
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! Recovering the square of the local period when exactly two exponents match.
Only the constant, linear and quadratic coefficients of each factor are needed. -/

namespace PrimeFactors.GeometricDoubleMatch

open Finset Polynomial

set_option exponentiation.threshold 4096

section Algebra
variable {R : Type*} [CommRing R]

/-- Through degree two this is y(1+zt) − (g(1+t))^i. -/
noncomputable def factor (y g z : R) (i : ℕ) : R[X] :=
  C (y-g^i) + X*(C (z*y-i*g^i) + X*C (-(i.choose 2 : R)*g^i))

noncomputable def reading (I : Finset ℕ) (y g z : R) : R :=
  (∏ i ∈ I, factor y g z i).coeff 2

private theorem at_hit {y g : R} (z : R) {i : ℕ} (hit : g^i=y) :
    factor y g z i = X*(C (y*(z-i)) + X*C (-(i.choose 2 : R)*y)) := by
  simp only [factor, hit, sub_self, map_zero, zero_add]
  congr 3
  ring

/-- The leading coefficient in t records the two actual exponent labels, even
when both first derivatives vanish. The omitted entries contribute one scalar. -/
theorem two_hits {I : Finset ℕ} {a b : ℕ} (ha : a∈I) (hb : b∈I) (ne : a≠b)
    (y g z : R) (pa : g^a=y) (pb : g^b=y) :
    reading I y g z =
      (y^2 * ∏ i ∈ (I.erase a).erase b, (y-g^i)) * (z-a)*(z-b) := by
  have hb' : b∈I.erase a := mem_erase.mpr ⟨ne.symm,hb⟩
  unfold reading
  rw [←mul_prod_erase I (fun i => factor y g z i) ha,
    ←mul_prod_erase (I.erase a) (fun i => factor y g z i) hb',at_hit z pa,at_hit z pb]
  let P := ∏ i ∈ (I.erase a).erase b, factor y g z i
  let U (i : ℕ) := C (y*(z-i)) + X*C (-(i.choose 2 : R)*y)
  change ((X*U a)*(X*U b*P)).coeff 2 = _
  rw [show (X*U a)*(X*U b*P) = (U a * U b * P)*X^2 by ring, Polynomial.coeff_mul_X_pow']
  simp only [le_refl, if_true, Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_mul]
  have constant : P.eval 0 = ∏ i ∈ (I.erase a).erase b, (y-g^i) := by
    simp only [P,Polynomial.eval_prod,factor,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,zero_mul,add_zero]
  rw [constant]
  simp only [U,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,
    zero_mul,add_zero]
  ring

/-- The combination uses no modular divisions, including division by two. -/
def leading (C : R → R) := C 1 + C (-1) - 2*C 0
def linear (C : R → R) := C (-1) - C 1
def discriminant (C : R → R) := (linear C)^2 - 8*(leading C)*C 0

theorem extract {c : R → R} {u a b : R} (evaluates : ∀ z, c z = u*(z-a)*(z-b)) :
    leading c = 2*u ∧ linear c = (2*u)*(a+b) ∧
      discriminant c = (leading c)^2*(b-a)^2 := by
  simp only [leading, linear, discriminant, evaluates]
  constructor
  · ring
  constructor <;> ring

/-- All three public readings commute with reduction to either hidden prime. -/
theorem map_reading {T : Type*} [CommRing T] (f : R →+* T) (I : Finset ℕ) (y g z : R) :
    f (reading I y g z) = reading I (f y) (f g) (f z) := by
  unfold reading
  rw [←Polynomial.coeff_map, Polynomial.map_prod]
  simp only [factor, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  simp only [map_sub, map_pow, map_mul, map_neg, map_natCast]

end Algebra

/-- Between the two matches there is exactly one period. The two tails contain
fewer than one period apiece. This argument also works for any finite group. -/
theorem spacing {G : Type*} [Group G] [Finite G] {W a b : ℕ} (g y : G)
    (ab : a<b) (inside : b≤W) (hits : ∀ i ≤ W, g^i=y ↔ i=a ∨ i=b) :
    b=a+orderOf g ∧ W<3*orderOf g := by
  let d := orderOf g
  have dp : 0<d := orderOf_pos g
  have ha := (hits a (ab.le.trans inside)).mpr (Or.inl rfl)
  have hb := (hits b inside).mpr (Or.inr rfl)
  have perm (i : ℕ) : g^(i+d)=g^i := by simp [d,pow_add,pow_orderOf_eq_one]
  have dvd : d ∣ b-a :=
    orderOf_dvd_of_pow_eq_one (x:=g) (n:=b-a) (by
      apply mul_left_cancel (a:=g^a)
      rw [←pow_add,Nat.add_sub_of_le ab.le,mul_one,hb,ha])
  have step : d≤b-a := Nat.le_of_dvd (by omega) dvd
  have next := (hits (a+d) (by omega)).mp ((perm a).trans ha)
  have before : a<d := by
    apply Nat.lt_of_not_ge
    intro rev
    have eq : g^(a-d)=y := by
      rw [←perm (a-d), Nat.sub_add_cancel rev, ha]
    have old := (hits (a-d) (by omega)).mp eq
    omega
  have after : W<b+d := by
    apply Nat.lt_of_not_ge
    intro bad
    have extra := (hits (b+d) bad).mp ((perm b).trans hb)
    omega
  change b=a+d ∧ W<3*d
  omega

/-- A local period producing just two matches has a small cofactor in the
predecessor of either 1024-bit factor when the public interval has width ≥2^1020. -/
theorem cofactor_lt {p W d k : ℕ} (narrow : W<3*d) (size : p≤16*W)
    (cofactor : k*d+1=p) : k<48 := by
  by_contra! large
  have high := Nat.mul_le_mul_right d large
  omega

/-- Width of the actual interval, including both endpoint roundings. -/
theorem width_at_2048 {n : ℕ} (bits : 2^2047≤n) :
    2^1020≤(9*n/2).sqrt-ceilSqrt (4*n) := by
  let t := (4*n).sqrt
  have low := (SumSignatureCost.interval_span bits (t+1)
    (Finset.mem_Icc.mpr ⟨le_rfl,Nat.le_add_right ..⟩)).1
  have high := (SumSignatureCost.interval_span bits (t+1+2^1020)
    (Finset.mem_Icc.mpr ⟨Nat.le_add_right ..,le_rfl⟩)).2
  have lower := ceilSqrt_le_iff.mpr low
  have upper : t+1+2^1020 ≤ (9*n/2).sqrt := Nat.le_sqrt'.mpr
    ((Nat.le_div_iff_mul_le (by decide : 0<2)).mpr (by simpa only [mul_comm 2] using high))
  omega

/-- The tested indices 1 through 47 contain the order cofactor at each prime
with exactly two matches throughout the actual public interval. -/
theorem local_cofactor {n p W a b : ℕ} (bits : 2^2047≤n)
    (width : W=(9*n/2).sqrt-ceilSqrt (4*n)) (hp : p.Prime) (size : p<2^1024)
    (g y : (ZMod p)ˣ) (ab : a<b) (inside : b≤W)
    (hits : ∀ i ≤ W, g^i=y ↔ i=a ∨ i=b) :
    ∃ k, 0<k ∧ k<48 ∧ k*(b-a)+1=p := by
  letI : Fact p.Prime := ⟨hp⟩
  have ⟨gap, narrow⟩ := spacing g y ab inside hits
  have divides : orderOf g ∣ p-1 := (Nat.prime_iff_card_units p).mp hp ▸ orderOf_dvd_card
  obtain ⟨k,hk⟩ := divides
  have eq : k*orderOf g+1=p := by rw [mul_comm,←hk]; have := hp.one_le; omega
  have hi : p ≤ 16*W := by
    have cap : (2:ℕ)^1024 = 16*2^1020 := by decide +kernel
    have minW : 2^1020≤W := width ▸ width_at_2048 bits
    exact size.le.trans (cap ▸ Nat.mul_le_mul_left 16 minW)
  refine ⟨k,?_,cofactor_lt narrow hi eq,?_⟩
  · apply Nat.pos_of_ne_zero
    intro zero
    rw [zero,zero_mul,zero_add] at eq
    exact hp.ne_one eq.symm
  · simpa [gap] using eq

/-- A squared-period reading splits whenever the two small order cofactors differ.
The field calculation characterizes every zero of the public gcd probe. -/
theorem probe_zero {K : Type*} [Field K] {a d k h : K}
    (unit : a≠0) (cofactor : h*d = -1) :
    k^2*(a^2*d^2)-a^2=0 ↔ k=h ∨ k= -h := by
  have hne : h≠0 := by intro hz; simp [hz] at cofactor
  have prod : (k^2*(a^2*d^2)-a^2)*h^2 = a^2*((k-h)*(k+h)) := by
    have hh : (h*d)^2=(-1:K)^2 := congrArg (·^2) cofactor
    linear_combination k^2*a^2*hh
  rw [←mul_eq_zero_iff_right (pow_ne_zero 2 hne), prod, mul_eq_zero,
    or_iff_right (pow_ne_zero 2 unit), mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- In a prime field the computed discriminant tests exactly the positive
cofactor on this bounded menu. No inverse of the quadratic leading term is needed. -/
theorem local_probe {p W a b k h : ℕ} [Fact p.Prime]
    (g y : ZMod p) (nonzero : y≠0) (two : (2:ZMod p)≠0) (ab : a<b) (inside : b≤W)
    (hits : ∀ i≤W, g^i=y ↔ i=a ∨ i=b) (cofactor : h*(b-a)+1=p)
    (kh : k+h<p) :
    let c := reading (range (W+1)) y g
    (k : ZMod p)^2*discriminant c-(leading c)^2=0 ↔ k=h := by
  let I := range (W+1)
  have ai : a∈I := mem_range.mpr (by omega)
  have bi : b∈I := mem_range.mpr (by omega)
  let u := y^2 * ∏ i ∈ (I.erase a).erase b, (y-g^i)
  have non : u≠0 := mul_ne_zero (pow_ne_zero 2 nonzero) (Finset.prod_ne_zero_iff.mpr (by
    intro i hi
    obtain ⟨nb,hi⟩ := mem_erase.mp hi
    obtain ⟨na,hi⟩ := mem_erase.mp hi
    have less := mem_range.mp hi
    exact sub_ne_zero.mpr (fun h => ((hits i (by omega)).mp h.symm).elim na nb)))
  have value := extract (fun z => two_hits ai bi ab.ne y g z
    ((hits a (by omega)).mpr (Or.inl rfl)) ((hits b inside).mpr (Or.inr rfl)))
  let c := reading I y g
  change (k:ZMod p)^2*discriminant c-(leading c)^2=0 ↔ k=h
  have le : leading c=2*u := value.1
  have eq : (h:ZMod p)*((b:ZMod p)-a) = -1 := by
    apply eq_neg_of_add_eq_zero_left
    rw [←Nat.cast_sub ab.le,←Nat.cast_mul,←Nat.cast_one (R:=ZMod p),←Nat.cast_add,cofactor]
    exact ZMod.natCast_self p
  rw [value.2.2,probe_zero (le ▸ mul_ne_zero two non) eq]
  have pk : k<p := by omega
  have ph : h<p := by omega
  constructor
  · rintro (same|opp)
    · have m := (ZMod.natCast_eq_natCast_iff' ..).mp same
      simpa only [Nat.mod_eq_of_lt pk, Nat.mod_eq_of_lt ph] using m
    · have sum : ((k+h:ℕ):ZMod p)=0 := by push_cast; rw [opp,neg_add_cancel]
      have dv := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp sum
      have small : k+h=0 := by
        by_contra! pos
        have := Nat.le_of_dvd (by omega : 0<k+h) dv
        omega
      omega
  · rintro rfl; exact Or.inl rfl

end PrimeFactors.GeometricDoubleMatch
