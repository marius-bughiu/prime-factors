import PrimeFactors.MaskedRelations
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors.PolynomialRelations

/-- A root lift shifts the polynomial index. Simultaneous sign reversal produces
the same full and reduced norms at the reflected index. -/
theorem lift_reflect (A B C x j : ℤ) :
    A*x^2+2*(B+A*j)*x+(C+2*B*j+A*j^2) =
      A*(x+j)^2+2*B*(x+j)+C ∧
    A*(-x)^2+2*(-B)*(-x)+C=A*x^2+2*B*x+C := by
  constructor <;> ring

/-- The squared-root congruence uses the entire leading coefficient. -/
theorem full_row {R : Type*} [CommRing R] {A B C N : R} (abc : A*C=B^2-N) (x : R) :
    A*(A*x^2+2*B*x+C)=(A*x+B)^2-N := by
  linear_combination abc

/-- Positive magnitudes of two different negative norms. Their square dependency
has both modular roots in a window of total width less than N. Equality of the
two roots as integers is characterized by a representation of N as two squares. -/
theorem negative_window {N t s D E z : ℕ} (order : t<s)
    (first : t^2+D=N) (second : s^2+E=N) (ep : 0<E) (square : D*E=z^2) :
    t*s+z < N ∧ (t*s=z ↔ t^2+s^2=N) := by
  have npos : 0<N := by omega
  have tslt : t*s<N := by
    have : t*s≤s*s := Nat.mul_le_mul_right s order.le
    nlinarith [this]
  have npos' : (0 : ℤ)<N := by exact_mod_cast npos
  have tslt' : (t : ℤ)*s<N := by exact_mod_cast tslt
  have f : (t : ℤ)^2+D=N := by exact_mod_cast first
  have h : (s : ℤ)^2+E=N := by exact_mod_cast second
  have sq : (D : ℤ)*E=z^2 := by exact_mod_cast square
  have prod : ((N : ℤ)-(t : ℤ)*s)^2-(z : ℤ)^2=(N : ℤ)*(s-t)^2 := by
    linear_combination sq - (E : ℤ)*f - ((N : ℤ)-(t : ℤ)^2)*h
  have big : (z : ℤ) < (N : ℤ)-(t : ℤ)*s := by
    have pos : (0 : ℤ)<(s : ℤ)-t := sub_pos.mpr (by exact_mod_cast order)
    have sq_lt : (z : ℤ)^2 < ((N : ℤ)-(t : ℤ)*s)^2 := by
      have := mul_pos npos' (sq_pos_of_pos pos)
      omega
    exact lt_of_not_ge fun opposite => (not_le_of_gt sq_lt)
      (pow_le_pow_left₀ (sub_nonneg.mpr tslt'.le) opposite 2)
  have gap : ((t : ℤ)*s)^2-(z : ℤ)^2=(N : ℤ)*((t : ℤ)^2+(s : ℤ)^2-N) := by
    linear_combination sq - (E : ℤ)*f - ((N : ℤ)-(t : ℤ)^2)*h
  constructor
  · exact_mod_cast (show (t : ℤ)*s+z<N by omega)
  · constructor
    · intro same
      have equal : (t : ℤ)*s=z := by exact_mod_cast same
      rw [equal,sub_self] at gap
      have := (mul_eq_zero.mp gap.symm).resolve_left npos'.ne'
      exact_mod_cast (show (t : ℤ)^2+(s : ℤ)^2=N by omega)
    · intro rep
      have equal : (t : ℤ)^2+(s : ℤ)^2=N := by exact_mod_cast rep
      rw [equal,sub_self,mul_zero,sub_eq_zero] at gap
      exact Nat.pow_left_injective two_ne_zero (by exact_mod_cast gap)

/-- If the sum-of-two-squares exception is absent, the usual dependency gcd
splits the input, on every square-class collision below its square root. -/
theorem negative_split {N t s D E z : ℕ} [NeZero N] (order : t<s)
    (first : t^2+D=N) (second : s^2+E=N) (ep : 0<E) (square : D*E=z^2)
    (exception : t^2+s^2≠N) :
    1 < (t*s+z).gcd N ∧ (t*s+z).gcd N < N := by
  have window := negative_window order first second ep square
  have f : (t : ZMod N)^2+D=0 := by
    simpa only [Nat.cast_add, Nat.cast_pow, ZMod.natCast_self] using
      congrArg (fun k : ℕ => (k : ZMod N)) first
  have h : (s : ZMod N)^2+E=0 := by
    simpa only [Nat.cast_add, Nat.cast_pow, ZMod.natCast_self] using
      congrArg (fun k : ℕ => (k : ZMod N)) second
  have sq : (D : ZMod N)*E=z^2 := by exact_mod_cast congrArg (fun k : ℕ => (k : ZMod N)) square
  apply maskedRelations_short _ (fun e => exception (window.2.mp e)) window.1
  push_cast
  rw [mul_pow, eq_neg_of_add_eq_zero_left f, eq_neg_of_add_eq_zero_left h, neg_mul_neg, sq]

/-- Two nontrivial leading coefficients with a nontrivial common divisor
exclude the exceptional sum-of-squares case at a unit coefficient. -/
theorem shared_coefficient {N t s D E C : ℕ} (first : t^2+D=N) (second : s^2+E=N)
    (cd : C ∣ D) (ce : C ∣ E) (cop : C.Coprime N) (large : 1<C) : t^2+s^2≠N := by
  intro rep
  have e : E=t^2 := by omega
  have d : D=s^2 := by omega
  have dv : C ∣ N := rep ▸ (dvd_add (e ▸ ce) (d ▸ cd))
  have one : C = 1 := by
    rw [Nat.Coprime, Nat.gcd_eq_left dv] at cop
    exact cop
  omega

/-- For a common coefficient, it is enough to match the square classes of
the two reduced polynomial values below the square root. -/
theorem negative_coefficient_split {N A t s f h w : ℕ} [NeZero N]
    (big : 1<A) (unit : A.Coprime N) (order : t<s) (positive : 0<h)
    (first : t^2+A*f=N) (second : s^2+A*h=N) (matched : f*h=w^2) :
    1 < (t*s+A*w).gcd N ∧ (t*s+A*w).gcd N < N := by
  apply negative_split order first second (Nat.mul_pos (by omega) positive) _
    (shared_coefficient first second (dvd_mul_right ..) (dvd_mul_right ..) unit big)
  rw [mul_pow, ← matched]
  ring

/-- Two different unordered positive sum-of-two-squares representations can be
combined even if each first appeared as a trivial square dependency. -/
theorem two_representations {N a b c d : ℕ} [NeZero N] (order : a<c)
    (sortSecond : c≤d) (first : a^2+b^2=N) (second : c^2+d^2=N) :
    1 < (a*c+b*d).gcd N ∧ (a*c+b*d).gcd N < N := by
  apply negative_split order first second (by have : 0<d := lt_of_lt_of_le (Nat.zero_lt_of_lt order) sortSecond; positivity) (mul_pow b d 2).symm
  intro equal
  have smaller : a<d := lt_of_lt_of_le order sortSecond
  have strict := Nat.pow_lt_pow_left smaller (by decide : 2≠0)
  omega

/-- A selected coefficient product and reduced-value magnitude product must
have equal valuation parities at every prime, including those outside the
sieve's factor base. -/
theorem coefficient_parity {coeff values z : ℕ} (c : coeff≠0) (v : values≠0)
    (square : coeff*values=z^2) (p : ℕ) :
    coeff.factorization p % 2 = values.factorization p % 2 := by
  have h := congrArg (fun n : ℕ => n.factorization p) square
  simp only [Nat.factorization_mul c v, Nat.factorization_pow, Finsupp.add_apply,
    Finsupp.smul_apply, nsmul_eq_mul] at h
  omega

/-- The directions of different positive representations of N by x²+D y²
cannot agree even up to modular sign when D>1. -/
theorem direction_gap {N D t s a b : ℕ} (big : 1<D) (order : t<s) (bpos : 0<b)
    (left : t^2+D*a^2=N) (right : s^2+D*b^2=N) :
    t*b<s*a ∧ t*b+s*a<N := by
  have ts := Nat.pow_lt_pow_left order (by decide : 2≠0)
  have ba : b<a := by
    by_contra! bad
    have := Nat.mul_le_mul_left D (Nat.pow_le_pow_left bad 2)
    omega
  have tb := lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right order bpos) (Nat.mul_le_mul_left s ba.le)
  refine ⟨tb, ?_⟩
  have l : (t : ℤ)^2+D*a^2=N := by exact_mod_cast left
  have r : (s : ℤ)^2+D*b^2=N := by exact_mod_cast right
  have norm : (N : ℤ)^2 = (D : ℤ)*(t*b+s*a)^2+((t : ℤ)*s-D*a*b)^2 := by
    calc
      _ = ((t : ℤ)^2+D*a^2)*(s^2+D*b^2) := by rw [l,r,pow_two]
      _ = _ := by ring
  have spos : 0<(t : ℤ)*b+s*a := by
    exact_mod_cast (show 0<t*b+s*a by omega)
  have dlarge : (1 : ℤ)<D := by exact_mod_cast big
  have strict := mul_pos (sub_pos.mpr dlarge) (sq_pos_of_pos spos)
  have h : ((t : ℤ)*b+s*a)^2 < (N : ℤ)^2 := by nlinarith [sq_nonneg ((t : ℤ)*s-D*a*b)]
  exact lt_of_not_ge fun opp => (not_le_of_gt h) (by exact_mod_cast Nat.pow_le_pow_left opp 2)

/-- Modulo 77, the common coefficient 13 gives reduced values −4 and −1. -/
theorem example_77 :
    5^2+13*4=77 ∧ 8^2+13*1=77 ∧ (5*8+13*2).gcd 77=11 ∧ 7*11=77 := by decide

/-- Each displayed swapped representation is a trivial dependency, while
mixing one midpoint from each recovers the factors. -/
theorem example_221 :
    5^2+14^2=221 ∧ 10^2+11^2=221 ∧ (5*10+14*11).gcd 221=17 ∧ 13*17=221 := by decide

/-- Absolute fundamental discriminants used in the nine-field count. -/
def discriminants : List ℕ := [3,4,7,8,11,19,43,67,163]

private def smallTest (a b D : ℕ) : Bool :=
  !decide (0 < a ∧ b ≤ a ∧ 4*a^2 ≤ D+b^2 ∧ (D+b^2) % (4*a) = 0) || a == 1

private theorem reduced_table : ∀ a b : Fin 8, discriminants.all (smallTest a b) = true := by
  decide +kernel

/-- Every reduced positive form of any of the nine discriminants has leading
coefficient one. Ordinary Gauss reduction then identifies its ideal class. -/
theorem reduced_leading_one {D a b c : ℕ} (hd : D ∈ discriminants) (pos : 0<a)
    (reducedB : b≤a) (reducedC : a≤c) (disc : 4*a*c=D+b^2) : a=1 := by
  have hD : D≤163 := by
    simp only [discriminants,List.mem_cons,List.not_mem_nil,or_false] at hd
    omega
  have le := Nat.mul_le_mul_left (4*a) reducedC
  have bs := Nat.pow_le_pow_left reducedB 2
  have bound : 3*a^2≤D := by nlinarith
  have a8 : a<8 := by
    by_contra! bad
    nlinarith [Nat.pow_le_pow_left bad 2]
  have ht := List.all_eq_true.mp (reduced_table ⟨a,a8⟩ ⟨b,by omega⟩) D hd
  have cond : 0<a ∧ b≤a ∧ 4*a^2≤D+b^2 ∧ (D+b^2)%(4*a)=0 :=
    ⟨pos,reducedB,by nlinarith, Nat.mod_eq_zero_of_dvd ⟨c,disc.symm⟩⟩
  simpa [smallTest,cond] using ht

end PrimeFactors.PolynomialRelations
