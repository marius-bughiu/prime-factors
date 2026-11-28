import PrimeFactors.FiniteThreeSquareTwists
import Mathlib.Tactic.NormNum.LegendreSymbol

/-! Compare two fixed three-square twists on two small semiprime radii.
The recurrence uses known primes to verify the resulting counts. -/
namespace PrimeFactors.ThreeSquareTwistExamples

open FiniteThreeSquareTwists

/-- Specialize the classical recurrence twice. Multiplying the target
by the first prime squared preserves its sign at the second prime. -/
theorem two_primes (h : HirschhornSellers) {p q d : ℕ} (pp : p.Prime) (qp : q.Prime)
    (op : Odd p) (oq : Odd q) (ne : p≠q) (pd : ¬p∣d) (qd : ¬q∣d) :
    (r₃ (d*(p*q)^2):ℤ) = ((p:ℤ)+1-jacobiSym (-(d:ℤ)) p)*
      ((q:ℤ)+1-jacobiSym (-(d:ℤ)) q)*r₃ d := by
  have qnp : ¬q∣p := fun dv => ne ((Nat.prime_dvd_prime_iff_eq qp pp).mp dv).symm
  have qn : ¬q∣p^2*d := fun dv => (qp.dvd_mul.mp dv).elim
    (fun dv' => qnp (qp.dvd_of_dvd_pow dv')) qd
  have one := h p d pp op
  have two := h q (p^2*d) qp oq
  rw [if_neg (fun dvd => pd ((dvd_pow_self p (by decide : 2≠0)).trans dvd)),sub_zero] at one
  rw [if_neg (fun dvd => qn ((dvd_pow_self q (by decide : 2≠0)).trans dvd)),sub_zero] at two
  have cop : (p:ℤ).gcd (q:ℤ)=1 := by
    simpa only [Int.gcd_natCast_natCast] using ((Nat.coprime_primes pp qp).mpr ne)
  have sq := jacobiSym.sq_one' (a:=(p:ℤ)) (b:=q) cop
  rw [Nat.cast_mul,Nat.cast_pow,←mul_neg,jacobiSym.mul_left,sq,one_mul,one] at two
  rw [show d*(p*q)^2=q^2*(p^2*d) by ring,two]
  ring

private theorem bases : r₃ 1=6 ∧ r₃ 2=12 ∧ r₃ 3=8 := by decide +kernel

attribute [local irreducible] r₃
/-- The first two twists both give only the public base counts at 697.
At radius 65 the second twist already gives a different reading. -/
theorem compare (h : HirschhornSellers) :
    r₃ (1*65^2)=390 ∧ r₃ (2*65^2)=1260 ∧ r₃ (3*65^2)=728 ∧
    r₃ (1*697^2)=4182 ∧ r₃ (2*697^2)=8364 ∧ r₃ (3*697^2)=6536 := by
  obtain ⟨b1,b2,b3⟩ := bases
  repeat' apply And.intro
  all_goals first
    | apply Int.ofNat_inj.mp; rw [show 65=5*13 by decide, two_primes h (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]; norm_num [b1,b2,b3]
    | apply Int.ofNat_inj.mp; rw [show 697=17*41 by decide, two_primes h (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]; norm_num [b1,b2,b3]

end PrimeFactors.ThreeSquareTwistExamples
