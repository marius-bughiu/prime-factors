import PrimeFactors.SmallJacobiNonresidue
import PrimeFactors.LeastPrimeBoundInterface
import PrimeFactors.EvenPrimeThreeSquareBase
import PrimeFactors.AdaptiveThreeSquareTwist

/-! A product-dependent choice of a small positive twist. The sign of each
candidate is a Jacobi symbol at the public product. The large three-square
representation count remains a separate input. -/
namespace PrimeFactors.BoundedThreeSquareTwist

open FiniteThreeSquareTwists LeastPrimeBoundInterface

/-- A positive base count and a mixed local sign are exactly the data
used to select a twist before requesting its large representation count. -/
def Useful (n d : ℕ) : Prop := 0<d ∧ 0<r₃ d ∧ jacobiSym (-(d:ℤ)) n= -1

/-- With a negative-symbol prime available, two Jacobi tests at the
public modulus determine which target to use. -/
noncomputable def choose (n l : ℕ) : ℕ :=
  if jacobiSym (-1) n= -1 then 1 else if jacobiSym (-2) n= -1 then 2 else 2*l

attribute [local irreducible] r₃

private theorem base_counts : 0<r₃ 1 ∧ 0<r₃ 2 ∧ 0<r₃ 4 := by
  unfold r₃
  decide +kernel

/-- A prime with negative Jacobi symbol is sufficient. If the first two
base twists fail, doubling this prime keeps the negative sign and ensures
the three-square representability condition for the base target. -/
theorem from_prime {n l : ℕ} (odd : Odd n) (prime : l.Prime)
    (sign : jacobiSym l n= -1) (represented : l≠2 → 0<r₃ (2*l)) :
    choose n l≤2*l ∧ Useful n (choose n l) := by
  obtain ⟨one,two,four⟩ := base_counts
  have pos := prime.two_le
  by_cases first : jacobiSym (-1) n= -1
  · rw [choose,if_pos first]
    exact ⟨by omega,by simpa [Useful] using And.intro one first⟩
  by_cases second : jacobiSym (-2) n= -1
  · rw [choose,if_neg first,if_pos second]
    exact ⟨by omega,by simpa [Useful] using And.intro two second⟩
  have cop : (-2:ℤ).gcd (n:ℤ)=1 := by
    simpa only [Int.gcd,Int.natAbs_neg,Int.natAbs_natCast] using
      Nat.coprime_two_left.mpr odd
  have positive := (jacobiSym.eq_one_or_neg_one cop).resolve_right second
  have base : 0<r₃ (2*l) := by
    by_cases eq : l=2
    · simpa [eq] using four
    · exact represented eq
  rw [choose,if_neg first,if_neg second]
  refine ⟨le_rfl,Nat.mul_pos (by decide) prime.pos,base,?_⟩
  rw [Nat.cast_mul,Nat.cast_ofNat,←neg_mul,jacobiSym.mul_left,positive,sign,one_mul]

/-- Conditional on the small outside-prime bound and the classical
representability of twice every odd prime up to that bound. -/
theorem bounded {p q M : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (op : p≠2) (oq : q≠2) (small : SmallPrimeOutside (p*q) M)
    (base : ∀ l≤M, l.Prime → l≠2 → 0<r₃ (2*l)) :
    ∃ d≤2*M, Useful (p*q) d := by
  obtain ⟨l,lim,prime,_,sign⟩ := SmallJacobiNonresidue.exists_prime pp qp ne oq small
  obtain ⟨cap,good⟩ := from_prime ((pp.odd_of_ne_two op).mul (qp.odd_of_ne_two oq)) prime
    sign (base l lim prime)
  exact ⟨choose (p*q) l,cap.trans (Nat.mul_le_mul_left 2 lim),good⟩

/-- The full-size statement with the three classical inputs exposed. The
large count in the conclusion is a cardinality, with no evaluation bound. -/
theorem full_size {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (width : p*q<2^2048)
    (least : 3000≤p*q → (∀ r : ℕ, r.Prime → r∣p*q → Real.log (p*q:ℕ)^2≤(r:ℝ)) →
      RealOutside (p*q) (Real.log (p*q:ℕ)^2))
    (three : EvenPrimeThreeSquareBase.ThreeSquares) (recurrence : HirschhornSellers) :
    ∃ d≤4030330, Useful (p*q) d ∧
      let v := (r₃ (d*(p*q)^2)/r₃ d-p*q)/2
      (v=p ∨ v=q) ∧ jacobiSym (-(d:ℤ)) v=1 := by
  have lower : 3≤2^1023 := by decide +kernel
  have op : p≠2 := by omega
  have oq : q≠2 := by omega
  have small := LeastPrimeBoundInterface.full_size pp qp pl ql width least
  obtain ⟨d,cap,good⟩ := bounded pp qp ne op oq small (fun l lim prime odd =>
    EvenPrimeThreeSquareBase.bounded three 2015165 l prime (prime.odd_of_ne_two odd) lim)
  refine ⟨d,cap,good,?_⟩
  exact AdaptiveThreeSquareTwist.reading recurrence pp qp (pp.odd_of_ne_two op)
    (qp.odd_of_ne_two oq) ne good.2.2 good.2.1

/-- On 697 the old twists one and two both repeat their base count
times 697. The public sign choice gives ten, whose count selects 41. -/
theorem controls (recurrence : HirschhornSellers) :
    choose 65 3=6 ∧ r₃ (6*65^2)=1800 ∧
    choose 697 5=10 ∧ r₃ 10=24 ∧ r₃ (10*697^2)=18696 := by
  have base6 : r₃ 6=24 := EvenPrimeThreeSquareBase.controls.1
  have base10 : r₃ 10=24 := by unfold r₃; decide +kernel
  have small := ThreeSquareTwistExamples.two_primes (p:=5) (q:=13) (d:=6) recurrence
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have larger := ThreeSquareTwistExamples.two_primes (p:=17) (q:=41) (d:=10) recurrence
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  norm_num [base6,base10] at small larger
  refine ⟨by norm_num [choose],?_,by norm_num [choose],base10,?_⟩
  · norm_num
    exact_mod_cast small
  · norm_num
    exact_mod_cast larger

end PrimeFactors.BoundedThreeSquareTwist
