import PrimeFactors.Certificate
import PrimeFactors.ClassNumberWindow
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.Prime

namespace PrimeFactors.AmbiguousTwist

/-- The ramified form [l,l,c] has the public twist character of N,
since 4c=N+l. Here l is odd and prime. -/
theorem ramified_sign {l : ℕ} [Fact l.Prime] (two : (2 : ZMod l) ≠ 0)
    {c N : ℤ} (coeff : 4*c = N+l) :
    legendreSym l c = legendreSym l N := by
  have same : ((4*c : ℤ) : ZMod l) = (N : ZMod l) := by
    rw [coeff]
    simp
  have eqsym : legendreSym l (4*c) = legendreSym l N :=
    congrArg (quadraticChar (ZMod l)) same
  rw [legendreSym.mul, show (4:ℤ) = 2^2 by decide,
    legendreSym.sq_one' l (a:=2) (by simpa using two), one_mul] at eqsym
  exact eqsym

section Character
variable {G : Type*} [CommGroup G] (χ : G →* ℤ) (T : G)

/-- A nontrivial real character on the public involution lets one choose
one representative of positive sign in every pair {g,gT}. -/
def normalize (g : G) : G := if χ g = 1 then g else g*T

theorem normalize_sign (negative : χ T = -1) (g : G) : χ (normalize χ T g) = 1 := by
  have sign := Int.isUnit_iff.mp ((Group.isUnit g).map χ)
  rcases sign with pos | neg
  · simp [normalize, pos]
  · simp [normalize, neg, negative]

/-- Every coset of the public order-two subgroup has one positive
representative. In particular a class-number interval can be halved. -/
noncomputable def signEquiv (negative : χ T = -1) (square : T^2 = 1) :
    G ≃ {g : G // χ g = 1} × Bool where
  toFun g := (⟨normalize χ T g, normalize_sign χ T negative g⟩, decide (χ g ≠ 1))
  invFun z := if z.2 then z.1.1*T else z.1.1
  left_inv g := by
    by_cases pos : χ g = 1
    · simp [normalize, pos]
    · simp [normalize, pos, mul_assoc, ← sq, square]
  right_inv z := by
    obtain ⟨⟨g,hg⟩,b⟩ := z
    cases b <;> simp [normalize, hg, negative, mul_assoc, ← sq, square]

theorem twice_kernel_card [Fintype G] (negative : χ T = -1) (square : T^2 = 1) :
    Fintype.card G = 2 * Fintype.card {g : G // χ g = 1} := by
  simpa [Nat.mul_comm] using Fintype.card_congr (signEquiv χ T negative square)

/-- A nonidentity quotient involution is represented by a class x
outside {1,T} with x² in {1,T}. Its square must actually equal one. -/
theorem lift_involution (negative : χ T = -1) {x : G}
    (ord : x^2 = 1 ∨ x^2 = T) : x^2 = 1 := by
  rcases ord with trivial | bad
  · exact trivial
  · have eq := congrArg χ bad
    rw [map_pow, negative] at eq
    nlinarith [sq_nonneg (χ x)]

/-- If a second genus character is negative on the normalized class, then
any annihilator yields a usable involution. Both harmless classes are excluded. -/
theorem extract (negative : χ T = -1) (η : G →* ℤ) (g : G)
    (witness : η (normalize χ T g) = -1) {u v : ℕ} (odd : Odd u)
    (ann : normalize χ T g ^ (u*2^v) = 1) :
    ∃ j < v, let x := ((normalize χ T g)^u)^(2^j)
             x ≠ 1 ∧ x ≠ T ∧ x^2 = 1 := by
  obtain ⟨j,hj,non,square⟩ :=
    involution_of_genus_annihilator η _ witness odd ann
  refine ⟨j,hj,non,?_,square⟩
  intro eq
  have signs := congrArg χ eq
  simp [normalize_sign χ T negative, negative] at signs

end Character

/-- Determinant-one variable changes identify the opposite order of a
partition and turn a balanced boundary form into a symmetric form. -/
theorem boundary_changes (u v c : ℤ) (coeff : 4*c = u+v) (x y : ℤ) :
    u*(x+y)^2 + u*(x+y)*(-2*x-y) + c*(-2*x-y)^2 = v*x^2+v*x*y+c*y^2 ∧
    u*(-y)^2 + u*(-y)*(x+y) + c*(x+y)^2 = c*x^2+(2*c-u)*x*y+c*y^2 := by
  constructor
  · linear_combination (x^2+x*y)*coeff
  · ring

/-- A nontrivial bipartition of l*N other than l times N splits N. -/
theorem proper_gcd {l N u v : ℕ} (prime : l.Prime) (pos : 0 < N)
    (prod : u*v = l*N) (hu : u ≠ 1 ∧ u ≠ l) (hv : v ≠ 1 ∧ v ≠ l) :
    1 < Nat.gcd u N ∧ Nat.gcd u N < N := by
  have du : u ∣ l*N := ⟨v, prod.symm⟩
  have dpos := Nat.gcd_pos_of_pos_right u pos
  have dne : Nat.gcd u N ≠ 1 := by
    intro h
    have cop : u.Coprime N := h
    exact (prime.eq_one_or_self_of_dvd _ (cop.dvd_of_dvd_mul_right du)).elim hu.1 hu.2
  have le := Nat.le_of_dvd pos (Nat.gcd_dvd_right u N)
  have dneN : Nat.gcd u N ≠ N := by
    intro h
    have divides : N ∣ u := h ▸ Nat.gcd_dvd_left u N
    obtain ⟨k,rfl⟩ := divides
    have equal : N*(k*v) = N*l := by simpa [Nat.mul_assoc, Nat.mul_comm l N] using prod
    have small := Nat.eq_of_mul_eq_mul_left pos equal
    exact (prime.eq_one_or_self_of_dvd v ⟨k,by simpa [Nat.mul_comm] using small.symm⟩).elim hv.1 hv.2
  omega

/-- The lift of [5,1,107] to leading coefficient 25 has middle
coefficient -19 and lies on the symmetric boundary. -/
theorem example_713 :
    (1:ℤ)^2-4*5*107 = -3*713 ∧
    (-19:ℤ) % 10 = 1 ∧ (-19:ℤ)^2-4*25*25 = -3*713 ∧
    Nat.gcd (2*25-19) 713 = 31 ∧ Nat.gcd (2*25+19) 713 = 23 ∧
    ExactFactorization 713 [23,31] := by
  norm_num [ExactFactorization]

end PrimeFactors.AmbiguousTwist
