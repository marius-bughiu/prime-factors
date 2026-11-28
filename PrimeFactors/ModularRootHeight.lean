import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic

/-! How small can an ordinary representative of a modular square root be?
For a nonnegative nonsquare D, once the modulus exceeds D every representative
has square at least D plus the modulus. -/

namespace PrimeFactors.ModularRootHeight

/-- The congruence has a gap between the integer square and every other possibility. -/
theorem gap {D M x : ℕ} (large : D<M) (root : x^2 ≡ D [MOD M]) :
    x^2=D ∨ D+M≤x^2 := by
  have residue : x^2%M=D := (show x^2%M=D%M from root).trans (Nat.mod_eq_of_lt large)
  have division := Nat.div_add_mod (x^2) M
  rw [residue] at division
  by_cases zero : x^2/M=0
  · left
    simpa [zero] using division.symm
  · right
    have step := Nat.mul_le_mul_left M (Nat.one_le_iff_ne_zero.mpr zero)
    rw [Nat.mul_one] at step
    omega

/-- The bound holds for the magnitude of every signed integer representative. -/
theorem escapes {D M : ℕ} (large : D<M) (falseSquare : ¬IsSquare D) (x : ℤ)
    (root : (x:ZMod M)^2=(D:ZMod M)) : D+M≤x.natAbs^2 := by
  have square : ((x.natAbs^2:ℕ):ZMod M)=(D:ZMod M) := by
    have identity := congrArg (fun z : ℤ => (z:ZMod M)) (Int.natAbs_sq x)
    simp only [Int.cast_pow,Int.cast_natCast,Nat.cast_pow] at identity ⊢
    exact identity.trans root
  refine (gap large ((ZMod.natCast_eq_natCast_iff _ _ _).mp square)).resolve_left ?_
  intro eq
  exact falseSquare ⟨x.natAbs,by simpa [pow_two] using eq.symm⟩

/-- One root below this square-height threshold recognizes a genuine square. -/
theorem iff_short {D M : ℕ} (large : D<M) : IsSquare D ↔
    ∃ x : ℤ, (x:ZMod M)^2=(D:ZMod M) ∧ x.natAbs^2<D+M := by
  constructor
  · rintro ⟨a,ha⟩
    have sq : a^2=D := by simpa only [pow_two] using ha.symm
    refine ⟨a,?_,?_⟩
    · simpa only [Int.cast_natCast,Nat.cast_pow] using congrArg (fun n : ℕ => (n:ZMod M)) sq
    · simpa only [Int.natAbs_natCast,sq] using (show D<D+M by omega)
  · rintro ⟨x,root,short⟩
    exact of_not_not (fun bad => (not_le_of_gt short) (escapes large bad x root))

/-- A false midpoint may have roots at every modular precision. If M is
larger than both N and the discriminant, no representative can be the half-gap
of two nonnegative integers with ordinary midpoint h. -/
theorem outside_midpoint {N h M : ℕ} (above : N≤h^2) (large : h^2-N<M) (wide : N<M)
    (falseSquare : ¬IsSquare (h^2-N)) (x : ℤ) (root : (x:ZMod M)^2=((h^2-N:ℕ):ZMod M)) :
    h<x.natAbs := by
  have big := escapes large falseSquare x root
  apply lt_of_not_ge
  intro small
  have upper := Nat.pow_le_pow_left small 2
  omega

/-- Powers of two attain the gap. Here 257=1 mod 8 and 129²−257=2^14. -/
theorem sharp_example :
    ¬IsSquare (257:ℕ) ∧ 257<(2^14:ℕ) ∧ (129:ZMod (2^14))^2=257 ∧ (129:ℕ)^2=257+2^14 := by
  refine ⟨?_,by decide,by decide +kernel,by decide⟩
  rintro ⟨k,eq⟩
  by_cases h : k≤16 <;> nlinarith

/-- A wrong sum from the 28-bit fixture still has a joint modular root after
the product of the first ten primes has exceeded the input. Every ordinary
representative of any such root is too large to be a nonnegative half-gap. -/
theorem ten_prime_example :
    (2*3*5*7*11*13*17*19*23*29:ℕ)=6469693230 ∧
    (3593537:ZMod 6469693230)^2=483289 ∧
    ∀ x : ℤ, (x:ZMod 6469693230)^2=483289 → 12090<x.natAbs := by
  refine ⟨by decide,by decide +kernel,?_⟩
  intro x root
  have nonsquare : ¬IsSquare (483289:ℕ) := by
    rintro ⟨k,eq⟩
    by_cases h : k≤695 <;> nlinarith
  exact outside_midpoint (N:=145684811) (h:=12090) (M:=6469693230)
    (by decide) (by decide) (by decide) nonsquare x root

end PrimeFactors.ModularRootHeight
