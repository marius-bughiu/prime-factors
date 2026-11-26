import PrimeFactors.StationaryRadixLimit
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction

/-! The finite number of slopes available to primitive integer points of
square norm. The modulus is a *square*, so any square root of a squarefree
integer has to be a unit. This allows translation to the previously counted
square roots of one, including at the prime two. -/

namespace PrimeFactors.WeightedMultiplierRoots
open Finset StationaryRadixLimit

/-- A common prime of the root and the modulus would have its square
dividing the squarefree target. -/
theorem slope_coprime {a t s : ℕ} (free : Squarefree t) (root : a^2 ≡ t [MOD s^2]) :
    a.Coprime (s^2) := by
  apply Nat.coprime_of_dvd
  intro p hp ha hs
  have ps := hp.dvd_of_dvd_pow hs
  have pt := (root.dvd_iff (pow_dvd_pow_of_dvd ps 2)).mp (pow_dvd_pow_of_dvd ha 2)
  exact Nat.squarefree_iff_prime_squarefree.mp free p hp (by simpa [sq] using pt)

/-- Every possible slope is counted, including a modulus of one and an empty
root set. Translation by one chosen root maps all other roots injectively to
the 2-torsion in the unit group. -/
theorem slope_count {s t : ℕ} (pos : 0<s) (free : Squarefree t) :
    ((range (s^2)).filter fun a => a^2 ≡ t [MOD s^2]).card ≤ 2^(s.primeFactors.card+1) := by
  classical
  haveI : NeZero (s^2) := ⟨pow_ne_zero _ pos.ne'⟩
  let S := (range (s^2)).filter fun a => a^2 ≡ t [MOD s^2]
  change S.card ≤ _
  by_cases nonempty : S.Nonempty
  · obtain ⟨a,ha⟩ := nonempty
    have valid {v : ℕ} (hv : v∈S) := mem_filter.mp hv
    let unit (v : S) := ZMod.unitOfCoprime v.val (slope_coprime free (valid v.property).2)
    have same (v : S) : (unit v)^2=(unit ⟨a,ha⟩)^2 := by
      apply Units.ext
      change (v.val:ZMod (s^2))^2=(a:ZMod (s^2))^2
      exact_mod_cast (ZMod.eq_iff_modEq_nat _).2 ((valid v.property).2.trans (valid ha).2.symm)
    let f (v : S) : Roots (s^2) := ⟨unit v / unit ⟨a,ha⟩, by rw [div_pow,same]; simp⟩
    have inj : Function.Injective f := by
      intro v w eq
      have h : unit v / unit ⟨a,ha⟩=unit w / unit ⟨a,ha⟩ := congrArg Subtype.val eq
      have u : unit v=unit w := by
        simpa using congrArg (fun z => z * unit ⟨a,ha⟩) h
      have c : (v.val:ZMod (s^2))=w.val := congrArg Units.val u
      exact Subtype.ext (((ZMod.natCast_eq_natCast_iff ..).mp c).eq_of_lt_of_lt
        (mem_range.mp (valid v.property).1) (mem_range.mp (valid w.property).1))
    have amount := (Nat.card_le_card_of_injective f inj).trans (roots_le (pow_pos pos 2))
    simpa [Nat.card_eq_fintype_card,Nat.primeFactors_pow _ (by decide : 2≠0)] using amount
  · rw [not_nonempty_iff_eq_empty.mp nonempty,card_empty]
    exact Nat.zero_le _

open ArithmeticFunction

/-- The total number of choices of one of two signs at each prime of each
divisor is exactly the divisor count of the square of the original integer. -/
theorem divisor_classes (c : ℕ) :
    ∑ s ∈ c.divisors, 2^s.primeFactors.card = (c^2).divisors.card := by
  let f := ArithmeticFunction.prodPrimeFactors (fun _ => (2:ℕ))
  have value {s : ℕ} (pos : s≠0) : f s=2^s.primeFactors.card := by
    simp [f,prodPrimeFactors_apply pos]
  have mult := (IsMultiplicative.prodPrimeFactors (fun _ => (2:ℕ))).mul isMultiplicative_zeta
  change IsMultiplicative (f * ζ) at mult
  have count (n : ℕ) : (f * ζ) n=(n^2).divisors.card := by
    induction n using Nat.recOnPosPrimePosCoprime with
    | h0 => simp
    | h1 => simp [mult.1]
    | hp p k hp hk =>
      rw [mul_zeta_apply,Nat.sum_divisors_prime_pow hp,sum_range_succ',←pow_mul,
        Nat.divisors_prime_pow hp]
      have one (i : ℕ) : f (p^(i+1))=2 := by
        rw [value (pow_ne_zero _ hp.ne_zero),Nat.primeFactors_prime_pow (by omega) hp]
        simp
      simp [one,value, mul_two]
    | h a b _ _ cop ihA ihB =>
      rw [mult.map_mul_of_coprime cop,ihA,ihB,mul_pow,
        (cop.pow_left 2 |>.pow_right 2).card_divisors_mul]
  rw [← count c,mul_zeta_apply]
  exact sum_congr rfl fun s hs => (value (Nat.pos_of_mem_divisors hs).ne').symm

end PrimeFactors.WeightedMultiplierRoots
