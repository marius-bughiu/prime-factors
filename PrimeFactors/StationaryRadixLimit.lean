import PrimeFactors.PrimitiveNorm
import PrimeFactors.ConditionalStride
import PrimeFactors.MidpointWeightBudget
import PrimeFactors.AffineSlopeClasses
import Mathlib.Data.Nat.Factorization.Induction

namespace PrimeFactors.StationaryRadixLimit

open Finset

/-- Unit square roots of one, including the full dyadic component. -/
abbrev Roots (R : ℕ) := {u : (ZMod R)ˣ // u^2 = 1}

private theorem roots_product {A B : ℕ} [NeZero A] [NeZero B] (cop : A.Coprime B) :
    Nat.card (Roots (A*B)) ≤ Nat.card (Roots A) * Nat.card (Roots B) := by
  let e := (Units.mapEquiv (ZMod.chineseRemainder cop).toMulEquiv).trans MulEquiv.prodUnits
  let f (u : Roots (A*B)) : Roots A × Roots B := by
    have hu : (e u.val)^2 = 1 := by rw [← map_pow, u.property, map_one]
    exact (⟨(e u.val).1, congrArg Prod.fst hu⟩, ⟨(e u.val).2, congrArg Prod.snd hu⟩)
  have hinj : Function.Injective f := by
    intro u v same
    apply Subtype.ext
    apply e.injective
    apply Prod.ext
    · exact congrArg (fun z : Roots A × Roots B => z.1.val) same
    · exact congrArg (fun z : Roots A × Roots B => z.2.val) same
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective f hinj

private theorem roots_odd_prime_power {p e : ℕ} (hp : p.Prime) (odd : p ≠ 2) :
    Nat.card (Roots (p^(e+1))) ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let f (x : Roots (p^(e+1))) : {r : ZMod (p^(e+1)) // r^2 = ((1:ℤ) : ZMod (p^(e+1)))} :=
    ⟨x.val, by simpa using congrArg (fun u : (ZMod (p^(e+1)))ˣ => (u : ZMod (p^(e+1)))) x.property⟩
  have count := Nat.card_le_card_of_injective f
    (fun _ _ h => Subtype.ext (Units.ext (congrArg Subtype.val h)))
  have small := primitiveNorm_odd_root_count odd 1 (by simp) e
  exact count.trans (by rw [small]; simp)

private theorem roots_two (e : ℕ) : Nat.card (Roots (2^e)) ≤ 4 := by
  classical
  simpa [Roots, Nat.card_eq_fintype_card, Fintype.card_subtype, strideUnitRoots] using
    strideUnitRoots_two_pow_le_four e 1

theorem roots_factor_bound {R : ℕ} (pos : 0 < R) :
    Nat.card (Roots R) ≤ ∏ p ∈ R.primeFactors, (if p = 2 then 4 else 2) := by
  revert pos
  induction R using Nat.recOnPosPrimePosCoprime with
  | hp p k prime hk =>
    intro _
    rw [Nat.primeFactors_prime_pow hk.ne' prime, Finset.prod_singleton]
    by_cases two : p = 2
    · subst p; simpa using roots_two k
    · obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      simpa [two] using roots_odd_prime_power (e := e) prime two
  | h0 => omega
  | h1 =>
    intro _
    have : Nat.card (Roots 1) ≤ 1 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    simpa using this
  | h a b ha hb cop ihA ihB =>
    intro _
    rw [cop.primeFactors_mul, Finset.prod_union ((Nat.disjoint_primeFactors (by omega) (by omega)).mpr cop)]
    haveI : NeZero a := ⟨by omega⟩
    haveI : NeZero b := ⟨by omega⟩
    exact (roots_product cop).trans (Nat.mul_le_mul (ihA (by omega)) (ihB (by omega)))

theorem roots_le {R : ℕ} (pos : 0 < R) :
    Nat.card (Roots R) ≤ 2^(R.primeFactors.card+1) := by
  apply (roots_factor_bound pos).trans
  have bound (s : Finset ℕ) : (∏ p ∈ s, (if p = 2 then 4 else 2)) =
      2^s.card * (if 2 ∈ s then 2 else 1) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [prod_insert ha, card_insert_of_not_mem ha, ih, pow_succ]
      by_cases h : a = 2
      · subst a; simp [ha]; ring
      · simp [h, Ne.symm h]; ring
  rw [bound, pow_succ]
  split_ifs <;> omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem primorial_467 :
    (quotientBudgetPrimes 467).card = 91 ∧ 2^648 < quotientBudgetWheel 467 := by
  change ((range 468).filter Nat.Prime).card = 91 ∧ 2^648 < ∏ p ∈ (range 468).filter Nat.Prime, p
  decide +kernel

/-- A modulus small enough to threaten the adaptive width lower bound has
at most 90 distinct prime factors, hence at most 2^91 square roots of unity. -/
theorem small_radix_torsion {R : ℕ} (pos : 0 < R) (hr : R ≤ 2^648) :
    Nat.card (Roots R) ≤ 2^91 := by
  obtain ⟨count, product⟩ := primorial_467
  have card := quotientBudget_primeFactors_below pos (by decide : 1 ≤ 467) (hr.trans_lt product)
  apply (roots_le pos).trans
  exact Nat.pow_le_pow_right (by decide) (by omega)

end PrimeFactors.StationaryRadixLimit
