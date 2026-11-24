import PrimeFactors.Pratt
import Mathlib.FieldTheory.Finite.Basic

namespace PrimeFactors

/-- A unit condition on every proper prime quotient keeps the full order F
after reducing the certificate modulo any prime divisor of the input. -/
theorem partial_order_dvd_predecessor {n F r : ℕ} [NeZero n] (z : ZMod n)
    (hF : 0 < F) {ps : List ℕ} (cover : Covers F ps) (full : z ^ F = 1)
    (proper : ∀ l ∈ ps, Nat.Coprime ((z ^ (F / l) - 1).val) n)
    (prime : r.Prime) (divides : r ∣ n) : F ∣ r - 1 := by
  haveI : Fact r.Prime := ⟨prime⟩
  let f := ZMod.castHom divides (ZMod r)
  have full' : (f z) ^ F = 1 := by rw [← map_pow, full, map_one]
  have nonzero : f z ≠ 0 := by
    intro zero
    rw [zero, zero_pow (by omega : F ≠ 0)] at full'
    exact zero_ne_one full'
  have order : orderOf (f z) = F := by
    apply orderOf_eq_of_pow_and_pow_div_prime hF full'
    intro l prime_l member eqn
    let u : ZMod n := z ^ (F/l) - 1
    have unit : IsUnit u := by
      rw [← ZMod.natCast_zmod_val u]
      exact (ZMod.isUnit_iff_coprime u.val n).mpr (proper l (cover l prime_l member))
    have mapped := (unit.map f).ne_zero
    apply mapped
    dsimp [u]
    rw [map_sub, map_pow, map_one, eqn, sub_self]
  exact order ▸ ZMod.orderOf_dvd_card_sub_one nonzero

/-- A partial-order primality certificate needs only a factored order whose
square is at least the input. Every prime divisor exceeds that order. -/
theorem prime_of_partial_order_cover {n F : ℕ} (z : ZMod n)
    (hn : 1 < n) (hF : 0 < F) (large : n ≤ F^2) {ps : List ℕ}
    (cover : Covers F ps) (full : z ^ F = 1)
    (proper : ∀ l ∈ ps, Nat.Coprime ((z ^ (F / l) - 1).val) n) : n.Prime := by
  haveI : NeZero n := ⟨by omega⟩
  apply Nat.prime_def_le_sqrt.mpr
  refine ⟨hn, ?_⟩
  intro m hm bound div
  obtain ⟨r, prime, rd⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
  have ord := partial_order_dvd_predecessor z hF cover full proper prime (rd.trans div)
  have flt : F < r := by
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt prime.one_lt) ord
    omega
  have rle : r ≤ m := Nat.le_of_dvd (by omega) rd
  have lower := Nat.pow_lt_pow_left (flt.trans_le rle) (show 2 ≠ 0 by decide)
  have upper := Nat.le_sqrt.mp bound
  simp only [pow_two] at lower large
  omega

end PrimeFactors
