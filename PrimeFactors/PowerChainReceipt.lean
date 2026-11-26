import PrimeFactors.LastPowerGCD
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.ReduceModChar

/-! Replay the final modular exponent at the public integer square root.
The divisibility chain transports a unit final gcd to every earlier index. -/

namespace PrimeFactors.PowerChainReceipt

open LastPowerGCD

/-- A reduced residue suffices to compute the gcd of the original integer power. -/
theorem reading_of_residue {n a e r : ℕ} (power : (a : ZMod n)^e = (r : ZMod n)) :
    reading n a e = Int.gcd ((r : ℤ)-1) n := by
  have eq : (a : ℤ)^e ≡ (r : ℤ) [ZMOD (n : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff ..).mp
    simpa only [Int.cast_pow, Int.cast_natCast] using power
  have divides {x y : ℤ} (h : x ≡ y [ZMOD (n : ℤ)]) : Int.gcd x n ∣ Int.gcd y n := by
    apply Int.natCast_dvd_natCast.mp
    apply Int.dvd_coe_gcd _ Int.gcd_dvd_right
    have diff := (Int.gcd_dvd_right (a := x) (b := (n : ℤ))).trans h.dvd
    simpa only [sub_add_cancel] using dvd_add diff (Int.gcd_dvd_left (a := x) (b := (n : ℤ)))
  exact Nat.dvd_antisymm (divides (eq.sub_right 1)) (divides (eq.sub_right 1).symm)

/-- Replay the actual checked gcd at the product's floor square root. -/
theorem endpoint {n a e r g : ℕ}
    (root : a^2 ≤ n ∧ n < (a+1)^2) (power : (a : ZMod n)^e = (r : ZMod n))
    (residue_gcd : Int.gcd ((r : ℤ)-1) n = g) : reading n n.sqrt e = g := by
  rw [← Nat.eq_sqrt'.mpr root]
  exact (reading_of_residue power).trans residue_gcd

/-- A terminal gcd equal to one rules out a proper gcd at every index in this chain. -/
theorem no_split_at_horizon {n first H : ℕ}
    (last : reading n n.sqrt (first * 2^H) = 1) :
    ∀ i ≤ H, reading n n.sqrt (first * 2^i) = 1 := by
  intro i ih
  exact Nat.dvd_one.mp (last ▸ divides n (n.sqrt : ℤ) (doubling first i H ih))

end PrimeFactors.PowerChainReceipt
