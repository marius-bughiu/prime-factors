import PrimeFactors.FractionalCorrectionBudget
import PrimeFactors.LocalSumMenu

/-! Every admissible modular sum is the reduction of an ordinary correction.
The existing prime-power and CRT density bound therefore gives a lower
bound on the full list, even for a modulus chosen after seeing the product. -/
namespace PrimeFactors.FractionalMenuDensity

open Finset FractionalCorrectionBudget

/-- Reduction modulo m maps the complete ordinary list onto the admissible
modular sum classes. -/
theorem modular_le {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) :
    LocalSumMenu.count (u : ZMod m).val m ≤ (menu u).card := by
  classical
  let A := (menu u).image (fun r : ℕ => (r : ZMod m))
  have e : {s : ZMod m // AdmissibleSum (u : ZMod m) s} ≃ ↥A :=
    Equiv.subtypeEquivRight (fun s => (represents u s).trans (mem_image.symm))
  unfold LocalSumMenu.count
  rw [ZMod.natCast_zmod_val, Nat.card_congr e, Nat.card_eq_finsetCard]
  exact card_image_le

/-- Uniform density bound including repeated prime factors of m. The
exponent 393 comes from the finite charge table for primes below 283. -/
theorem modulus_bound {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) :
    m^14 < 2^393*(menu u).card^16 := by
  let C := ∏ p∈m.primeFactors, LocalSumMenu.charge p
  let K := (menu u).card
  let H := LocalSumMenu.count (u : ZMod m).val m
  have cost : m^8 ≤ m*C*H^8 := LocalSumMenu.density_budget _ m (NeZero.pos m)
    (ZMod.val_coe_unit_coprime u).symm
  have cover : H≤K := modular_le u
  have positive : 0<K := card_pos.mpr ⟨_,mem_image_of_mem _ (mem_univ (1 : (ZMod m)ˣ))⟩
  have power : m^7 ≤ C*K^8 := by
    apply Nat.le_of_mul_le_mul_left _ (NeZero.pos m)
    calc m*m^7 = m^8 := by ring
         _ ≤ m*C*H^8 := cost
         _ ≤ m*(C*K^8) := by rw [←Nat.mul_assoc]; gcongr
  have finite : C^2 < 2^393 := LocalSumMenu.charge_bound_squared m
  calc m^14 = (m^7)^2 := by ring
       _ ≤ (C*K^8)^2 := Nat.pow_le_pow_left power 2
       _ = C^2*K^16 := by ring
       _ < _ := Nat.mul_lt_mul_of_pos_right finite (pow_pos positive 16)

/-- A 2048-bit input forces more than 2^942 entries in the prefix or in
the unpruned ordinary correction list, for any unit product residue. -/
theorem full_width {n m : ℕ} [NeZero m] (width : 2^2047≤n) (u : (ZMod m)ˣ) :
    2^942<n/m ∨ 2^942<(menu u).card := by
  by_contra! small
  have cap : 2^2047 ≤ m*(2^942+1) := width.trans
    ((Nat.lt_mul_div_succ n (NeZero.pos m)).le.trans (Nat.mul_le_mul_left _ (by omega)))
  have upper := (modulus_bound u).trans_le
    (Nat.mul_le_mul_left (2^393) (Nat.pow_le_pow_left small.2 16))
  have contradiction : ((2:ℕ)^2047)^14 < ((2:ℕ)^2047)^14 := calc
    _ ≤ m^14*(2^942+1)^14 := (Nat.pow_le_pow_left cap 14).trans_eq (mul_pow ..)
    _ < (2^393*(2^942)^16)*(2^942+1)^14 := Nat.mul_lt_mul_of_pos_right upper (by positivity)
    _ ≤ _ := by decide +kernel
  exact contradiction.false

/-- At or above the square root, even a known prefix count leaves more
than 2^871 entries in the full correction list on a 2048-bit input. -/
theorem near_root {n m : ℕ} [NeZero m] (width : 2^2047≤n) (root : n≤m^2) (u : (ZMod m)ˣ) :
    2^871<(menu u).card := by
  by_contra! small
  have lower : ((2:ℕ)^2047)^7 ≤ m^14 :=
    (Nat.pow_le_pow_left (width.trans root) 7).trans_eq (by ring)
  have cap := (modulus_bound u).trans_le
    (Nat.mul_le_mul_left (2^393) (Nat.pow_le_pow_left small 16))
  exact (not_le_of_gt (lower.trans_lt cap)) (by decide +kernel)

end PrimeFactors.FractionalMenuDensity
