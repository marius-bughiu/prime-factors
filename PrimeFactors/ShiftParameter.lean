import PrimeFactors.DiscriminantPencil
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.FieldSimp

namespace PrimeFactors

/-- Every shifted-square root in the balanced family lies in a product-only
interval shorter than the shift. This bound is independent of the size of k. -/
theorem shift_root_window {p q k r : ℕ} (ord : p ≤ q) (bal : q ≤ 2*p)
    (root : r^2 = (2*p+k)*(2*q+k)) :
    let m := ceilSqrt (4*(p*q))
    m+k ≤ r ∧ r ≤ m+k+k/16 := by
  let m := ceilSqrt (4*(p*q))
  have bound : 4*(p*q) ≤ m^2 := ceilSqrt_le_iff.mp le_rfl
  have key : 16*(p+q) ≤ 17*m := by
    have pos : 0 ≤ (2*(q:ℤ)-p)*(2*(p:ℤ)-q) := mul_nonneg (by omega) (by omega)
    by_contra! bad
    have ss := Nat.pow_lt_pow_left bad (by decide : 2 ≠ 0)
    zify at ss bound
    nlinarith
  have max : r ≤ p+q+k := by
    by_contra! h
    have ss := Nat.pow_lt_pow_left h (by decide : 2 ≠ 0)
    zify at ss root
    nlinarith [sq_nonneg ((p:ℤ)-q)]
  have rk : k ≤ r := by
    by_contra! h
    have ss := Nat.pow_lt_pow_left h (by decide : 2 ≠ 0)
    nlinarith only [root, ss, Nat.zero_le (p*q), Nat.zero_le (p*k), Nat.zero_le (q*k)]
  obtain ⟨z, hz⟩ := Nat.exists_eq_add_of_le rk
  have zle : z ≤ p+q := by omega
  have zm : m ≤ z := ceilSqrt_le_iff.mpr (by
    nlinarith only [root, hz ▸ root, Nat.mul_le_mul_left (2*k) zle])
  have top : 16*r ≤ 16*m+17*k := by
    by_contra! h
    have ss := Nat.pow_lt_pow_left h (by decide : 2 ≠ 0)
    nlinarith only [ss, root, bound, Nat.mul_le_mul_left (32*k) key, Nat.zero_le (k^2)]
  change m+k ≤ r ∧ _
  omega

/-- Recover a candidate from a root square by exact division. -/
def sumFromShiftRoot (n k r : ℕ) : ℕ := (r^2-4*n-k^2)/(2*k)

theorem sumFromShiftRoot_correct {p q k r : ℕ} (positive : 0 < k)
    (root : r^2 = (2*p+k)*(2*q+k)) : sumFromShiftRoot (p*q) k r = p+q := by
  have eq : r^2 = 4*(p*q) + (k^2 + 2*k*(p+q)) := by nlinarith only [root]
  simp [sumFromShiftRoot, eq, positive.ne']

/-- For a prime shift the two possible offsets in the short interval are
the residues of the signed modular roots relative to its known left endpoint. -/
theorem shift_root_offsets {p q k r : ℕ} (ord : p ≤ q) (bal : q ≤ 2*p)
    (prime : k.Prime) (root : r^2 = (2*p+k)*(2*q+k)) (z : ZMod k)
    (residue : z^2 = (4*(p*q) : ℕ)) :
    let L := ceilSqrt (4*(p*q)) + k
    r = L + (z - (L : ZMod k)).val ∨ r = L + (-z - (L : ZMod k)).val := by
  letI : Fact k.Prime := ⟨prime⟩
  let L := ceilSqrt (4*(p*q)) + k
  obtain ⟨lo,hi⟩ := shift_root_window ord bal root
  change L ≤ r at lo
  change r ≤ L+k/16 at hi
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le lo
  have small : j < k := by have := prime.pos; omega
  have phase : (r : ZMod k)^2 = z^2 := by
    rw [residue]
    have lift := congrArg (fun v : ℕ => (v : ZMod k)) root
    push_cast at lift ⊢
    simp only [ZMod.natCast_self, add_zero] at lift
    rw [lift]
    ring
  have recover (u : ZMod k) (hu : (r : ZMod k) = u) : r = L + (u-(L : ZMod k)).val := by
    rw [← hu, hj, Nat.cast_add, add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt small]
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp phase).imp (recover z) (recover (-z))

/-- For k = 3 mod 4, a modular square present in the input has an explicit
root. The hypothesis is automatic for a shifted-square solution. -/
theorem shift_modular_sqrt {k : ℕ} (prime : k.Prime) (three : k%4=3)
    {v : ZMod k} (square : IsSquare v) : (v^((k+1)/4))^2 = v := by
  letI : Fact k.Prime := ⟨prime⟩
  obtain ⟨u, rfl⟩ := square
  have expo : 4*((k+1)/4) = k+1 := by omega
  calc
    ((u*u)^((k+1)/4))^2 = u^(4*((k+1)/4)) := by
      rw [← sq u, ← pow_mul, ← pow_mul]
      congr 1
      ring
    _ = u^(k+1) := by rw [expo]
    _ = u*u := by rw [pow_succ, ZMod.pow_card]

/-- Two integer roots to test for a shift prime congruent to 3 modulo 4. -/
noncomputable def primeShiftRoots (n k : ℕ) [NeZero k] : ℕ × ℕ :=
  let l := ceilSqrt (4*n) + k
  let z := ((4*n : ℕ) : ZMod k)^((k+1)/4)
  (l + (z-(l:ZMod k)).val, l + (-z-(l:ZMod k)).val)

theorem primeShiftRoots_complete {p q k r : ℕ} (ord : p ≤ q) (bal : q ≤ 2*p)
    (prime : k.Prime) (three : k%4=3) [NeZero k] (root : r^2 = (2*p+k)*(2*q+k)) :
    r = (primeShiftRoots (p*q) k).1 ∨ r = (primeShiftRoots (p*q) k).2 := by
  have sq : IsSquare ((4*(p*q) : ℕ) : ZMod k) := by
    refine ⟨(r : ZMod k), ?_⟩
    have lift := congrArg (fun v : ℕ => (v : ZMod k)) root
    push_cast at lift ⊢
    simp only [ZMod.natCast_self, add_zero] at lift
    rw [← sq, lift]
    ring
  exact shift_root_offsets ord bal prime root _ (shift_modular_sqrt prime three sq)

theorem primeShiftRoots_96113 :
    (primeShiftRoots 96113 10163).2 = 10815 ∧
      sumFromShiftRoot 96113 10163 10815 = 654 ∧ 96113 = 223*431 ∧
      Nat.Prime 223 ∧ Nat.Prime 431 ∧ Nat.Prime 10163 := by
  refine ⟨?_, by decide, by decide, by norm_num, by norm_num, by norm_num⟩
  have z : (((4*96113 : ℕ) : ZMod 10163)^((10163+1)/4 : ℕ)) = (9511:ℕ) := by
    rw [← Nat.cast_pow]
    apply (ZMod.natCast_eq_natCast_iff ..).mpr
    change (4 * 96113)^((10163+1)/4 : ℕ) % 10163 = 9511 % 10163
    norm_num
  have m : ceilSqrt (4*96113) = 621 := le_antisymm (ceilSqrt_le_iff.mpr (by decide)) (by
    by_contra! small
    have h := ceilSqrt_le_iff.mp (show ceilSqrt (4*96113) ≤ 620 by omega)
    exact (by decide : ¬ 4*96113 ≤ 620^2) h)
  simp only [primeShiftRoots, z, m]
  decide

/-- Parameterizing all symmetric shifts by a divisor pair of the squared
factor gap. This includes large shifts outside a short-gap search. -/
theorem shift_gap_identity (p q k r : ℤ) :
    r^2 = (2*p+k)*(2*q+k) ↔ (p+q+k-r)*(p+q+k+r) = (q-p)^2 := by
  constructor <;> intro h <;> nlinarith only [h]

/-- If p = h-g and q = h+g, the shift g²+1-2h always makes the norm a
square. It is positive once g²+1 exceeds 2h, but depends on the unknown sum. -/
theorem shift_from_gap (h g : ℤ) :
    let k := g^2+1-2*h
    (2*(h-g)+k)*(2*(h+g)+k) = (g^2-1)^2 := by dsimp; ring

/-- A value of the shifted first factor congruent to ℓ modulo ℓ²
and the displayed product-only condition force an odd valuation. Signed
integer coefficients allow rational shifts with cleared denominators. -/
theorem shift_local_obstruction {ℓ : ℕ} (prime : ℓ.Prime) {A B p q : ℤ}
    (first : 2*B*p+A ≡ (ℓ:ℤ) [ZMOD (ℓ:ℤ)^2])
    (other : ¬(ℓ:ℤ) ∣ A^2 - 4*B^2*(p*q)) :
    ¬ IsSquare ((2*B*p+A)*(2*B*q+A)) := by
  obtain ⟨z,hz⟩ := first.dvd
  let u := 1-(ℓ:ℤ)*z
  let v := 2*B*q+A
  have eq : 2*B*p+A = (ℓ:ℤ)*u := by dsimp [u]; linarith
  have ellP : Prime (ℓ:ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa)
  rintro ⟨r,square⟩
  have er : (ℓ:ℤ) ∣ r*r := square ▸ ⟨u*v, by rw [eq]; ring⟩
  obtain ⟨t,ht⟩ := (ellP.dvd_mul.mp er).elim id id
  have cancelled : u*v = (ℓ:ℤ)*t^2 := by
    apply mul_left_cancel₀ ellP.ne_zero
    calc
      (ℓ:ℤ)*(u*v) = (2*B*p+A)*v := by rw [eq]; ring
      _ = r*r := square
      _ = (ℓ:ℤ)*((ℓ:ℤ)*t^2) := by rw [ht]; ring
  have vd : v = (ℓ:ℤ)*(t^2+z*v) := by dsimp [u] at cancelled; linarith
  apply other
  refine ⟨A*u-2*B*p*(t^2+z*v), ?_⟩
  calc
    A^2-4*B^2*(p*q) = A*(2*B*p+A) - 2*B*p*v := by dsimp [v]; ring
    _ = _ := by nth_rw 1 [eq, vd]; ring

end PrimeFactors
