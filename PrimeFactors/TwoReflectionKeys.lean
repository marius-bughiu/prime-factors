import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-! A universal lookup key on powers `g^x` is a periodic function of the
integer exponent. Inversion reflects `x` to `-x`; a second reflection centered
at `g^r` sends it to `2r-x`. Both identities are assumed on every exponent.
A key built for a particular finite set of stored points need not obey them. -/
namespace PrimeFactors.TwoReflectionKeys

variable {α : Type*} {K : ℤ → α} {r d : ℤ}

/-- The composition of the two reflections rotates by twice the center. -/
theorem rotation (neg : ∀ x, K (-x) = K x) (reflect : ∀ x, K (2*r-x) = K x) :
    Function.Periodic K (2*r) := by
  intro x
  calc K (x+2*r) = K (2*r-(-x)) := by congr 1; ring
       _ = K (-x) := reflect _
       _ = K x := neg _

/-- Any period `d` for the query, together with the rotations, forces a gcd period. -/
theorem common_period (period : Function.Periodic K d)
    (neg : ∀ x, K (-x) = K x) (reflect : ∀ x, K (2*r-x) = K x) :
    Function.Periodic K (Int.gcd d (2*r) : ℤ) := by
  rw [Int.gcd_eq_gcd_ab]
  simpa only [Int.cast_id, mul_comm (Int.gcdA d (2*r)), mul_comm (Int.gcdB d (2*r))] using
    (period.int_mul (Int.gcdA d (2*r))).add_period ((rotation neg reflect).int_mul (Int.gcdB d (2*r)))

/-- Every key is represented between zero and half the gcd period, inclusive. -/
theorem representative (hd : d ≠ 0) (period : Function.Periodic K d)
    (neg : ∀ x, K (-x) = K x) (reflect : ∀ x, K (2*r-x) = K x) (x : ℤ) :
    ∃ j : ℕ, j ≤ Int.gcd d (2*r)/2 ∧ K x = K (j : ℤ) := by
  let G := Int.gcd d (2*r)
  have hG : 0 < (G : ℤ) := by exact_mod_cast Int.gcd_pos_of_ne_zero_left (2*r) hd
  have P : Function.Periodic K (G : ℤ) := common_period period neg reflect
  let b := x % (G : ℤ)
  have hb := Int.emod_nonneg x hG.ne'
  have ltG := Int.emod_lt_of_pos x hG
  have hx : K x = K b := by
    have h := (P.int_mul (x/(G : ℤ))) b
    simpa only [Int.cast_id, mul_comm (x/(G : ℤ)), b, Int.emod_add_ediv] using h
  change 0 ≤ b at hb
  change b < (G : ℤ) at ltG
  by_cases half : 2*b ≤ G
  · refine ⟨b.toNat, ?_, hx.trans ?_⟩
    · change b.toNat ≤ G/2
      omega
    · rw [Int.toNat_of_nonneg hb]
  · refine ⟨((G : ℤ)-b).toNat, ?_, hx.trans ?_⟩
    · change ((G : ℤ)-b).toNat ≤ G/2
      omega
    · rw [Int.toNat_of_nonneg (by omega : 0 ≤ (G : ℤ)-b)]
      calc K b = K (-b) := (neg _).symm
           _ = K (-b+G) := (P _).symm
           _ = K (G-b) := by congr 1; ring

/-- Cardinal bound for any finite collection of queried exponent indices. -/
theorem card_image_le [DecidableEq α] (hd : d ≠ 0) (period : Function.Periodic K d)
    (neg : ∀ x, K (-x) = K x) (reflect : ∀ x, K (2*r-x) = K x) (indices : Finset ℤ) :
    (indices.image K).card ≤ Int.gcd d (2*r)/2+1 := by
  let J := Finset.range (Int.gcd d (2*r)/2+1)
  have sub : indices.image K ⊆ J.image (fun j : ℕ => K (j : ℤ)) := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j, le, eq⟩ := representative hd period neg reflect x
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), eq.symm⟩
  exact (Finset.card_le_card sub).trans ((Finset.card_image_le).trans (by simp [J]))

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Modulo 17 take u=9, v=3. The target 5 shares a universal key with 3,
yet does not equal any of the four actual products u^(±1) v^(±1). -/
theorem false_match_17 (key : ZMod 17 → α)
    (inv : ∀ x : ZMod 17, x ≠ 0 → key x⁻¹ = key x)
    (reflect : ∀ x : ZMod 17, x ≠ 0 → key (9*x⁻¹) = key x) :
    key 5 = key 3 ∧
      ∀ x ∈ ({(9:ZMod 17), 9⁻¹} : Finset (ZMod 17)),
      ∀ y ∈ ({(3:ZMod 17), 3⁻¹} : Finset (ZMod 17)), x*y ≠ 5 := by
  have turn (x : ZMod 17) (nonzero : x ≠ 0) : key (9*x) = key x := by
    calc key (9*x) = key (9*(x⁻¹)⁻¹) := by rw [inv_inv]
         _ = key x⁻¹ := reflect _ (inv_ne_zero nonzero)
         _ = key x := inv _ nonzero
  constructor
  · calc key 5 = key (9*(9*3)) := congrArg key (by decide +kernel)
         _ = key (9*3) := turn _ (by decide +kernel)
         _ = key 3 := turn _ (by decide +kernel)
  · have a : (9 : ZMod 17)⁻¹ = 2 := inv_eq_of_mul_eq_one_right (by decide +kernel : (9 : ZMod 17)*2=1)
    have b : (3 : ZMod 17)⁻¹ = 6 := inv_eq_of_mul_eq_one_right (by decide +kernel : (3 : ZMod 17)*6=1)
    rw [a,b]
    decide +kernel

end PrimeFactors.TwoReflectionKeys
