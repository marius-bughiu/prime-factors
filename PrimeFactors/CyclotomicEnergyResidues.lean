import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! For a fixed modulus, consider all pairs of units with an observed product
residue. Determine when the product alone specifies whether the two factors
are equal or opposite, and which product residues allow both answers. -/
namespace PrimeFactors.CyclotomicEnergyResidues

/-- One predicate on product residues decides whether the unit factors are equal or opposite. -/
def ProductOnly (m : ℕ) : Prop := ∃ bit : (ZMod m)ˣ → Prop,
  ∀ a b, bit (a*b) ↔ a=b ∨ a= -b

def SignedSquares (m : ℕ) : Prop := ∀ a : (ZMod m)ˣ, a^2=1 ∨ a^2= -1

private theorem signed_iff_right_square {m : ℕ} (a b : (ZMod m)ˣ) :
    (a=b ∨ a= -b) ↔ (a*b=b^2 ∨ a*b= -(b^2)) := by
  simp only [sq,←neg_mul,mul_left_inj]

/-- For these moduli the public rule tests whether the product is ±1. -/
theorem product_rule {m : ℕ} (h : SignedSquares m) (a b : (ZMod m)ˣ) :
    (a=b ∨ a= -b) ↔ (a*b=1 ∨ a*b= -1) := by
  rcases h b with s|s <;> simpa [s,or_comm] using signed_iff_right_square a b

theorem productOnly_iff (m : ℕ) : ProductOnly m ↔ SignedSquares m := by
  constructor
  · rintro ⟨bit,h⟩ a
    have yes := (h a a).mpr (Or.inl rfl)
    have transfer := (h (a^2) 1).mp (by simpa [sq] using yes)
    exact transfer
  · exact fun h => ⟨fun n => n=1 ∨ n= -1, fun a b => (product_rule h a b).symm⟩

theorem descends {m d : ℕ} [NeZero m] (hd : d∣m) (h : SignedSquares m) : SignedSquares d := by
  intro b
  obtain ⟨u,rfl⟩ := ZMod.unitsMap_surjective hd b
  rcases h u with c|c
  · left
    simpa only [map_pow,map_one] using congrArg (ZMod.unitsMap hd) c
  · right
    apply Units.ext
    have base := congrArg (fun v : (ZMod m)ˣ => ZMod.castHom hd (ZMod d) v.val) c
    simpa only [ZMod.unitsMap_def,Units.val_pow_eq_pow_val,Units.coe_map,MonoidHom.coe_coe,Units.val_neg,
      Units.val_one,map_pow,map_neg,map_one] using base

private theorem odd_part {d : ℕ} (h : SignedSquares d) (odd : Odd d) : d∣3 ∨ d∣5 := by
  let u := ZMod.unitOfCoprime 2 odd.coprime_two_left
  rcases h u with c|c
  · left
    have val := congrArg Units.val c
    change (u:ZMod d)^2=1 at val
    rw [ZMod.coe_unitOfCoprime] at val
    apply (ZMod.natCast_zmod_eq_zero_iff_dvd 3 d).mp
    push_cast at val ⊢
    linear_combination val
  · right
    have val := congrArg Units.val c
    change (u:ZMod d)^2= -1 at val
    rw [ZMod.coe_unitOfCoprime] at val
    apply (ZMod.natCast_zmod_eq_zero_iff_dvd 5 d).mp
    push_cast at val ⊢
    linear_combination val

private theorem good24 : SignedSquares 24 := by unfold SignedSquares; decide +kernel
private theorem good5 : SignedSquares 5 := by unfold SignedSquares; decide +kernel
private theorem good10 : SignedSquares 10 := by unfold SignedSquares; decide +kernel
private theorem bad16 : ¬SignedSquares 16 := by unfold SignedSquares; decide +kernel
private theorem bad20 : ¬SignedSquares 20 := by unfold SignedSquares; decide +kernel

/-- Every odd divisor d must divide 3 or 5, because 2 is a unit modulo d.
The square of 3 rules out 16 and 20 as divisors of the modulus. -/
theorem classification {m : ℕ} [NeZero m] : ProductOnly m ↔ m∣24 ∨ m=5 ∨ m=10 := by
  rw [productOnly_iff]
  constructor
  · intro h
    obtain ⟨k,d,odd,eq⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne m)
    have nod16 : ¬16∣m := fun hd => bad16 (descends hd h)
    have nod20 : ¬20∣m := fun hd => bad20 (descends hd h)
    have k3 : k≤3 := by
      by_contra! large
      apply nod16
      rw [eq]
      exact dvd_mul_of_dvd_left (pow_dvd_pow 2 large) _
    have sd : SignedSquares d := descends (eq ▸ dvd_mul_left d (2^k)) h
    have cases : d=1 ∨ d=3 ∨ d=5 := by
      rcases odd_part sd odd with three|five
      · exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp three).imp_right Or.inl
      · exact ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp five).imp_right Or.inr
    rcases cases with rfl|rfl|rfl <;> interval_cases k <;> subst m <;> norm_num at nod20 ⊢
  · rintro (dvd|rfl|rfl)
    · exact descends dvd good24
    · exact good5
    · exact good10

/-- For modulus zero the ring is the integers and its only units are ±1. -/
theorem zero : ProductOnly 0 := by
  apply (productOnly_iff _).mpr
  intro a
  rcases Int.units_eq_one_or a with rfl|rfl <;> simp

/-- An observed product has a compatible yes pair precisely when it is
one of the two signs of a unit square. -/
theorem yes_iff {m : ℕ} (n : (ZMod m)ˣ) :
    (∃ a b, a*b=n ∧ (a=b ∨ a= -b)) ↔ ∃ u, n=u^2 ∨ n= -(u^2) := by
  constructor
  · rintro ⟨a,b,prod,sgn⟩
    exact ⟨b,prod ▸ (signed_iff_right_square a b).mp sgn⟩
  · rintro ⟨u,rfl|rfl⟩
    · exact ⟨u,u,(sq _).symm,Or.inl rfl⟩
    · exact ⟨-u,u,by simp [sq],Or.inr rfl⟩

/-- Every pair giving this product has equal or opposite factors exactly
when all unit squares are signed ones and this product itself is a signed one. -/
theorem all_yes_iff {m : ℕ} (n : (ZMod m)ˣ) :
    (∀ a b, a*b=n → a=b ∨ a= -b) ↔ SignedSquares m ∧ (n=1 ∨ n= -1) := by
  constructor
  · intro h
    have sign := h n 1 (mul_one _)
    refine ⟨?_,sign⟩
    intro a
    have prod : n*a⁻¹*a=n := by simp [mul_assoc]
    have sgn := (signed_iff_right_square (n*a⁻¹) a).mp (h _ _ prod)
    rw [prod] at sgn
    rcases sign with plus|minus <;> rcases sgn with e|e
    · exact Or.inl (e.symm.trans plus)
    · exact Or.inr (by simpa [plus] using congrArg Neg.neg e.symm)
    · exact Or.inr (e.symm.trans minus)
    · exact Or.inl (by simpa [minus] using congrArg Neg.neg e.symm)
  · rintro ⟨h,sign⟩ a b rfl
    exact (product_rule h a b).mpr sign

/-- Outside the classification, a product admits both possible answers
exactly when it is a square or the negative of a square. -/
theorem ambiguous_iff {m : ℕ} (nonpublic : ¬ProductOnly m) (n : (ZMod m)ˣ) :
    ((∃ a b, a*b=n ∧ (a=b ∨ a= -b)) ∧ (∃ a b, a*b=n ∧ a≠b ∧ a≠ -b)) ↔
      ∃ u, n=u^2 ∨ n= -(u^2) := by
  rw [yes_iff]
  constructor
  · exact And.left
  · intro yes
    refine ⟨yes,?_⟩
    by_contra! no
    apply nonpublic
    apply (productOnly_iff _).mpr
    apply ((all_yes_iff n).mp ?_).1
    intro a b prod
    exact or_iff_not_imp_left.mpr (fun ne => no a b prod ne)

/-- Both ten-bit products have residue 2 modulo 7. The first factor pair
has equal residues there. The second pair has neither equal nor opposite residues. -/
theorem matched : Nat.Prime 17 ∧ Nat.Prime 31 ∧ Nat.Prime 23 ∧ Nat.Prime 29 ∧
    17*31=527 ∧ 23*29=667 ∧ 2^9≤527 ∧ 527<2^10 ∧ 2^9≤667 ∧ 667<2^10 ∧
    527%7=2 ∧ 667%7=2 ∧ (17:ZMod 7)=31 ∧ (23:ZMod 7)≠29 ∧ (23:ZMod 7)≠ -29 := by
  decide +kernel

end PrimeFactors.CyclotomicEnergyResidues
