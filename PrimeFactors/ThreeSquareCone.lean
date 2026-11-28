import PrimeFactors.ExtensionTrace

/-! Exact counts of ordered triples with a prescribed sum of three squares
over finite fields of odd characteristic, including the singular zero fiber. -/

namespace PrimeFactors.ThreeSquareCone

open Finset
open private PrimeFactors.ExtensionTrace.shifted_square from PrimeFactors.ExtensionTrace

/-- All ordered triples, with zero coordinates allowed. This set also makes
sense over residue rings of composite modulus. -/
noncomputable def points (F : Type*) [CommRing F] [Fintype F] [DecidableEq F] (t : F) :
    Finset (F×F×F) :=
  univ.filter (fun v => v.1^2+v.2.1^2+v.2.2^2=t)

@[simp] theorem mem_points {F : Type*} [CommRing F] [Fintype F] [DecidableEq F]
    {t : F} {v : F×F×F} : v∈points F t ↔ v.1^2+v.2.1^2+v.2.2^2=t := by
  simp [points]

/-- For Q elements the number of triples at t is Q²+Qχ(−t), with χ(0)=0.
The proof counts possible third coordinates, then sums a shifted quadratic
character in the second coordinate. -/
theorem field_count (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (odd : ringChar F≠2) (t : F) : ((points F t).card : ℤ) =
      (Fintype.card F:ℤ)^2+(Fintype.card F:ℤ)*quadraticChar F (-t) := by
  have roots (s:F) : (∑ z:F, if z^2=s then (1:ℤ) else 0)=quadraticChar F s+1 := by
    rw [sum_boole]
    simpa only [Set.toFinset_setOf] using quadraticChar_card_sqrts odd s
  have third (x y:F) : (∑ z:F, if x^2+y^2+z^2=t then (1:ℤ) else 0) =
      quadraticChar F (t-x^2-y^2)+1 := by
    convert roots (t-x^2-y^2) using 1
    apply sum_congr rfl
    intro z _
    congr 1
    exact propext ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  have middle (x : F) : (∑ y:F, quadraticChar F (t-x^2-y^2)) =
      quadraticChar F (-1) * ((if x^2=t then (Fintype.card F:ℤ) else 0)-1) := by
    have perm (y:F) : t-x^2-y^2=(-1)*(y^2-(t-x^2)) := by ring
    simp_rw [perm,map_mul, ←mul_sum, PrimeFactors.ExtensionTrace.shifted_square odd]
    rw [if_congr (show t-x^2=0 ↔ x^2=t by rw [sub_eq_zero,eq_comm]) rfl rfl]
  have weighted : (∑ x:F, if x^2=t then (Fintype.card F:ℤ) else 0) =
      (quadraticChar F t+1)*(Fintype.card F) := by
    rw [←roots]
    simp only [sum_mul, ite_mul, one_mul, zero_mul]
  simp only [points,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    Fintype.sum_prod_type,third,sum_add_distrib,middle,← mul_sum,sum_sub_distrib,weighted,
    sum_const,card_univ,nsmul_eq_mul,mul_one]
  rw [show -t=(-1)*t by ring,map_mul]
  ring

/-- At an odd prime the zero fiber has exactly p² points. -/
theorem prime_zero (p : ℕ) [Fact p.Prime] (odd : p≠2) :
    (points (ZMod p) 0).card=p^2 := by
  have h := field_count (ZMod p) (by rwa [ZMod.ringChar_zmod_n]) 0
  simp only [ZMod.card,neg_zero,quadraticChar_zero,mul_zero,add_zero] at h
  exact_mod_cast h

/-- Removing the origin leaves all p²−1 nonzero triples on the cone. -/
theorem prime_nonzero_points (p : ℕ) [Fact p.Prime] (odd : p≠2) :
    ((points (ZMod p) 0).erase (0,0,0)).card=p^2-1 := by
  rw [card_erase_of_mem (by simp),prime_zero p odd]

/-- Direct enumeration at 5 checks the zero, square and nonsquare corrections. -/
theorem five : (points (ZMod 5) 0).card=25 ∧ (points (ZMod 5) 1).card=30 ∧
    (points (ZMod 5) 2).card=20 := by decide +kernel

end PrimeFactors.ThreeSquareCone
