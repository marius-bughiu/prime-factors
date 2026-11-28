import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic

/-! The exact precision of a single factor-sum remainder forced by knowing
one modular factor in a prescribed residue class. Only the product and
the supplied class enter the greatest common divisor. -/
namespace PrimeFactors.FactorClueSumPrecision

/-- The fixed divisor of the quadratic change in the scaled sum. -/
private def precision (N a m : ℕ) : ℕ :=
  Int.gcd ((m : ℤ) * ((a : ℤ)^2 - N + a*m)) (2*(a : ℤ)*m^2)

private def changeAt (N a m t : ℕ) : ℤ :=
  (m : ℤ)*t*((a : ℤ)^2 - N + a*m*t)

private theorem fixed_divisor (N a m M : ℕ) :
    (∀ t : ℕ, (M : ℤ) ∣ changeAt N a m t) ↔ M ∣ precision N a m := by
  let B := (m : ℤ)*((a : ℤ)^2-N+a*m)
  let C := 2*(a : ℤ)*m^2
  have first : changeAt N a m 1 = B := by unfold changeAt B; ring
  have second : changeAt N a m 2 - 2*B = C := by unfold changeAt B C; push_cast; ring
  change _ ↔ M ∣ Int.gcd B C
  constructor
  · intro all
    have b := first ▸ all 1
    have c : (M : ℤ) ∣ C := second ▸ dvd_sub (all 2) (dvd_mul_of_dvd_right b 2)
    exact Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd b c)
  · intro div t
    have D : (M : ℤ) ∣ (Int.gcd B C : ℤ) := Int.natCast_dvd_natCast.mpr div
    obtain ⟨k,hk⟩ := Int.even_mul_pred_self (t : ℤ)
    have eq : changeAt N a m t = B*t + C*k := by
      dsimp [changeAt,B,C]
      linear_combination (a : ℤ)*m^2*hk
    rw [eq]
    exact dvd_add (dvd_mul_of_dvd_left (D.trans Int.gcd_dvd_left) _)
      (dvd_mul_of_dvd_left (D.trans Int.gcd_dvd_right) _)

/-- Every modular factor x from the supplied class gives the same scaled
sum a(x+y)=a²+N. When a is invertible this determines the sum uniquely. -/
def Pinned (M N a m : ℕ) : Prop :=
  ∀ (t : ℕ) (y : ZMod M), ((a+m*t : ℕ) : ZMod M)*y=N →
    (a : ZMod M)*(((a+m*t : ℕ) : ZMod M)+y)=(a : ZMod M)^2+N

/-- The moduli tested may involve any primes dividing m, to arbitrary
precision. A failure of divisibility implies an actual modular counterexample. -/
private theorem pinned_iff {M N a m : ℕ} (cop : a.Coprime m)
    (supported : ∃ k : ℕ, M ∣ m^k) :
    Pinned M N a m ↔ M ∣ precision N a m := by
  obtain ⟨k,hk⟩ := supported
  have unit (t : ℕ) : IsUnit ((a+m*t : ℕ) : ZMod M) :=
    (ZMod.isUnit_iff_coprime _ _).mpr
      ((((Nat.coprime_add_mul_left_left a m t).mpr cop).pow_right k).of_dvd_right hk)
  have scaled (t : ℕ) (y : ZMod M) (prod : ((a+m*t : ℕ) : ZMod M)*y=N) :
      (a+m*t : ZMod M)*((a : ZMod M)*((a+m*t)+y)-(a^2+N))=(changeAt N a m t : ZMod M) := by
    push_cast at prod
    dsimp [changeAt]
    push_cast
    linear_combination (a : ZMod M)*prod
  rw [← fixed_divisor]
  constructor
  · intro pinned t
    obtain ⟨u,hu⟩ := unit t
    let y := (↑u⁻¹ : ZMod M)*N
    have prod : ((a+m*t : ℕ) : ZMod M)*y=N := by rw [←hu]; simp [y,←mul_assoc]
    have eq := pinned t y prod
    push_cast at eq
    have zero := scaled t y prod
    rw [eq,sub_self,mul_zero] at zero
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp zero.symm
  · intro div t y prod
    have zero := scaled t y prod
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (div t)] at zero
    have ux := unit t
    push_cast at ux ⊢
    exact sub_eq_zero.mp (ux.mul_left_cancel (by simpa only [mul_zero] using zero :
      (a+m*t : ZMod M)*((a : ZMod M)*((a+m*t)+y)-(a^2+N))=(a+m*t : ZMod M)*0))

/-- The largest possible increase in precision from m, before the
product-dependent first difference is taken into account. -/
def cap (m : ℕ) : ℕ := if 2 ∣ m then 2*m^2 else m^2

/-- Greatest modulus supported on the supplied modulus for which the sum
is forced to a single residue. -/
def greatest (N a m : ℕ) : ℕ :=
  Int.gcd ((m : ℤ)*((a : ℤ)^2-N+a*m)) (cap m)

private theorem cap_supported (m : ℕ) : cap m ∣ m^3 := by
  unfold cap
  split_ifs with even
  · simpa only [pow_succ m 2, mul_comm (m^2) m] using Nat.mul_dvd_mul_right even (m^2)
  · exact pow_dvd_pow _ (by decide : 2≤3)

/-- The factor clue gives a unique sum modulo M exactly for the divisors
of the single, explicitly computable modulus greatest N a m. -/
theorem unique_precision {M N a m : ℕ} (cop : a.Coprime m)
    (supported : ∃ k : ℕ, M ∣ m^k) :
    Pinned M N a m ↔ M ∣ greatest N a m := by
  rw [pinned_iff cop supported]
  obtain ⟨k,support⟩ := supported
  have ca : M.Coprime a := ((cop.pow_right k).of_dvd_right support).symm
  let B := (m : ℤ)*((a : ℤ)^2-N+a*m)
  have gcd_iff (c : ℕ) : M ∣ Int.gcd B (c : ℤ) ↔ (M : ℤ) ∣ B ∧ M ∣ c := by
    constructor
    · intro div
      have hz := Int.natCast_dvd_natCast.mpr div
      exact ⟨hz.trans Int.gcd_dvd_left,Int.natCast_dvd_natCast.mp (hz.trans Int.gcd_dvd_right)⟩
    · rintro ⟨left,right⟩
      exact Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd left (Int.natCast_dvd_natCast.mpr right))
  change M ∣ Int.gcd B (2*(a : ℤ)*m^2) ↔ M ∣ Int.gcd B (cap m)
  rw [show 2*(a : ℤ)*m^2 = ((a*(2*m^2) : ℕ) : ℤ) by push_cast; ring,
    gcd_iff, gcd_iff, ca.dvd_mul_left]
  unfold cap
  split_ifs with even
  · rfl
  · have c2 := ((Nat.prime_two.coprime_iff_not_dvd.mpr even).pow_right k).of_dvd_right support
    rw [c2.symm.dvd_mul_left]

/-- The computed greatest modulus itself works. Since a is a unit modulo
it, the linear equation in Pinned determines a unique ordinary sum residue. -/
theorem at_greatest {N a m : ℕ} (cop : a.Coprime m) :
    Pinned (greatest N a m) N a m ∧ a.Coprime (greatest N a m) := by
  have div : greatest N a m ∣ m^3 :=
    (Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..)).trans (cap_supported m)
  exact ⟨(unique_precision cop ⟨3,div⟩).mpr dvd_rfl,(cop.pow_right 3).of_dvd_right div⟩

/-- An actual factorization satisfying the supplied clue obeys the same
congruence at the greatest modulus. Primality is unnecessary. -/
theorem factor_sum {N p q a m : ℕ} (prod : p*q=N) (cop : a.Coprime m)
    (clue : ∃ t, p=a+m*t) :
    (a : ZMod (greatest N a m))*((p : ZMod (greatest N a m))+q)=(a : ZMod (greatest N a m))^2+N := by
  obtain ⟨t,rfl⟩ := clue
  have h := (at_greatest (N:=N) cop).1 t q (by rw [←Nat.cast_mul,prod])
  push_cast at h ⊢
  exact h

/-- The gcd with a natural modulus depends only on the integer residue. -/
theorem gcd_of_congruent {b r : ℤ} {c : ℕ} (eq : b ≡ r [ZMOD (c : ℤ)]) :
    Int.gcd b c = Int.gcd r c := by
  have le {u v : ℤ} (h : u ≡ v [ZMOD (c : ℤ)]) : Int.gcd u c ∣ Int.gcd v c := by
    apply Int.natCast_dvd_natCast.mp
    apply Int.dvd_coe_gcd _ Int.gcd_dvd_right
    have du : (Int.gcd u c : ℤ) ∣ u := Int.gcd_dvd_left ..
    have dc : (Int.gcd u c : ℤ) ∣ c := Int.gcd_dvd_right ..
    simpa only [sub_add_cancel] using dvd_add (dc.trans (Int.modEq_iff_dvd.mp h)) du
  exact Nat.dvd_antisymm (le eq) (le eq.symm)

/-- Knowing the common factor class modulo twelve gives exactly one sum
modulo 144 or 288, depending only on the product modulo eight. No larger
2,3-supported modulus pins a unique residue in the modular factor model. -/
theorem twelve {N a : ℕ} (one : N%12=1) (cop : a.Coprime 12) :
    greatest N a 12 = if N%8=1 then 144 else 288 := by
  have cop24 := (cop.pow_right 2).of_dvd_right (by decide : 24∣12^2)
  let u := ZMod.unitOfCoprime a cop24
  have table : ∀ v : (ZMod 24)ˣ, (v : ZMod 24)^2+12*v=13 := by decide +kernel
  have residue : ((a : ℤ)^2+12*a) ≡ 13 [ZMOD 24] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ 24).mp
    push_cast
    simpa only [u,ZMod.coe_unitOfCoprime] using table u
  change Int.gcd (12*((a : ℤ)^2-N+a*12)) 288=_
  have rem : ((a : ℤ)^2+12*a)%24=13 := residue
  have input : (N : ℤ)%12=1 := by exact_mod_cast one
  rw [mul_comm (a : ℤ) 12]
  by_cases h : N%8=1
  · have h8 : (N : ℤ)%8=1 := by exact_mod_cast h
    rw [if_pos h]
    refine (gcd_of_congruent (b:=12*((a : ℤ)^2-N+12*a)) (r:=144) (c:=288) (by
      change (12*((a : ℤ)^2-N+12*a))%288=144
      omega)).trans (by decide)
  · have h8 : ¬(N : ℤ)%8=1 := by exact_mod_cast h
    rw [if_neg h]
    refine (gcd_of_congruent (b:=12*((a : ℤ)^2-N+12*a)) (r:=0) (c:=288) (by
      change (12*((a : ℤ)^2-N+12*a))%288=0
      omega)).trans (by decide)

end PrimeFactors.FactorClueSumPrecision
