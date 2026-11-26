import PrimeFactors.GeometricCollisionGap
import PrimeFactors.ReducedSlopes
import Mathlib.Data.Nat.Factorization.Basic

/-! An order divisor in any quotient of the public unit group can improve
its own factor-sum congruence. A quotient map is a hypothesis: the example
below instead certifies an order directly in the public group. -/
namespace PrimeFactors.PartialOrderLift

private theorem gcd_lcm_right {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (a.lcm b).gcd c = (a.gcd c).lcm (b.gcd c) := by
  have da : a.gcd c ≠ 0 := fun h => ha (Nat.gcd_eq_zero_iff.mp h).1
  have db : b.gcd c ≠ 0 := fun h => hb (Nat.gcd_eq_zero_iff.mp h).1
  apply Nat.factorization_inj (show (a.lcm b).gcd c ≠ 0 from fun h => hc (Nat.gcd_eq_zero_iff.mp h).2)
    (show (a.gcd c).lcm (b.gcd c) ≠ 0 from Nat.lcm_ne_zero da db)
  rw [Nat.factorization_gcd (Nat.lcm_ne_zero ha hb) hc, Nat.factorization_lcm ha hb,
    Nat.factorization_lcm da db, Nat.factorization_gcd ha hc, Nat.factorization_gcd hb hc]
  ext t
  exact inf_sup_right (a.factorization t) (b.factorization t) (c.factorization t)

/-- For two primes the public predecessor intersects the group exponent in
exactly the common predecessor divisor. The identity only requires p,q>1. -/
theorem exponent_gcd {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    ((p-1).lcm (q-1)).gcd (p*q-1) = (p-1).gcd (q-1) := by
  have hpq : 1 < p*q := by nlinarith
  rw [gcd_lcm_right (by omega) (by omega) (by omega), gcd_predecessor_product (by omega) (by omega),
    Nat.mul_comm p q, gcd_predecessor_product (by omega) (by omega), Nat.gcd_comm (q-1) (p-1),
    Nat.lcm_self]

/-- At the exact group exponent the lifted modulus is the whole totient. -/
theorem full_exponent_modulus {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    let d := (p-1).lcm (q-1)
    d*d.gcd (p*q-1) = (p-1)*(q-1) := by
  dsimp only
  rw [exponent_gcd hp hq, Nat.mul_comm, Nat.gcd_mul_lcm]

/-- With any certified divisor m of the exponent one can use the modulus
m*gcd(m,N−1). For the full exponent this modulus equals the totient. -/
theorem sum_lift {p q m : ℕ} (hp : 1 < p) (hq : 1 < q) (known : m ∣ (p-1).lcm (q-1)) :
    p+q ≡ p*q+1 [MOD m*m.gcd (p*q-1)] := by
  have extra : m.gcd (p*q-1) ∣ (p-1).gcd (q-1) := by
    rw [←exponent_gcd hp hq]
    exact Nat.dvd_gcd ((Nat.gcd_dvd_left ..).trans known) (Nat.gcd_dvd_right ..)
  have phi : m*m.gcd (p*q-1) ∣ (p-1)*(q-1) := by
    rw [←Nat.gcd_mul_lcm (p-1) (q-1), Nat.mul_comm ((p-1).gcd (q-1))]
    exact Nat.mul_dvd_mul known extra
  have decomp : p+q+(p-1)*(q-1) = p*q+1 := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p≠0)
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q≠0)
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring
  rw [←decomp, Nat.modEq_iff_dvd' (Nat.le_add_right ..), Nat.add_sub_cancel_left]
  exact phi

/-- A witnessed order divisor of the image of a single public unit suffices;
the quotient may be any monoid, and its computation is charged separately. -/
theorem from_image {p q g m : ℕ} {H : Type*} [Monoid H]
    (hp : p.Prime) (hq : q.Prime) (distinct : p≠q) (unit : g.Coprime (p*q))
    (χ : (ZMod (p*q))ˣ →* H) (known : m ∣ orderOf (χ (ZMod.unitOfCoprime g unit))) :
    p+q ≡ p*q+1 [MOD m*m.gcd (p*q-1)] := by
  apply sum_lift hp.one_lt hq.one_lt
  have global : m ∣ GeometricCollisionGap.ord (p*q) g unit :=
    known.trans (orderOf_map_dvd ..)
  rw [GeometricCollisionGap.global_order ((Nat.coprime_primes hp hq).mpr distinct) unit] at global
  have loc {r : ℕ} (prime : r.Prime) (u : g.Coprime r) : GeometricCollisionGap.ord r g u ∣ r-1 := by
    letI : Fact r.Prime := ⟨prime⟩
    exact orderOf_dvd_of_pow_eq_one (ZMod.units_pow_card_sub_one_eq_one r _)
  exact global.trans (Nat.lcm_dvd ((loc hp _).trans (Nat.dvd_lcm_left ..))
                                   ((loc hq _).trans (Nat.dvd_lcm_right ..)))

/-- Concrete public power checks can supply the entire order m of one unit,
without knowing either local order or assuming they agree. -/
theorem from_public_order {p q g m : ℕ} (hp : p.Prime) (hq : q.Prime) (distinct : p≠q)
    (unit : g.Coprime (p*q)) (positive : 0<m) (kill : g^m ≡ 1 [MOD p*q])
    (minimal : ∀ ℓ, ℓ.Prime → ℓ∣m → ¬g^(m/ℓ) ≡ 1 [MOD p*q]) :
    p+q ≡ p*q+1 [MOD m*m.gcd (p*q-1)] :=
  from_image hp hq distinct unit (MonoidHom.id _)
    (dvd_of_eq (GeometricCollisionGap.stripped unit positive kill minimal).symm)

/-- 4,193,821 = Φ₅(45). The public order-five witness singles out one
residue for the sum at modulus 25, before either prime has been supplied. -/
theorem public_4193821 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (distinct : p≠q)
    (product : p*q=4193821) : p+q ≡ 22 [MOD 25] := by
  have unit : Nat.Coprime 45 (p*q) := by rw [product]; decide +kernel
  have hit : p+q ≡ p*q+1 [MOD 5*(5:ℕ).gcd (p*q-1)] := by
    apply from_public_order hp hq distinct unit (by decide)
    · rw [product]; decide +kernel
    · intro ℓ prime div
      obtain one | five := (Nat.dvd_prime (by decide : Nat.Prime 5)).mp div
      · exact (prime.ne_one one).elim
      · subst ℓ; rw [product]; decide +kernel
  rw [product] at hit
  exact hit.trans (by decide +kernel)

/-- The local product condition alone also allows the sum 0 modulo 25. -/
theorem untreated_4193821 : 2*23 ≡ 4193821 [MOD 25] ∧ ¬(2+23 ≡ 22 [MOD 25]) := by
  decide +kernel

end PrimeFactors.PartialOrderLift
