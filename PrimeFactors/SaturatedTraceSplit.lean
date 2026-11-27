import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Split a public modulus into the full prime-power parts supported on a
public seed and the complementary part, by a single modular power and a gcd. -/
namespace PrimeFactors.SaturatedTraceSplit

private def ladder (d base : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1%d
  | bits+1, exponent =>
    let half := ladder d base bits (exponent/2)
    let square := half*half%d
    if exponent%2=1 then (base*square)%d else square

private theorem ladder_eq (d z bits exponent : ℕ) (fits : exponent < 2^bits) :
    ladder d (z%d) bits exponent = z^exponent%d := by
  induction bits generalizing exponent with
  | zero =>
    have : exponent=0 := by simpa using fits
    simp [ladder,this]
  | succ bits ih =>
    have small : exponent/2 < 2^bits := by
      rw [pow_succ] at fits
      omega
    rw [ladder,ih _ small]
    have digits : exponent/2+exponent/2+exponent%2=exponent := by omega
    conv_rhs => rw [←digits, pow_add, pow_add]
    by_cases odd : exponent%2=1
    · simp [odd,Nat.mod_mul_mod,Nat.mul_mod_mod,Nat.mul_comm]
    · have even : exponent%2=0 := by omega
      simp [even,Nat.mod_mul_mod,Nat.mul_mod_mod]

private def bitLength (n : ℕ) := if n=0 then 0 else n.log2+1

private theorem bitLength_eq (n : ℕ) : bitLength n = n.size := by
  by_cases hn : n=0
  · simp [bitLength,hn]
  rw [bitLength,if_neg hn]
  exact le_antisymm (Nat.lt_size.mpr (Nat.log2_self_le hn))
    (Nat.size_le.mpr ((Nat.log2_lt hn).mp (Nat.lt_succ_self _)))

/-- Binary powering with all stored residues reduced modulo the input modulus.
Each exponent bit costs one square and at most one additional multiplication. -/
def powerMod (d z L : ℕ) := ladder d (z%d) (bitLength L) L

theorem powerMod_eq (d z L : ℕ) : powerMod d z L = z^L%d := by
  rw [powerMod,bitLength_eq]
  exact ladder_eq d z _ _ (Nat.lt_size_self L)

/-- The whole primary part of d supported on primes dividing z. -/
def v (d z : ℕ) := (powerMod d z (bitLength d)).gcd d

/-- Complementary part of the modulus. -/
def u (d z : ℕ) := d / v d z

theorem v_eq (d z : ℕ) : v d z = (z^d.size).gcd d := by
  rw [v, bitLength_eq, powerMod_eq, ←Nat.gcd_rec, Nat.gcd_comm]

theorem v_dvd (d z : ℕ) : v d z ∣ d := v_eq d z ▸ Nat.gcd_dvd_right _ _

theorem product (d z : ℕ) : u d z * v d z = d := Nat.div_mul_cancel (v_dvd d z)

theorem prime_support {d z p : ℕ} (hp : p.Prime) (h : p ∣ v d z) : p ∣ z := by
  rw [v_eq] at h
  exact hp.dvd_of_dvd_pow (h.trans (Nat.gcd_dvd_left _ _))

/-- Saturation includes the full exponent of each selected prime. -/
theorem prime_power_dvd {d z p : ℕ} (hd : 0<d) (hp : p.Prime) (hz : p∣z) :
    p^(d.factorization p) ∣ v d z := by
  have full := Nat.ordProj_dvd d p
  have lt : d.factorization p < d.size :=
    Nat.lt_size.mpr ((Nat.pow_le_pow_left hp.two_le _).trans (Nat.le_of_dvd hd full))
  rw [v_eq]
  exact Nat.dvd_gcd ((pow_dvd_pow p lt.le).trans (pow_dvd_pow_of_dvd hz _)) full

theorem unit_seed {d z : ℕ} (hd : 0<d) : z.Coprime (u d z) := by
  by_contra bad
  obtain ⟨p,hp,hz,hu⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
  have excessive : p^(d.factorization p+1) ∣ d := by
    rw [pow_succ, Nat.mul_comm]
    have both := Nat.mul_dvd_mul hu (prime_power_dvd hd hp hz)
    rwa [product] at both
  have impossible := (hp.pow_dvd_iff_le_factorization hd.ne').mp excessive
  omega

theorem coprime_parts {d z : ℕ} (hd : 0<d) : (u d z).Coprime (v d z) := by
  by_contra bad
  obtain ⟨p,hp,hu,hv⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
  exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt (prime_support hp hv) hu (unit_seed hd)

/-- Any translate by a unit modulo d is a unit on its z-supported part. -/
theorem unit_translate {d z a : ℕ} (unit : a.Coprime d) : (z+a).Coprime (v d z) := by
  by_contra bad
  obtain ⟨p,hp,sum,hv⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
  have ha : p∣a := (Nat.dvd_add_iff_right (prime_support hp hv)).mpr sum
  exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt ha (hv.trans (v_dvd d z)) unit

/-- The two units needed by the adaptive character can always be obtained from
the public d,z,e using a modular power, one gcd and an exact division. -/
theorem split_spec {d z e : ℕ} (hd : 0<d) (unit : (2*e).Coprime d) :
    u d z * v d z = d ∧ (u d z).Coprime (v d z) ∧
    z.Coprime (u d z) ∧ (z+4*e).Coprime (v d z) := by
  refine ⟨product d z, coprime_parts hd, unit_seed hd, unit_translate ?_⟩
  have two : Nat.Coprime 2 d := unit.coprime_dvd_left (dvd_mul_right 2 e)
  rw [show 4*e = 2*(2*e) by omega, Nat.coprime_mul_iff_left]
  exact ⟨two,unit⟩

/-- Both powers of 5 and all three powers of 3 go to the second part, even though
neither full prime power divides the original seed 15. -/
theorem example_4725 :
    (15:ℕ).gcd 4725 = 15 ∧ u 4725 15 = 7 ∧ v 4725 15 = 675 ∧
    (15:ℕ).Coprime 7 ∧ (19:ℕ).Coprime 675 := by
  have bits : (4725:ℕ).size = 13 := le_antisymm (Nat.size_le.mpr (by decide))
    (Nat.lt_size.mpr (by decide : 2^12≤4725))
  simp only [u,v_eq,bits]
  decide

end PrimeFactors.SaturatedTraceSplit
