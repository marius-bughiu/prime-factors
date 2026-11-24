import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Units

namespace PrimeFactors

/-- A Fermat witness at `q` recovers the other prime when `p-1` divides `q-1`.
The gcd uses the reduced residue, as in modular exponentiation. -/
theorem subgroupWitnessFactor {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hfamily : p - 1 ∣ q - 1) (ha : a.Coprime p)
    (hwitness : ¬ Nat.ModEq q (a ^ (p * q - 1)) 1) :
    Nat.gcd (a ^ (p * q - 1) % (p * q) - 1) (p * q) = p := by
  have hp₁ : Nat.ModEq (p - 1) p 1 := Nat.modEq_sub hp.one_le
  have hq₁ : Nat.ModEq (p - 1) q 1 := ((Nat.modEq_iff_dvd' hq.one_le).2 hfamily).symm
  have hexp : p - 1 ∣ p * q - 1 := (Nat.modEq_iff_dvd' (Nat.mul_pos hp.pos hq.pos)).1
    (by simpa using (hp₁.mul hq₁).symm)
  have hfermat : Nat.ModEq p (a ^ (p - 1)) 1 := by
    simpa only [Nat.totient_prime hp] using Nat.ModEq.pow_totient ha
  have hone : Nat.ModEq p (a ^ (p * q - 1)) 1 := by
    obtain ⟨k, hk⟩ := hexp
    rw [hk, pow_mul]
    simpa using hfermat.pow k
  let r := a ^ (p * q - 1) % (p * q)
  have hred : Nat.ModEq (p * q) r (a ^ (p * q - 1)) := Nat.mod_modEq _ _
  have hrp : Nat.ModEq p r 1 := (hred.of_dvd (dvd_mul_right p q)).trans hone
  have hrq : ¬ Nat.ModEq q r 1 :=
    fun h => hwitness ((hred.of_dvd (dvd_mul_left q p)).symm.trans h)
  have hr : 1 ≤ r := by
    by_contra! h
    have e : r = 0 := by omega
    rw [e] at hrp
    simp [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] at hrp
  have hpDiv : p ∣ r - 1 := (Nat.modEq_iff_dvd' hr).1 hrp.symm
  have hqCoprime : q.Coprime (r - 1) :=
    hq.coprime_iff_not_dvd.2 (fun h => hrq ((Nat.modEq_iff_dvd' hr).2 h).symm)
  change Nat.gcd (r - 1) (p * q) = p
  rw [Nat.gcd_comm, Nat.mul_comm p q]
  exact Nat.gcd_mul_of_coprime_of_dvd hqCoprime hpDiv

/-- The finite conclusion needed from the least-prime-outside-a-subgroup bound.
Theorem 1.1(2) of Lamzouri, Li and Soundararajan supplies it in the range
described in `docs/research.md`, after removing small prime divisors. -/
def SmallPrimeOutside (n bound : ℕ) : Prop :=
  ∀ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ →
    ∃ a : ℕ, a.Prime ∧ a ≤ bound ∧ ∃ ha : a.Coprime n, ZMod.unitOfCoprime a ha ∉ H

/-- For this semiprime family the subgroup bound implies a successful gcd
split within the same base limit. -/
theorem exists_subgroupWitnessFactor {p q bound : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hlt : p < q) (hfamily : p - 1 ∣ q - 1) (hsmall : SmallPrimeOutside (p * q) bound) :
    ∃ a : ℕ, a.Prime ∧ a ≤ bound ∧ Nat.gcd (a ^ (p * q - 1) % (p * q) - 1) (p * q) = p := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hqd : q ∣ p * q := dvd_mul_left q p
  let f : (ZMod (p * q))ˣ →* (ZMod q)ˣ := (powMonoidHom (p * q - 1)).comp (ZMod.unitsMap hqd)
  have hproper : f.ker ≠ ⊤ := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hqd g
    intro hall
    have huKer : u ∈ f.ker := hall ▸ Subgroup.mem_top u
    change (ZMod.unitsMap hqd u) ^ (p * q - 1) = 1 at huKer
    rw [hu] at huKer
    have hdiv := orderOf_dvd_of_pow_eq_one huKer
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      (Nat.prime_iff_card_units q).1 hq] at hdiv
    have hsplit : p * q - 1 = (q - 1) * p + (p - 1) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne_zero
      rw [Nat.mul_succ, Nat.succ_sub_one, Nat.mul_comm k p]
      have := hp.pos
      omega
    rw [hsplit] at hdiv
    have hle : q - 1 ≤ p - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt)
      ((Nat.dvd_add_iff_right (dvd_mul_right (q - 1) p)).2 hdiv)
    have := hp.pos
    omega
  obtain ⟨a, hprime, hab, ha, hout⟩ := hsmall f.ker hproper
  refine ⟨a, hprime, hab, subgroupWitnessFactor hp hq hfamily
    (ha.of_dvd_right (dvd_mul_right p q)) ?_⟩
  intro heq
  apply hout
  change (ZMod.unitsMap hqd (ZMod.unitOfCoprime a ha)) ^ (p * q - 1) = 1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hqd]
  simpa using (ZMod.natCast_eq_natCast_iff _ _ _).2 heq

end PrimeFactors
