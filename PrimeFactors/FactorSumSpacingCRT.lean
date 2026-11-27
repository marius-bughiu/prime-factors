import PrimeFactors.FactorSumSpacing
import PrimeFactors.FactorSumCRT
import Mathlib.Data.Nat.Factorization.Induction

/-! Spacings between admissible factor sums combine across coprime moduli.
Every spacing occurs if all prime divisors of the modulus are at least eleven. -/
namespace PrimeFactors.FactorSumSpacing

/-- Two admissible sums at a prescribed spacing modulo a product are equivalent
to a pair at that spacing in each coprime component. -/
theorem crt_iff {a b : ℕ} (cop : a.Coprime b) (n t : ℤ) :
    Gap (a*b) n t ↔ Gap a n t ∧ Gap b n t := by
  let e := ZMod.chineseRemainder cop
  have split (s : ZMod (a*b)) :
      AdmissibleSum (n : ZMod (a*b)) s ↔
      AdmissibleSum (n : ZMod a) (e s).1 ∧ AdmissibleSum (n : ZMod b) (e s).2 := by
    simpa only [e, map_intCast, Prod.fst_intCast, Prod.snd_intCast] using
      admissibleSum_crt_iff cop (n : ZMod (a*b)) s
  constructor
  · rintro ⟨s, hs, ht⟩
    obtain ⟨ha, hb⟩ := (split s).mp hs
    obtain ⟨hta, htb⟩ := (split _).mp ht
    simp only [map_add, map_intCast, Prod.fst_add, Prod.snd_add, Prod.fst_intCast,
      Prod.snd_intCast] at hta htb
    exact ⟨⟨(e s).1, ha, hta⟩, ⟨(e s).2, hb, htb⟩⟩
  · rintro ⟨⟨x, hx, hxt⟩, ⟨y, hy, hyt⟩⟩
    refine ⟨e.symm (x,y), (split _).mpr ?_, (split _).mpr ?_⟩
    · simpa only [e.apply_symm_apply] using And.intro hx hy
    · simpa only [map_add, e.apply_symm_apply, map_intCast, Prod.fst_add, Prod.snd_add,
        Prod.fst_intCast, Prod.snd_intCast] using And.intro hxt hyt

/-- No combination of prime powers with primes at least eleven can exclude
a fixed spacing using only the product and local admissibility of the two sums. -/
theorem all_large_prime_factors (n t : ℤ) (m : ℕ) (pos : 0<m)
    (large : ∀ p, p.Prime → p∣m → 11≤p) : Gap m n t := by
  revert pos large
  induction m using Nat.recOnPosPrimePosCoprime with
  | hp p k pp kp =>
    cases k with
    | zero => omega
    | succ k =>
      intro _ large
      letI : Fact p.Prime := ⟨pp⟩
      have dv : p∣p^(k+1) := dvd_pow_self _ (Nat.succ_ne_zero k)
      exact prime_power_all (large p pp dv) n t k
  | h0 => omega
  | h1 =>
    intros
    have every (s : ZMod 1) : AdmissibleSum (n : ZMod 1) s :=
      ⟨0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    exact ⟨0, every _, every _⟩
  | h a b ha hb ab ia ib =>
    intro _ large
    have da : a∣a*b := dvd_mul_right _ _
    have db : b∣a*b := dvd_mul_left _ _
    have left := ia (by omega) (fun p hp d => large p hp (d.trans da))
    have right := ib (by omega) (fun p hp d => large p hp (d.trans db))
    exact (crt_iff ab n t).mpr ⟨left, right⟩

end PrimeFactors.FactorSumSpacing
