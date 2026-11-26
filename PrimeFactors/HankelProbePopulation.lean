import PrimeFactors.HankelProbePolynomial
import PrimeFactors.SquareRootShiftPartners
import PrimeFactors.ChebyshevPrimeSample

/-! Population bound for the eight public Hasse Hankel determinant tests on
products of two 1024-bit primes, including both fixed and square-root shifts. -/
namespace PrimeFactors.HankelProbePopulation

open Finset HasseHankelBilinear HankelTranslation HankelProbePolynomial
open MixedPrefixSample SquareRootShiftPartners

def rawHit {p : ℕ} (c : ZMod p) : Prop :=
  rawMinor (hankel (fun j => TranslatedHasse.value j c)) 0 = 0 ∨
  rawMinor (hankel (fun j => TranslatedHasse.value j c)) 1 = 0

def menuHit (p n : ℕ) : Prop :=
  rawHit (2 : ZMod p) ∨ rawHit (3 : ZMod p) ∨
    rawHit (n.sqrt : ZMod p) ∨ rawHit ((n.sqrt : ZMod p)+1)

/-- Counts each unordered eligible pair once, allowing a hit on either local prime. -/
noncomputable def flagged : Finset (ℕ×ℕ) := by
  classical
  exact eligible.filter (fun z => menuHit z.1 (z.1*z.2) ∨ menuHit z.2 (z.1*z.2))

private theorem info {p : ℕ} (h : p∈primes) :
    (X≤p ∧ p<2*X) ∧ p.Prime := by simpa [primes, and_assoc] using h

attribute [local irreducible] X eligible primes

private theorem eligible_anchor {p q : ℕ} (hp : p∈primes) (hq : q∈primes)
    (hit : menuHit p (p*q)) :
    (min p q, max p q) ∈ detected residues := by
  classical
  obtain ⟨⟨pl,_⟩,pp⟩ := info hp
  obtain ⟨⟨ql,qu⟩,qp⟩ := info hq
  letI : Fact p.Prime := ⟨pp⟩
  have big : 2^280≤p := (by decide +kernel : 2^280 ≤ X).trans pl
  have odd : q%2=1 := (qp.eq_two_or_odd.resolve_left (by
    have : 2<X := by decide +kernel
    omega))
  have two : (2:ZMod p)≠0 := by
    intro z
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0<2)
      ((by decide +kernel : 2<X).trans_le pl) ((ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp z)
  obtain ⟨fixedTwo,fixedThree⟩ := fixed_shifts p big
  have r := mem_residues big ((p*q).sqrt : ZMod p) (by
    rcases hit with a|b|c|d
    · exact False.elim (fixedTwo (zero_of_raw _ two a))
    · exact False.elim (fixedThree (zero_of_raw _ two b))
    · exact Or.inl (zero_of_raw _ two c)
    · exact Or.inr (zero_of_raw _ two d))
  exact mem_biUnion.mpr ⟨p,hp,mem_image.mpr ⟨q,mem_filter.mpr ⟨mem_Ico.mpr ⟨ql,qu⟩,odd,r⟩,rfl⟩⟩

/-- Includes every split by the four shifts and two initial determinants.
A zero at both primes is also included, so flagging can overcount actual splits. -/
theorem population_bound :
    2^990*flagged.card < eligible.card := by
  classical
  have sub : flagged ⊆ detected residues ∩ eligible := by
    intro z hz
    obtain ⟨m,hit⟩ := mem_filter.mp hz
    have parts := m
    rw [eligible,sample] at parts
    obtain ⟨ord,lt⟩ := mem_filter.mp parts
    obtain ⟨p,q,_,_,_⟩ := mem_ordered.mp ord
    refine mem_inter.mpr ⟨?_,m⟩
    rcases hit with a|b
    · simpa [min_eq_left lt.le,max_eq_right lt.le] using eligible_anchor p q a
    · rw [Nat.mul_comm] at b
      simpa [min_eq_right lt.le,max_eq_left lt.le] using eligible_anchor q p b
  have cap (p : ℕ) (hp : p∈primes) : (residues p).card ≤ 202 := by
    have h := info hp
    letI : Fact p.Prime := ⟨h.2⟩
    exact residues_card p ((by decide +kernel : 2^280 ≤ X).trans h.1.1)
  exact (Nat.mul_le_mul_left _ (card_le_card sub)).trans_lt
    (population residues cap ChebyshevPrimeSample.prime_count)

end PrimeFactors.HankelProbePopulation
