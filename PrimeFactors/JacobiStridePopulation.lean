import PrimeFactors.JacobiPeriodProbe
import PrimeFactors.ChebyshevPrimeSample

/-! Count the sorted pairs of 1024-bit primes with a full 2048-bit product for
which the least all-offset period at stride (N−1)/2 fits a given budget. -/
namespace PrimeFactors.JacobiStridePopulation

open Finset MixedPrefixSample JacobiPeriodCount

/-- Eligible pairs whose product of reduced predecessors fits the candidate budget. -/
noncomputable def short (B : ℕ) : Finset (ℕ × ℕ) :=
  eligible.filter fun z => residualProduct z.1 z.2 ≤ B

/-- The larger reduced predecessor is b, the smaller a. Both prime predecessors
are even, so the common multiplier can be written as 2h. -/
private def withLarger (X b : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (X/b)) ×ˢ Icc 1 b).image fun x => (2*(x.1*x.2)+1,2*(x.1*b)+1)

private theorem withLarger_card (X b : ℕ) : (withLarger X b).card ≤ X := by
  refine card_image_le.trans ?_
  simpa [Finset.card_product] using Nat.div_mul_le_self X b

private theorem prime_info {p : ℕ} (mem : p ∈ primes) : (X ≤ p ∧ p < 2*X) ∧ p.Prime := by
  simpa only [primes,mem_filter,mem_Ico] using mem

attribute [local irreducible] X eligible primes ordered
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

/-- Each possible larger reduced predecessor costs at most X pairs, even
when all integer pairs in its progression are counted. -/
theorem short_card {B J : ℕ} (cut : 2*B < (J+1)^2) : (short B).card ≤ X*J := by
  classical
  let pool := (Icc 1 J).biUnion (withLarger X)
  have sub : short B ⊆ pool := by
    rintro ⟨p,q⟩ mem
    obtain ⟨ok,small⟩ := mem_filter.mp mem
    change residualProduct p q ≤ B at small
    rw [eligible,sample] at ok
    obtain ⟨ord,pq⟩ := mem_filter.mp ok
    obtain ⟨pm,qm,_,_,_⟩ := mem_ordered.mp ord
    obtain ⟨⟨pl,_⟩,pp⟩ := prime_info pm
    obtain ⟨⟨_,qu⟩,qp⟩ := prime_info qm
    change p < q at pq
    change X ≤ p at pl
    change q < 2*X at qu
    have hx : 7 ≤ X := by unfold X; decide +kernel
    have dp : 2 ∣ p-1 := by obtain ⟨a,ha⟩ := pp.odd_of_ne_two (by omega); exact ⟨a,by omega⟩
    have dq : 2 ∣ q-1 := by obtain ⟨b,hb⟩ := qp.odd_of_ne_two (by omega); exact ⟨b,by omega⟩
    let g := (p-1).gcd (q-1)
    let a := (p-1)/g
    let b := (q-1)/g
    have gv : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.sub_pos_of_lt pp.one_lt)
    obtain ⟨h,gh⟩ : 2 ∣ g := Nat.dvd_gcd dp dq
    have recP : g*a = p-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
    have recQ : g*b = q-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
    have recP' : p = 2*(h*a)+1 := by rw [gh,Nat.mul_assoc] at recP; omega
    have recQ' : q = 2*(h*b)+1 := by rw [gh,Nat.mul_assoc] at recQ; omega
    have ha : 0 < a := by
      by_contra! z
      rw [Nat.eq_zero_of_le_zero z,Nat.mul_zero] at recP
      omega
    have ab : a ≤ b := by
      by_contra! lt
      have hh := Nat.mul_le_mul_left h lt.le
      omega
    have close : b ≤ 2*a := by
      by_contra! lt
      have hh := (Nat.mul_lt_mul_left (by omega : 0 < h)).mpr lt
      rw [show h*(2*a) = 2*(h*a) by ring] at hh
      omega
    have prop : a*b ≤ B := small
    have square : b*b ≤ 2*B := calc
      _ ≤ 2*(a*b) := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right b close
      _ ≤ _ := Nat.mul_le_mul_left 2 prop
    have cap : b ≤ J := by
      by_contra! gt
      have hh : (J+1)*(J+1) ≤ b*b := Nat.mul_le_mul (Nat.succ_le_of_lt gt) (Nat.succ_le_of_lt gt)
      rw [pow_two] at cut
      exact (not_lt_of_ge (hh.trans square)) cut
    have hb := ha.trans_le ab
    refine mem_biUnion.mpr ⟨b,mem_Icc.mpr ⟨hb,cap⟩,mem_image.mpr ⟨(h,a),
      mem_product.mpr ⟨mem_Icc.mpr ⟨by change 1 ≤ h; omega,(Nat.le_div_iff_mul_le hb).mpr ?_⟩,
        mem_Icc.mpr ⟨ha,ab⟩⟩,?_⟩⟩
    · change h*b ≤ X
      omega
    · exact Prod.ext recP'.symm recQ'.symm
  have cnt := card_biUnion_le_card_mul (Icc 1 J) (withLarger X) X (fun b _ => withLarger_card X b)
  exact (card_le_card sub).trans (by simpa only [Nat.card_Icc,Nat.add_sub_cancel,Nat.mul_comm] using cnt)

/-- On an eligible pair, the budget event is equivalent to an actual positive
period of the sampled moment sequence, shared by every starting offset. -/
theorem mem_short_iff {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ok : (p,q) ∈ eligible) (B : ℕ) :
    (p,q) ∈ short B ↔ ∃ t : ℕ, 0 < t ∧ t ≤ B ∧
      JacobiPeriodProbe.AllOffsets (JacobiMomentPeriod.completeEven (p*q)) ((p*q-1)/2) t := by
  have bounds := ok
  rw [eligible,sample] at bounds
  obtain ⟨ord,lt⟩ := mem_filter.mp bounds
  obtain ⟨pm,qm,_,_,_⟩ := mem_ordered.mp ord
  have low : 7 ≤ X := by unfold X; decide +kernel
  have hp : 7 ≤ p := low.trans (prime_info pm).1.1
  have hq : 7 ≤ q := low.trans (prime_info qm).1.1
  have cop := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr
    (show p ≠ q from (show p < q from lt).ne)
  have pg : 0 < p-1 := by omega
  have qg : 0 < q-1 := by omega
  have gpos := Nat.gcd_pos_of_pos_left (q-1) pg
  have positive : 0 < residualProduct p q := Nat.mul_pos
    (Nat.div_pos (Nat.gcd_le_left _ pg) gpos) (Nat.div_pos (Nat.gcd_le_right _ qg) gpos)
  rw [short,mem_filter]
  change (_ ∧ residualProduct p q ≤ B) ↔ _
  constructor
  · rintro ⟨_,small⟩
    exact ⟨_,positive,small,(JacobiPeriodProbe.canonical_period cop hp hq _).mpr dvd_rfl⟩
  · rintro ⟨t,tp,tB,per⟩
    exact ⟨ok,(Nat.le_of_dvd tp ((JacobiPeriodProbe.canonical_period cop hp hq t).mp per)).trans tB⟩

/-- Strict upper fraction in the repository's full-width, sorted prime-pair sample. -/
theorem short_fraction : 2^978 * (short (2^40)).card < eligible.card := by
  have bound := short_card (B:=2^40) (J:=3*2^19) (by decide +kernel)
  have arith : 21000000*(2^978*(X*(3*2^19))) < 2^2046 := by unfold X; decide +kernel
  exact Nat.lt_of_mul_lt_mul_left <| (Nat.mul_le_mul_left 21000000
    (Nat.mul_le_mul_left (2^978) bound)).trans_lt (arith.trans ChebyshevPrimeSample.eligible_count)

end PrimeFactors.JacobiStridePopulation
