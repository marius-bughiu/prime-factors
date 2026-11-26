import PrimeFactors.SquareRootPolynomialFormula
import PrimeFactors.BlockProbePopulation

/-! Population bound for gcds of fixed integer polynomials in N and floor(sqrt N).
It charges exceptional primes dividing the integer content of the specialization. -/

namespace PrimeFactors.SquareRootFormulaPopulation

open Finset SquareRootPolynomialFormula MixedPrefixSample
open scoped Polynomial

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

noncomputable def exceptions (c : ℤ) : Finset ℕ := by
  classical exact primes.filter fun p => (p : ℤ) ∣ c

noncomputable def exceptionalPairs (c : ℤ) : Finset (ℕ×ℕ) :=
  ((exceptions c) ×ˢ primes).image fun z => (min z.1 z.2, max z.1 z.2)

noncomputable def splits (F : Formula) : Finset (ℕ×ℕ) := by
  classical
  exact eligible.filter fun z =>
    let n := z.1*z.2
    let g := Int.gcd (value F n n.sqrt) n
    1 < g ∧ g < n

private theorem prime_mem {p : ℕ} (mem : p ∈ primes) : p.Prime :=
  (mem_filter.mp mem).2

attribute [local irreducible] X primes eligible ordered sample

theorem exception_bits {c : ℤ} {L : ℕ} (nz : c ≠ 0) (size : c.natAbs < 2^L) :
    1023*(exceptions c).card < L := by
  let S := exceptions c
  have div := Finset.prod_primes_dvd (s:=S) c.natAbs
    (fun p hp => Nat.prime_iff.mp (prime_mem (mem_filter.mp hp).1))
    (fun p hp => by simpa only [Int.natAbs_natCast] using
      Int.natAbs_dvd_natAbs.mpr (mem_filter.mp hp).2)
  have lo : X^S.card ≤ ∏ p ∈ S, p := by
    apply Finset.pow_card_le_prod
    intro p hp
    have inside : p ∈ primes := (mem_filter.mp hp).1
    rw [primes] at inside
    exact (mem_Ico.mp (mem_filter.mp inside).1).1
  have bound := lo.trans_lt ((Nat.le_of_dvd (Int.natAbs_pos.mpr nz) div).trans_lt size)
  rw [X, ← pow_mul] at bound
  exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp bound

theorem exception_pair_count (c : ℤ) :
    (exceptionalPairs c).card ≤ primes.card*(exceptions c).card := by
  exact card_image_le.trans (by rw [card_product, Nat.mul_comm])

/-- Either the content already names one prime, or the public square root is
a root of the same primitive polynomial for that prime. -/
theorem cover (F : Formula) :
    splits F ⊆ (SquareRootShiftPartners.detected (residues (specialized F).primPart) ∩ eligible)
      ∪ exceptionalPairs (specialized F).content := by
  classical
  rintro ⟨p,q⟩ hm
  obtain ⟨mem,hg,_⟩ := mem_filter.mp hm
  have geometry := mem
  change (p,q)∈eligible at geometry
  rw [eligible,sample] at geometry
  obtain ⟨ord,lt⟩ := mem_filter.mp geometry
  obtain ⟨pm,qm,_,_,_⟩ := (mem_ordered (E:=fun _ => True) (z:=(p,q))).mp ord
  have pp := prime_mem pm
  have qp := prime_mem qm
  let n := p*q
  let c := (specialized F).content
  have found := BlockProbePopulation.prime_dvd_reading pp qp (value F n n.sqrt) hg
  rw [mem_union]
  rcases found with localP | localQ
  · by_cases bad : (p:ℤ) ∣ c
    · right
      apply mem_image.mpr
      exact ⟨(p,q), mem_product.mpr ⟨mem_filter.mpr ⟨pm,bad⟩,qm⟩,
        Prod.ext (min_eq_left lt.le) (max_eq_right lt.le)⟩
    · left
      refine mem_inter.mpr ⟨BlockProbePopulation.mem_detected _ mem (Or.inl ?_),mem⟩
      have h := hit pp (Nat.dvd_mul_right p q) F
        (fun h => bad ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp h)) (n.sqrt : ℤ)
        ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr localP)
      simpa only [Int.cast_natCast] using h
  · by_cases bad : (q:ℤ) ∣ c
    · right
      apply mem_image.mpr
      exact ⟨(q,p),mem_product.mpr ⟨mem_filter.mpr ⟨qm,bad⟩,pm⟩,
        Prod.ext (min_eq_right lt.le) (max_eq_left lt.le)⟩
    · left
      refine mem_inter.mpr ⟨BlockProbePopulation.mem_detected _ mem (Or.inr ?_),mem⟩
      have h := hit qp (Nat.dvd_mul_left q p) F
        (fun h => bad ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp h)) (n.sqrt : ℤ)
        ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr localQ)
      simpa only [Int.cast_natCast] using h

/-- No residue equidistribution assumption is made. -/
theorem count (F : Formula) :
    (splits F).card ≤ primes.card*
      (2*(specialized F).natDegree+(exceptions (specialized F).content).card) := by
  let P := specialized F
  have rootCount := BlockProbePopulation.residue_count (residues P.primPart) (D:=P.natDegree)
    (fun p hp => (residues_card P.primPart (prime_mem hp)).trans_eq P.natDegree_primPart)
  exact (card_le_card (cover F)).trans ((card_union_le _ _).trans ((Nat.add_le_add rootCount
    (exception_pair_count P.content)).trans_eq (Nat.mul_add ..).symm))

/-- A single finite numerical comparison applies directly to any formula in this
class, with its fixed exceptional primes charged by their total bit length. -/
theorem dyadic_bound (F : Formula) {K D E : ℕ} (degree : (specialized F).natDegree ≤ D)
    (extra : (exceptions (specialized F).content).card ≤ E) (pos : 0<2*D+E)
    (scale : 2^K*(41056*(2*D+E)) ≤ X) :
    2^K*(splits F).card < eligible.card := by
  have cap := (count F).trans (Nat.mul_le_mul_left primes.card
    (Nat.add_le_add (Nat.mul_le_mul_left 2 degree) extra))
  have h := (Nat.mul_le_mul_left X cap).trans_lt
    (by simpa only [← Nat.mul_assoc] using
      Nat.mul_lt_mul_of_pos_right SquareRootPhasePopulation.marginal pos)
  apply Nat.lt_of_mul_lt_mul_left (a:=41056*(2*D+E))
  calc
    _ = (2^K*(41056*(2*D+E)))*(splits F).card := by ac_rfl
    _ ≤ X*(splits F).card := Nat.mul_le_mul_right _ scale
    _ < _ := by simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- The prime divisors of the content also divide every nonzero coefficient,
so a bound on the bit length of just one such coefficient suffices. -/
theorem content_bound (P : ℤ[X]) (i : ℕ) (nz : P.coeff i ≠ 0) :
    P.content ≠ 0 ∧ P.content.natAbs ≤ (P.coeff i).natAbs := by
  have d : P.content ∣ P.coeff i := (Polynomial.C_dvd_iff_dvd_coeff ..).mp P.C_content_dvd i
  exact ⟨fun h => nz (by simpa [h] using d),
    Nat.le_of_dvd (Int.natAbs_pos.mpr nz) (Int.natAbs_dvd_natAbs.mpr d)⟩

/-- Degree up to four billion, with one nonzero coefficient fitting in a
mebibit. The other integer coefficients and the outer degree can be arbitrary. -/
theorem four_billion (F : Formula) (degree : (specialized F).natDegree ≤ 2^32)
    (i : ℕ) (nz : (specialized F).coeff i ≠ 0)
    (size : ((specialized F).coeff i).natAbs < 2^1048576) :
    2^974*(splits F).card < eligible.card := by
  obtain ⟨cn,cs⟩ := content_bound (specialized F) i nz
  have bits := exception_bits cn (cs.trans_lt size)
  apply dyadic_bound F (D:=2^32) (E:=1025) degree (by omega) (by decide)
  rw [MixedPrefixSample.X]
  decide +kernel

theorem zero_splits (F : Formula) (zero : specialized F = 0) : splits F = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_not_mem
  intro z hz
  let n := z.1*z.2
  let a := value F n n.sqrt
  obtain ⟨_,hpos,hlt⟩ := mem_filter.mp hz
  have dn : n ∣ a.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (whole_of_zero F zero n n.sqrt)
  have dg : n ∣ Int.gcd a n := by simpa only [Int.gcd, Int.natAbs_natCast] using Nat.dvd_gcd dn (dvd_refl n)
  exact Nat.not_le_of_lt hlt (Nat.le_of_dvd (by omega) dg)

/-- Selecting a formula from a previously fixed menu after seeing the entire
input cannot exceed the union of the same menu's successful pairs. -/
theorem billion_choices {ι : Type*} (M : Finset ι) (F : ι → Formula)
    (ne : M.Nonempty) (budget : M.card ≤ 2^30)
    (small : ∀ j ∈ M, let P := specialized (F j)
      P = 0 ∨ P.natDegree ≤ 2^32 ∧ ∃ i, P.coeff i ≠ 0 ∧ (P.coeff i).natAbs < 2^1048576) :
    2^944 * (M.biUnion fun j => splits (F j)).card < eligible.card := by
  classical
  have one (j) (h : j∈M) : 2^974*(splits (F j)).card < eligible.card := by
    rcases small j h with zero | ⟨degree,i,nz,size⟩
    · rw [zero_splits _ zero,card_empty,Nat.mul_zero]
      have m := SquareRootPhasePopulation.marginal
      by_contra! empty
      rw [show eligible.card = 0 by omega,Nat.mul_zero] at m
      omega
    · exact four_billion _ degree i nz size
  have H : 2^974 * (M.biUnion fun j => splits (F j)).card < M.card*eligible.card := calc
    _ ≤ 2^974*∑ j ∈ M, (splits (F j)).card := Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ j ∈ M, 2^974*(splits (F j)).card := Finset.mul_sum ..
    _ < ∑ _j ∈ M, eligible.card := Finset.sum_lt_sum_of_nonempty ne one
    _ = _ := by simp
  apply Nat.lt_of_mul_lt_mul_left (a:=2^30)
  calc
    _ = 2^974*(M.biUnion fun j => splits (F j)).card := by rw [← Nat.mul_assoc]; rfl
    _ < _ := H.trans_le (Nat.mul_le_mul_right _ budget)

end PrimeFactors.SquareRootFormulaPopulation
