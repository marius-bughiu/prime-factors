import PrimeFactors.SquareRootPhasePopulation
import PrimeFactors.FactorClueWidthProfile
import PrimeFactors.OddWidthSumPredictions

/-! An unconditional upper count for pairs realizing an exact dyadic gap
order. For each prime endpoint the other endpoint is in one progression
and avoids all prime divisors of 15015. -/
namespace PrimeFactors.ShiftedSquareSumCoverage

open Finset MixedPrefixSample
open FactorClueWidthProfile (GapAt)
open scoped Classical
open private PrimeFactors.MixedPrefixSample.mem_sample PrimeFactors.MixedPrefixSample.mem_primes
  from PrimeFactors.MixedPrefixSample
open private PrimeFactors.LocalMidpointLanes.odd_square from PrimeFactors.LocalMidpointLanes
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

noncomputable def exact (t : ℕ) := eligible.filter fun z => GapAt z.1 z.2 t

theorem mem_exact {p q t : ℕ} : (p,q)∈exact t ↔ (p,q)∈eligible ∧ GapAt p q t := mem_filter

attribute [local irreducible] eligible primes exact

private theorem flip {p q t : ℕ} (h : GapAt p q t) : GapAt q p t := by
  have eq := h.add_right (2^t)
  change p ≡ q+2^t [MOD 2^(t+1)]
  exact (eq.trans (by simp [Nat.add_assoc,←Nat.two_mul,Nat.pow_succ'])).symm

private abbrev W := 15015

private theorem tot : W.totient=5760 := by
  rw [show W=3*(5*(7*(11*13))) by decide]
  norm_num [Nat.totient_mul (by decide : Nat.Coprime 3 (5*(7*(11*13)))),
    Nat.totient_mul (by decide : Nat.Coprime 5 (7*(11*13))),
    Nat.totient_mul (by decide : Nat.Coprime 7 (11*13)),
    Nat.totient_mul (by decide : Nat.Coprime 11 13), Nat.totient_prime]

private theorem stripe {M r : ℕ} (mp : 0<M) (cop : M.Coprime W) :
    (primes.filter (fun q => q ≡ r [MOD M])).card ≤
      ((X-1)/(M*W)+1)*5760 := by
  let H := M*W
  let code (q : ℕ) := ((q-X)/H,q%W)
  let R := (range W).filter (fun c => W.Coprime c)
  have hp : 0<H := Nat.mul_pos mp (by decide)
  have inside {q : ℕ} (h : q∈primes) :
      (q-X)/H<(X-1)/H+1 ∧ q%W∈R := by
    obtain ⟨⟨lo,hi⟩,pr⟩ := PrimeFactors.MixedPrefixSample.mem_primes.mp h
    have cq := pr.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide : 0<W) ((by decide : W<X).trans_le lo))
    refine ⟨Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)),mem_filter.mpr
      ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),?_⟩⟩
    change W.gcd (q%W)=1
    rw [Nat.gcd_comm,←Nat.gcd_rec]
    exact cq.symm
  have size : (primes.filter (fun q => q ≡ r [MOD M])).card≤
      ((range ((X-1)/H+1)) ×ˢ R).card := by
    apply card_le_card_of_injOn code
    · intro q h
      have pair := inside (mem_filter.mp h).1
      exact mem_product.mpr ⟨mem_range.mpr pair.1,pair.2⟩
    · intro a ha b hb ab
      obtain ⟨pa,ar⟩ := mem_filter.mp ha
      obtain ⟨pb,br⟩ := mem_filter.mp hb
      have la := (PrimeFactors.MixedPrefixSample.mem_primes.mp pa).1.1
      have lb := (PrimeFactors.MixedPrefixSample.mem_primes.mp pb).1.1
      have same : a ≡ b [MOD H] := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp
        ⟨ar.trans br.symm,congrArg Prod.snd ab⟩
      have sub : a-X ≡ b-X [MOD H] := Nat.ModEq.add_left_cancel' X <| by
        simpa [Nat.add_sub_of_le la,Nat.add_sub_of_le lb] using same
      have blocks : (a-X)/H=(b-X)/H := congrArg Prod.fst ab
      have da := Nat.mod_add_div (a-X) H
      have db := Nat.mod_add_div (b-X) H
      change (a-X)%H=(b-X)%H at sub
      rw [blocks,sub] at da
      omega
  simpa only [card_product,card_range,R,←Nat.totient_eq_card_coprime,tot,H] using size

private noncomputable def orderedExact (t : ℕ) :=
  (primes ×ˢ primes).filter (fun z => z.2 ≡ z.1+2^t [MOD 2^(t+1)])

private theorem two_orders_le (t : ℕ) : 2*(exact t).card≤(orderedExact t).card := by
  let S := exact t
  have data {p q : ℕ} (mem : (p,q)∈S) : p∈primes ∧ q∈primes ∧ p<q ∧ GapAt p q t := by
    obtain ⟨inSample,gap⟩ := mem_exact.mp mem
    rw [eligible] at inSample
    obtain ⟨both,lt⟩ := PrimeFactors.MixedPrefixSample.mem_sample.mp inSample
    have fields := MixedPrefixSample.mem_ordered.mp both
    exact ⟨fields.1,fields.2.1,lt,gap⟩
  have dis : Disjoint S (S.image Prod.swap) := disjoint_left.mpr (by
    rintro ⟨p,q⟩ hp hq
    obtain ⟨⟨a,b⟩,hab,sw⟩ := mem_image.mp hq
    have left := data hp
    have right := data hab
    cases sw
    omega)
  have sub : S ∪ S.image Prod.swap ⊆ orderedExact t := by
    rintro ⟨p,q⟩ h
    rcases mem_union.mp h with mem|mem
    · have a := data mem
      exact mem_filter.mpr ⟨mem_product.mpr ⟨a.1,a.2.1⟩,a.2.2.2⟩
    · obtain ⟨⟨a,b⟩,hab,sw⟩ := mem_image.mp mem
      have info := data hab
      cases sw
      exact mem_filter.mpr ⟨mem_product.mpr ⟨info.2.1,info.1⟩,flip info.2.2.2⟩
  simpa only [card_union_of_disjoint dis,card_image_of_injective _ Prod.swap_injective,
    ←two_mul,S] using card_le_card sub

/-- Uniform bound on the number of pairs of each exact gap order. The
last, possibly incomplete block is charged as a whole coprime residue table. -/
theorem count (t : ℕ) : 2*(exact t).card≤
    primes.card*(((X-1)/(2^(t+1)*15015)+1)*5760) := by
  have rows (S : Finset ℕ) : ((S ×ˢ S).filter (fun z => z.2 ≡ z.1+2^t [MOD 2^(t+1)])).card=
      ∑ p∈S,(S.filter (fun q => q ≡ p+2^t [MOD 2^(t+1)])).card := by
    simp only [card_filter,sum_product]
  apply (two_orders_le t).trans
  rw [orderedExact,rows]
  apply (sum_le_sum (fun p (_ : p∈primes) => stripe (r:=p+2^t) (by positivity : 0<(2:ℕ)^(t+1))
    ((by decide : Nat.Coprime 2 W).pow_left (t+1)))).trans_eq
  simp

/-- Fewer than one pair in 2^500 has exact gap order 512. The prime-count
normalization is unconditional and the denominator includes every eligible
unordered pair. -/
theorem rare : 2^500*(exact 512).card<eligible.card := by
  have slots : 2^500*(((X-1)/(2^(512+1)*15015)+1)*5760)*41056≤2*X := by decide +kernel
  have marginal := SquareRootPhasePopulation.marginal
  have bound := count 512
  have calc1 := Nat.mul_le_mul_left (2^500*41056) bound
  have calc2 := Nat.mul_le_mul_right primes.card slots
  have calc3 := Nat.mul_lt_mul_of_pos_left marginal (by decide : 0<2)
  nlinarith only [calc1,calc2,calc3]

private theorem signed_gap {p q t : ℕ} :
    GapAt p q t ↔ ∃ g : ℤ, Odd g ∧ (q:ℤ)-p=2^t*g := by
  have cast : GapAt p q t ↔ (q:ℤ) ≡ p+2^t [ZMOD (2:ℤ)^(t+1)] := by
    unfold GapAt
    exact_mod_cast (Int.natCast_modEq_iff (a:=q) (b:=p+2^t) (n:=2^(t+1))).symm
  rw [cast]
  constructor
  · intro eq
    obtain ⟨w,hw⟩ := Int.modEq_iff_dvd.mp eq.symm
    refine ⟨2*w+1,⟨w,rfl⟩,?_⟩
    rw [pow_succ] at hw
    linear_combination hw
  · rintro ⟨g,⟨w,hw⟩,hg⟩
    apply Int.ModEq.symm
    apply Int.modEq_iff_dvd.mpr
    refine ⟨w,?_⟩
    rw [hw] at hg
    rw [pow_succ]
    linear_combination hg

/-- The shifted-square guesses are defined for the square unit class modulo
eight. Every other residue class is counted as a miss. -/
noncomputable def successes (j : ℕ) := eligible.filter fun v =>
  (v.1:ℤ)*v.2 ≡ 1 [ZMOD 8] ∧ OddWidthSumPredictions.predicts ((v.1:ℤ)*v.2) ((v.1:ℤ)+v.2) j

theorem successes_eq {j : ℕ} (hj : 2≤j) : successes j=exact (j+1) := by
  ext ⟨p,q⟩
  rw [successes,mem_filter,mem_exact]
  apply and_congr_right
  intro ok
  rw [eligible] at ok
  have both := MixedPrefixSample.mem_ordered.mp (PrimeFactors.MixedPrefixSample.mem_sample.mp ok).1
  have prime_odd (x : ℕ) (inside : x∈primes) : Odd (x:ℤ) := by
    obtain ⟨⟨lo,_⟩,pr⟩ := PrimeFactors.MixedPrefixSample.mem_primes.mp inside
    exact_mod_cast pr.odd_of_ne_two ((by decide : 2<X).trans_le lo).ne'
  have op := prime_odd p both.1
  have oq := prime_odd q both.2.1
  rw [signed_gap]
  constructor
  · rintro ⟨gate,hit⟩
    exact (OddWidthSumPredictions.true_iff hj op oq gate).mp hit
  · rintro ⟨g,og,gap⟩
    have div : (8:ℤ)∣(q:ℤ)-p :=
      (pow_dvd_pow (2:ℤ) (by omega : 3≤j+1)).trans ⟨g,gap⟩
    have eq : (p:ℤ) ≡ q [ZMOD 8] := Int.modEq_iff_dvd.mpr div
    have sq : (p:ℤ)*p ≡ 1 [ZMOD 8] :=
      (Int.modEq_iff_dvd.mpr (by simpa [pow_two] using PrimeFactors.LocalMidpointLanes.odd_square op)).symm
    have gate := (eq.symm.mul_left (p:ℤ)).trans sq
    exact ⟨gate,(OddWidthSumPredictions.true_iff hj op oq gate).mpr ⟨g,og,gap⟩⟩

attribute [local irreducible] successes
/-- Two sum guesses at precision 2·511+3=1025 use the exact-order-512 event. -/
theorem full_width : 2^500*(successes 511).card<eligible.card := by
  have same := (successes_eq (by decide : 2≤511)).trans (congrArg exact (by decide : 511+1=512))
  exact lt_of_eq_of_lt (congrArg (fun S : Finset (ℕ×ℕ) => 2^500*S.card) same) rare

end PrimeFactors.ShiftedSquareSumCoverage
