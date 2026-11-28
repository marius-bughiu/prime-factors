import PrimeFactors.FiniteBinCollisionPopulation
import PrimeFactors.CyclotomicCoefficientProbePopulation
import PrimeFactors.SquareRootPhasePopulation

/-! Count actual full-width prime pairs for which a *common* rectangle places
both primes just above its threshold. Its shape may depend on the entire pair.
Upper bounds allow the wider strip on either side. A separate lower bound
groups primes into actual rectangles and counts pairs in the same group. -/
namespace PrimeFactors.CircleMarkRationalBoundaryPopulation

open Finset MixedPrefixSample
open private PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info
  PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info from PrimeFactors.CyclotomicCoefficientProbePopulation
open private PrimeFactors.FiniteBinCollisionPopulation.upper_eligible
  PrimeFactors.FiniteBinCollisionPopulation.collision_bound
  PrimeFactors.FiniteBinCollisionPopulation.price from PrimeFactors.FiniteBinCollisionPopulation
open private PrimeFactors.FirstSumMenuPopulation.collision_count
  PrimeFactors.FirstSumMenuPopulation.prime_pairs from PrimeFactors.FirstSumMenuPopulation
open private PrimeFactors.MonotoneClosePrimeLower.prime_ratio from PrimeFactors.MonotoneClosePrimeLower
open private PrimeFactors.MixedPrefixSample.mem_upper from PrimeFactors.MixedPrefixSample

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192
attribute [local irreducible] eligible primes upperPrimes

/-- The positive shortfall for the exact divisor count at one prime. -/
abbrev Above (H D x : ℕ) : Prop :=
  (H+1)*(D+1)<x ∧ x≤(H+1)*(D+1)+min H D

/-- Allow the same width also below the boundary. -/
def Near (H D x : ℕ) : Prop :=
  (H+1)*(D+1)≤x+min H D ∧ x≤(H+1)*(D+1)+min H D

/-- Count every eligible pair once, whatever rectangles witness its inclusion. -/
noncomputable def pairs (region : ℕ→ℕ→ℕ→Prop) : Finset (ℕ×ℕ) := by
  classical
  exact eligible.filter fun z => ∃ H D, region H D z.1 ∧ region H D z.2

theorem mem_pairs {region : ℕ→ℕ→ℕ→Prop} {p q : ℕ} :
    (p,q)∈pairs region ↔ (p,q)∈eligible ∧ ∃ H D, region H D p ∧ region H D q := by
  classical exact mem_filter

private theorem width {H D p : ℕ} (hit : Near H D p) (hi : p<2^1024) : min H D<2^512 := by
  let k := min H D
  have square : (k+1)*(k+1)≤(H+1)*(D+1) :=
    Nat.mul_le_mul (Nat.add_le_add_right (min_le_left ..) 1) (Nat.add_le_add_right (min_le_right ..) 1)
  have lower := hit.1
  change (H+1)*(D+1)≤p+k at lower
  have small : k^2<p := by nlinarith only [square,lower,Nat.zero_le k]
  have atWidth : (2:ℕ)^1024=(2^512)^2 := by decide +kernel
  rw [atWidth] at hi
  exact lt_of_not_ge fun no => (not_lt_of_ge (Nat.pow_le_pow_left no 2)) (small.trans hi)

private theorem gaps (S : Finset (ℕ×ℕ)) (G : ℕ) (sub : S⊆eligible)
    (bound : ∀ z∈S, z.2-z.1<2*G) : S.card≤primes.card*G := by
  let code (z : ℕ×ℕ) := (z.1,(z.2-z.1)/2)
  have into (z : ℕ×ℕ) (h : z∈S) : code z ∈ primes ×ˢ range G :=
    mem_product.mpr ⟨(PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info (sub h)).1,
      mem_range.mpr (by have := bound z h; dsimp [code]; omega)⟩
  have inject (z : ℕ×ℕ) (h : z∈S) (w : ℕ×ℕ) (hw : w∈S) (eqn : code z=code w) : z=w := by
    have first := congrArg Prod.fst eqn
    change z.1=w.1 at first
    have second : (z.2-z.1)/2=(w.2-w.1)/2 := congrArg Prod.snd eqn
    obtain ⟨_,q,o⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info (sub h)
    obtain ⟨_,r,t⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info (sub hw)
    have qo := (PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info q).2.2.2
    have ro := (PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info r).2.2.2
    exact Prod.ext first (by omega)
  simpa only [card_product,card_range] using card_le_card_of_injOn code into inject

private theorem price_gap {S : Finset (ℕ×ℕ)} {G m : ℕ} (bound : S.card≤primes.card*G)
    (fit : 41056*m*G≤X) : m*S.card<eligible.card := by
  apply Nat.lt_of_mul_lt_mul_left (a:=41056)
  calc
    41056*(m*S.card) ≤ 41056*(m*(primes.card*G)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ bound)
    _ = (41056*m*G)*primes.card := by ring
    _ ≤ X*primes.card := Nat.mul_le_mul_right _ fit
    _ < _ := SquareRootPhasePopulation.marginal

/-- The rectangle can be chosen after seeing even the two hidden primes. -/
theorem upper : 2^496*(pairs Above).card<eligible.card := by
  apply price_gap (G:=2^511) _ (by decide +kernel)
  apply gaps _ _ (fun _ h => (mem_pairs.mp h).1)
  rintro ⟨p,q⟩ mem
  obtain ⟨pair,H,D,left,right⟩ := mem_pairs.mp mem
  have pi := (PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info
    (PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info pair).1).2.1
  have hi : p<2^1024 := pi
  have wid := width (H:=H) (D:=D) (p:=p) ⟨by have := left.1; omega,left.2⟩ hi
  have lo := left.1
  have up := right.2
  change q-p<2*2^511
  omega

/-- The two primes may approach the boundary from opposite sides as well. -/
theorem symmetric_upper : 2^495*(pairs Near).card<eligible.card := by
  apply price_gap (G:=2^512) _ (by decide +kernel)
  apply gaps _ _ (fun _ h => (mem_pairs.mp h).1)
  rintro ⟨p,q⟩ mem
  obtain ⟨pair,H,D,left,right⟩ := mem_pairs.mp mem
  have hi : p<2^1024 := (PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info
    (PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info pair).1).2.1
  have wid := width left hi
  have lo := left.1
  have up := right.2
  change q-p<2*2^512
  omega

/-- Group primes using a fixed side length W-1. The opposite side is the
quotient minus one, shared by every prime in the same bin. -/
theorem bin_above {p W : ℕ} (pr : p.Prime) (two : 2≤W) (size : W^2≤p) :
    Above (W-1) (p/W-1) p := by
  have wp : 0<W := by omega
  have quo : W≤p/W := (Nat.le_div_iff_mul_le wp).mpr (by simpa only [pow_two] using size)
  have lt : W<p := by nlinarith only [two,size]
  have nonzero : p%W≠0 := fun h => (pr.eq_one_or_self_of_dvd _ (Nat.dvd_of_mod_eq_zero h)).elim
    (by omega) (by omega)
  have eqn := Nat.div_add_mod p W
  have rem := Nat.mod_lt p wp
  unfold Above
  rw [Nat.sub_add_cancel (show 1≤W by omega),Nat.sub_add_cancel (show 1≤p/W by omega),
    min_eq_left (by omega : W-1≤p/W-1)]
  omega

/-- Every full-width prime individually has a well-shaped rectangle. The
quotient here uses that prime. A common public rectangle requires more. -/
theorem every_prime {p : ℕ} (pm : p∈primes) :
    Above (2^511-1) (p/2^511-1) p := by
  obtain ⟨lo,_,pr,_⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info pm
  exact bin_above pr (by decide +kernel) ((by decide +kernel : (2^511)^2≤X).trans lo)

/-- Width fixed across the entire population for the constructive lower bound. -/
abbrev W : ℕ := 3*2^510

/-- A single rectangle chosen from the product alone. -/
noncomputable def selected : Finset (ℕ×ℕ) :=
  eligible.filter fun z => Above (W-1) ((z.1*z.2).sqrt/W-1) z.1 ∧
    Above (W-1) ((z.1*z.2).sqrt/W-1) z.2

theorem selected_sub : selected⊆pairs Above := by
  intro z h
  obtain ⟨pair,hit⟩ := mem_filter.mp h
  exact mem_pairs.mpr ⟨pair,_,_,hit⟩

private abbrev start : ℕ := (283*X/200)/W
private abbrev numBins : ℕ := (2*X-1)/W-start+1
private def key (p : ℕ) := p/W-start

private theorem upper_data {p : ℕ} (mem : p∈upperPrimes) :
    p.Prime ∧ W^2≤p ∧ start≤p/W ∧ p/W≤(2*X-1)/W := by
  obtain ⟨pm,low⟩ := PrimeFactors.MixedPrefixSample.mem_upper.mp mem
  obtain ⟨_,hi,pr,_⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info pm
  have floor : 283*X/200≤p := by omega
  exact ⟨pr,(by decide +kernel : W^2≤283*X/200).trans floor,
    Nat.div_le_div_right floor,Nat.div_le_div_right (by omega)⟩

/-- Actual pairs of upper-interval primes sharing a bin give a lower bound.
No assumption on the distribution of primes among these bins is used. -/
theorem selected_lower : eligible.card<2^516*selected.card := by
  have bounded (p : ℕ) (pm : p∈upperPrimes) : key p<numBins := by
    obtain ⟨_,_,lo,hi⟩ := upper_data pm
    unfold key numBins
    omega
  have covers (p : ℕ) (pm : p∈upperPrimes) (q : ℕ) (qm : q∈upperPrimes)
      (ord : p<q) (same : key p=key q) : (p,q)∈selected := by
    obtain ⟨pp,pbig,pl,_⟩ := upper_data pm
    obtain ⟨qp,qbig,ql,_⟩ := upper_data qm
    have eqn : p/W=q/W := by unfold key at same; omega
    have lo : p≤(p*q).sqrt := by
      simpa only [Nat.sqrt_eq] using Nat.sqrt_le_sqrt (Nat.mul_le_mul_left p ord.le)
    have hi : (p*q).sqrt≤q := by
      simpa only [Nat.sqrt_eq] using Nat.sqrt_le_sqrt (Nat.mul_le_mul_right q ord.le)
    have publicBin : (p*q).sqrt/W=p/W := le_antisymm ((Nat.div_le_div_right hi).trans_eq eqn.symm)
      (Nat.div_le_div_right lo)
    refine mem_filter.mpr ⟨PrimeFactors.FiniteBinCollisionPopulation.upper_eligible pm qm ord,?_⟩
    change Above (W-1) ((p*q).sqrt/W-1) p ∧ Above (W-1) ((p*q).sqrt/W-1) q
    rw [publicBin]
    exact ⟨bin_above pp (by decide +kernel) pbig,eqn.symm ▸ bin_above qp (by decide +kernel) qbig⟩
  have lowerCount := ChebyshevPrimeSample.prime_count
  change 11*X<35500*(upperPrimes.card-1) at lowerCount
  have many : 1000*numBins≤upperPrimes.card := by
    have room : 35500*(1000*numBins)≤11*X := by decide +kernel
    omega
  have coll := PrimeFactors.FirstSumMenuPopulation.collision_count upperPrimes key numBins bounded
  have cap := PrimeFactors.FiniteBinCollisionPopulation.collision_bound _ selected upperPrimes key rfl covers
  have count := PrimeFactors.FiniteBinCollisionPopulation.price (coll.trans (Nat.mul_le_mul_left _ cap)) many
    PrimeFactors.MonotoneClosePrimeLower.prime_ratio PrimeFactors.FirstSumMenuPopulation.prime_pairs
  exact count.trans_le (Nat.mul_le_mul_right _ (by decide +kernel : 40*numBins≤2^516))

/-- Even after allowing arbitrary shapes, the probability of the common
positive strip remains within these two unconditional bounds. -/
theorem frequency : eligible.card<2^516*(pairs Above).card ∧ 2^496*(pairs Above).card<eligible.card :=
  ⟨selected_lower.trans_le (Nat.mul_le_mul_left _ (card_le_card selected_sub)),upper⟩

/-- A rectangle fixed once for the entire population, independently of each product. -/
noncomputable def fixed (H D : ℕ) : Finset (ℕ×ℕ) :=
  eligible.filter fun z => Above H D z.1 ∧ Above H D z.2

private theorem fixed_count (S : Finset (ℕ×ℕ)) (C G : ℕ)
    (data : ∀ z∈S, C<z.1 ∧ z.1<C+2*G ∧ C<z.2 ∧ z.2<C+2*G ∧ z.1%2=1 ∧ z.2%2=1) :
    S.card≤G*G := by
  let digit (r : ℕ) := (r-(C+1))/2
  let code (z : ℕ×ℕ) := (digit z.1,digit z.2)
  have into (z : ℕ×ℕ) (h : z∈S) :
      code z∈range G ×ˢ range G := by
    obtain ⟨a,b,c,d,_,_⟩ := data z h
    apply mem_product.mpr
    simp only [code,digit,mem_range]
    omega
  have inj (z : ℕ×ℕ) (h : z∈S) (w : ℕ×ℕ) (hw : w∈S)
      (eqn : code z=code w) : z=w := by
    have first := congrArg Prod.fst eqn
    have second := congrArg Prod.snd eqn
    dsimp [code,digit] at first second
    obtain ⟨a,_,c,_,po,qo⟩ := data z h
    obtain ⟨e,_,g,_,uo,vo⟩ := data w hw
    exact Prod.ext (by omega) (by omega)
  simpa only [card_product,card_range] using card_le_card_of_injOn code into inj

theorem fixed_upper (H D : ℕ) : 2^999*(fixed H D).card<eligible.card := by
  let C := (H+1)*(D+1)
  have count := fixed_count (fixed H D) C (2^511) (fun z m => by
    rw [fixed,mem_filter] at m
    obtain ⟨em,left,right⟩ := m
    obtain ⟨pm,qm,_⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info em
    obtain ⟨_,hi,_,od⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info pm
    have w := width (H:=H) (D:=D) (p:=z.1) ⟨by have := left.1; omega,left.2⟩ hi
    have wid : min H D<2*2^511 := w.trans_eq (by decide +kernel)
    have front : C+min H D<C+2*2^511 := Nat.add_lt_add_left wid C
    exact ⟨left.1,left.2.trans_lt front,right.1,right.2.trans_lt front,od,
      (PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info qm).2.2.2⟩)
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ count)).trans_lt
    ((by decide +kernel : 21000000*(2^999*(2^511*2^511))<2^2046).trans ChebyshevPrimeSample.eligible_count)

/-- The public square-root choice moves the boundary and covers far more
products than *every* one fixed shape for this two-prime incidence event. -/
theorem adaptation_gain (H D : ℕ) : 2^483*(fixed H D).card<selected.card := by
  apply Nat.lt_of_mul_lt_mul_left (a:=2^516)
  rw [←Nat.mul_assoc,←pow_add]
  exact (fixed_upper H D).trans selected_lower

end PrimeFactors.CircleMarkRationalBoundaryPopulation
