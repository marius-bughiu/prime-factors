import PrimeFactors.DecreasingSumChains
import PrimeFactors.MonotoneSumExtension
import PrimeFactors.SeparatedMonotonePopulation
import PrimeFactors.FactorSum

/-! Increasing products can have successively smaller prime sums over a
long chain, even with the bit lengths and a minimum prime gap fixed. -/
namespace PrimeFactors.PrimeSumOrderReversals

open Finset MixedPrefixSample MonotoneSumExtension DecreasingSumChains
open private PrimeFactors.MixedPrefixSample.mem_sample PrimeFactors.MixedPrefixSample.mem_primes
  from PrimeFactors.MixedPrefixSample

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible primes ordered sample SeparatedMonotonePopulation.far
  SeparatedMonotonePopulation.agreement

abbrev prodOf (z : ℕ×ℕ) := z.1*z.2
abbrev sumOf (z : ℕ×ℕ) := z.1+z.2

private theorem prime_data {z : ℕ×ℕ} (hz : z∈eligible) :
    z.1.Prime ∧ z.2.Prime ∧ z.1<z.2 := by
  rw [eligible] at hz
  obtain ⟨ordered,lt⟩ := PrimeFactors.MixedPrefixSample.mem_sample.mp hz
  obtain ⟨p,q,_,_,_⟩ := mem_ordered.mp ordered
  exact ⟨(PrimeFactors.MixedPrefixSample.mem_primes.mp p).2,
    (PrimeFactors.MixedPrefixSample.mem_primes.mp q).2,lt⟩

private theorem unique_on (P : Finset (ℕ×ℕ))
    (data : ∀ z∈P, z.1.Prime ∧ z.2.Prime ∧ z.1<z.2) :
    (P : Set (ℕ×ℕ)).InjOn prodOf := by
  intro x hx y hy equal
  obtain ⟨xp,_,xs⟩ := data x hx
  obtain ⟨yp,yq,ys⟩ := data y hy
  obtain ⟨a,b⟩ := ordered_semiprime_pair_unique yp yq ys.le xs.le xp.one_lt equal
  exact Prod.ext a b

theorem prod_unique : (eligible : Set (ℕ×ℕ)).InjOn prodOf :=
  unique_on eligible (fun _ hz => prime_data hz)

/-- A uniform strict frequency bound for every monotone predictor forces
an order-reversing chain longer than the reciprocal fraction. -/
theorem chain_of_fraction {α : Type*} (P : Finset α) (n s : α → ℕ)
    (unique : (P : Set α).InjOn n) (L : ℕ) (pos : 0<L)
    (bound : ∀ g : ℕ→ℕ, Monotone g → L*(exactHits P n s g).card<P.card) :
    ∃ xs, L<xs.length ∧ ChainIn P n s xs := by
  classical
  haveI : NeZero L := ⟨pos.ne'⟩
  rcases chain_or_ordered_layers P n s L unique with done|layers
  · exact done
  obtain ⟨layer,cover,order⟩ := layers
  have inside (i : Fin L) (_ : i∈univ) : layer i⊆P := by
    intro z hz
    rw [cover]
    exact mem_biUnion.mpr ⟨i,mem_univ _,hz⟩
  have less := scaled_union_lt univ univ_nonempty layer inside (fun i _ => order i) bound
  rw [←cover,card_univ,Fintype.card_fin] at less
  exact (Nat.lt_irrefl _ less).elim

private theorem hits_subset {α : Type*} (P Q : Finset α) (g : ℕ → ℕ)
    (input : α → ℕ) (value : α → ℕ)
    (into : ∀ z∈P, g (input z)=value z → z∈Q) : exactHits P input value g ⊆ Q := by
  intro z hz
  exact into z (mem_filter.mp hz).1 (mem_filter.mp hz).2

private theorem hits_in_agreement (g : ℕ → ℕ) :
    exactHits SeparatedMonotonePopulation.far prodOf sumOf g ⊆
      SeparatedMonotonePopulation.agreement g 0 := by
  apply hits_subset _ _ g
  intro z hz fit
  apply SeparatedMonotonePopulation.mem_agreement.mpr
  exact ⟨hz,by simpa only [Nat.add_zero] using fit.le,
    by simpa only [Nat.add_zero] using fit.ge⟩

/-- More than 2^979 products in strictly increasing order with strictly
decreasing prime sums. Every pair belongs to the same gap-separated
subpopulation of the full-width study. -/
theorem long_chain :
    ∃ xs, 2^979<xs.length ∧ ChainIn SeparatedMonotonePopulation.far prodOf sumOf xs := by
  apply chain_of_fraction _ _ _ (unique_on _ fun _ hz =>
    prime_data (SeparatedMonotonePopulation.mem_far.mp hz).1) _ (by positivity)
  intro g mono
  exact (Nat.mul_le_mul_left _ (card_le_card (hits_in_agreement g))).trans_lt
    (SeparatedMonotonePopulation.exact_fraction g mono)

/-- Five pairs of eight-bit primes. Their products are sixteen bits long.
Sorting these five products in increasing order strictly decreases the sums. -/
theorem small_chain :
    let xs : List (ℕ×ℕ) := [(131,251),(137,241),(149,227),(163,211),(173,199)]
    xs.map prodOf=[32881,33017,33823,34393,34427] ∧
    xs.map sumOf=[382,378,376,374,372] ∧
    xs.Pairwise (Before prodOf sumOf) ∧
    xs.all (fun z => decide (z.1.Prime ∧ z.2.Prime ∧
      2^7≤z.1 ∧ z.1<z.2 ∧ z.2<2^8 ∧ 2^15≤prodOf z ∧ prodOf z<2^16)) := by
  unfold Before
  decide +kernel

end PrimeFactors.PrimeSumOrderReversals
