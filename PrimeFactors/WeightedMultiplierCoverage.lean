import PrimeFactors.WeightedMultiplierFiber
import PrimeFactors.FactorSum

/-! Coverage of two weighted square excesses on the actual population of
distinct 1,024-bit prime pairs with a 2,048-bit product. The multipliers
and labels can be chosen afresh for each product. -/
namespace PrimeFactors.WeightedMultiplierCoverage
open Finset WeightedMultiplierPopulation WeightedMultiplierFiber

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

/-- Both public labels lie in the designated windows and the product of
their excesses is a square. We even count a minus gcd equal to one. -/
def Reached (k b n : ℕ) : Prop :=
  ∃ r s A B : ℕ, 0<r ∧ r≤2^k ∧ 0<s ∧ s≤2^k ∧
    Label r (2^b) A (Real.sqrt n) ∧ Label s (2^b) B (Real.sqrt n) ∧
    ∃ d e z : ℕ, A^2=d+4*r*n ∧ B^2=e+4*s*n ∧ z^2=d*e ∧ (A*B-z).gcd n<n

private abbrev budgets : List (ℕ×ℕ) := [(4,0),(16,16),(64,64),(128,128),(160,64),(64,256)]

/-- On any finite set of products, pick one witness per product and count the
union, allowing repeated witnesses or multiple choices for one product. -/
private theorem by_product {k b : ℕ} (row : (k,b)∈budgets) (P : Finset ℕ)
    (data : ∀ n∈P, ∃ r s A B : ℕ, 0<r ∧ r≤2^k ∧ 0<s ∧ s≤2^k ∧ Hit r s A B n (2^b)) :
    2^(saving k b)*P.card < MixedPrefixSample.eligible.card := by
  classical
  have selects (n : P) := data n n.property
  choose r s A B hr hrk hs hsk hit using selects
  let w (n : P) := (r n,s n)
  let ws := univ.image w
  let as (w₀ : ℕ×ℕ) := (univ.filter (fun n : P => w n=w₀)).image A
  let bs (w₀ : ℕ×ℕ) (a : ℕ) := (univ.filter (fun n : P => w n=w₀ ∧ A n=a)).image B
  let cell (w₀ : ℕ×ℕ) (a f : ℕ) :=
    P.filter fun n => Hit w₀.1 w₀.2 a f n (2^b)
  have weights (w₀ : ℕ×ℕ) (mem : w₀∈ws) :
      0<w₀.1 ∧ w₀.1≤2^k ∧ 0<w₀.2 ∧ w₀.2≤2^k := by
    obtain ⟨n,_,rfl⟩ := mem_image.mp mem
    exact ⟨hr n,hrk n,hs n,hsk n⟩
  have pairData (w₀ : ℕ×ℕ) (a f : ℕ) (mem : f∈bs w₀ a) :
      ∃ n∈P, Hit w₀.1 w₀.2 a f n (2^b) := by
    obtain ⟨n,hm,rfl⟩ := mem_image.mp mem
    obtain ⟨eq1,eq2⟩ := (mem_filter.mp hm).2
    rw [←eq1,←eq2]
    exact ⟨n,n.property,hit n⟩
  obtain ⟨even,room,short⟩ := reported_budgets row
  apply population even room short ws as bs weights
  · intro w₀ _ a mem
    obtain ⟨n,hm,rfl⟩ := mem_image.mp mem
    rw [←(mem_filter.mp hm).2]
    exact ⟨Real.sqrt n.val,Real.sqrt_nonneg _,by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using (hit n).top,(hit n).first⟩
  · intro w₀ _ a _ f mem
    obtain ⟨n,_,h⟩ := pairData w₀ a f mem
    exact ⟨Real.sqrt n,Real.sqrt_nonneg _,by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using h.top,h.first,h.second⟩
  · intro w₀ _ a _ f mem
    obtain ⟨_,_,h⟩ := pairData w₀ a f mem
    exact h.nonsingular
  · have cover : P⊆ws.biUnion (fun w₀ => (as w₀).biUnion (fun a => (bs w₀ a).biUnion (cell w₀ a))) := by
      intro n hn
      let i : P := ⟨n,hn⟩
      have wIn : w i∈ws := mem_image_of_mem _ (mem_univ _)
      have aIn : A i∈as (w i) := mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,rfl⟩)
      have bIn : B i∈bs (w i) (A i) := mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,rfl,rfl⟩)
      exact mem_biUnion.mpr ⟨w i,wIn,mem_biUnion.mpr ⟨A i,aIn,mem_biUnion.mpr
        ⟨B i,bIn,mem_filter.mpr ⟨hn,hit i⟩⟩⟩⟩
    apply (card_le_card cover).trans
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro w₀ hw
    obtain ⟨rp,rk,sp,sk⟩ := weights _ hw
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro a _
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro f _
    exact WeightedMultiplierFiber.bound row rp rk sp sk (cell w₀ a f) (fun _ hn => (mem_filter.mp hn).2)

attribute [local irreducible] MixedPrefixSample.ordered MixedPrefixSample.primes MixedPrefixSample.X

private theorem sample_data {E : ℕ → Prop} {z : ℕ×ℕ} (mem : z∈MixedPrefixSample.sample E) :
    z.1.Prime ∧ z.2.Prime ∧ z.1<z.2 ∧
    Real.sqrt (z.1*z.2 : ℕ) ≤ 2*(2:ℝ)^1023 ∧ E (z.1*z.2) := by
  rw [MixedPrefixSample.sample, mem_filter] at mem
  obtain ⟨hm,ord⟩ := mem
  obtain ⟨hp,hq,_,_,event⟩ := (MixedPrefixSample.mem_ordered (E:=E) (z:=z)).mp hm
  rw [MixedPrefixSample.primes, mem_filter, mem_Ico] at hp hq
  obtain ⟨bp,pprime⟩ := hp
  obtain ⟨bq,qprime⟩ := hq
  have size : z.1*z.2 ≤ (2*MixedPrefixSample.X)^2 := by
    rw [sq]
    exact Nat.mul_le_mul bp.2.le bq.2.le
  refine ⟨pprime,qprime,ord,?_,event⟩
  apply (Real.sqrt_le_iff).mpr
  unfold MixedPrefixSample.X at size
  exact ⟨by positivity,by exact_mod_cast size⟩

attribute [local irreducible] MixedPrefixSample.sample

private theorem prime_pairs {k b : ℕ} (row : (k,b)∈budgets) (S : Finset (ℕ×ℕ))
    (properties : ∀ z∈S, z.1.Prime ∧ z.2.Prime ∧ z.1<z.2 ∧
      Real.sqrt (z.1*z.2 : ℕ) ≤ 2*(2:ℝ)^1023 ∧ Reached k b (z.1*z.2)) :
    2^(saving k b)*S.card<MixedPrefixSample.eligible.card := by
  classical
  let value (z : ℕ×ℕ) := z.1*z.2
  let P := S.image value
  have unique : Set.InjOn value (S : Set (ℕ×ℕ)) := by
    intro x hx y hy eq
    obtain ⟨xp,_,xy,_,_⟩ := properties x hx
    obtain ⟨yp,yq,yy,_,_⟩ := properties y hy
    obtain ⟨h₁,h₂⟩ := ordered_semiprime_pair_unique yp yq yy.le xy.le xp.one_lt eq
    exact Prod.ext h₁ h₂
  have equal : P.card=S.card := card_image_of_injOn unique
  refine lt_of_eq_of_lt (congrArg (fun j => 2^(saving k b)*j) equal.symm) ?_
  apply by_product row P
  intro n hn
  change n∈S.image value at hn
  rw [mem_image] at hn
  obtain ⟨z,hz,rfl⟩ := hn
  obtain ⟨_,_,_,top,r,s,A,B,rp,rk,sp,sk,al,bl,wit⟩ := properties z hz
  exact ⟨r,s,A,B,rp,rk,sp,sk,top,al,bl,wit⟩

/-- No auxiliary population, fiber, or divisor-count hypotheses. Every pair
that admits even one successful bounded choice is included. -/
theorem eligible_coverage {k b : ℕ}
    (row : (k,b)∈[(4,0),(16,16),(64,64),(128,128),(160,64),(64,256)]) :
    2^(saving k b)*(MixedPrefixSample.sample (Reached k b)).card <
      MixedPrefixSample.eligible.card :=
  prime_pairs row _ (fun z hz => sample_data (E:=Reached k b) (z:=z) hz)

end PrimeFactors.WeightedMultiplierCoverage
