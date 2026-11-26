import PrimeFactors.WeightedTripleFiber
import PrimeFactors.WeightedMultiplierCoverage

/-! Finite target population for three weighted square excesses. All three
multipliers and labels may be chosen after observing the product. This count
requires positive pairwise norm constants and the indicated support condition. -/
namespace PrimeFactors.WeightedTriplePopulation
open Finset WeightedMultiplierPopulation WeightedTripleFiber
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

private abbrev X : ℕ := 2^1023

/-- Evidence used to count a fixed triple of weights and labels. -/
structure Row (r s v A B F n : ℕ) : Prop where
  top : Real.sqrt n ≤ 2*(2:ℝ)^1023
  first : Label r 2 A (Real.sqrt n)
  second : Label s 2 B (Real.sqrt n)
  third : Label v 2 F (Real.sqrt n)
  pos12 : 0<difference (r,s) A B
  pos13 : 0<difference (r,v) A F
  pos23 : 0<difference (s,v) B F
  support : ∃ m : ℕ, m ∣ difference (r,v) A F * difference (s,v) B F ∧ InClass r s A B m 2048 n

def Reached (n : ℕ) : Prop := ∃ r∈Icc 1 8, ∃ s∈Icc 1 8, ∃ v∈Icc 1 8,
  ∃ A B F, Row r s v A B F n

private abbrev fiberCap : ℕ := 2^242*(4096*2^242)
private abbrev fixedCap : ℕ := (197*3*X*2)*(288*fiberCap)

set_option exponentiation.threshold 100000 in
private theorem divisor_cap {a : ℕ} (ha : 0<a) (small : a<2^2074) :
    a.divisors.card<2^242 := by
  have bound := UniformDivisorCount.below_power_two ha small
  apply (Nat.pow_lt_pow_iff_left (by decide : 336≠0)).mp
  rw [←pow_mul]
  exact bound.trans_le (Nat.pow_le_pow_right (by decide) (by decide : 14882+32*2074≤242*336))

private theorem diff_small {r s A B n : ℕ} (hr : r∈Icc 1 8) (hs : s∈Icc 1 8)
    (top : Real.sqrt n ≤ 2*(2:ℝ)^1023) (a : Label r 2 A (Real.sqrt n))
    (b : Label s 2 B (Real.sqrt n)) : difference (r,s) A B < 2^1037 := by
  obtain ⟨rp,rk⟩ := mem_Icc.mp hr
  obtain ⟨sp,sk⟩ := mem_Icc.mp hs
  have h := difference_lt rp sp rk sk (by decide : 8≤3^2) (by decide +kernel : 24*2≤3*X)
    (Real.sqrt_nonneg _) (by exact_mod_cast top : Real.sqrt n≤2*(X:ℝ)) a b
  exact h.trans_le (by decide +kernel)

private theorem fiber {r s v A B F : ℕ} (hr : r∈Icc 1 8) (hs : s∈Icc 1 8) (hv : v∈Icc 1 8)
    (P : Finset ℕ) (each : ∀ n∈P, Row r s v A B F n) : P.card≤fiberCap := by
  rcases P.eq_empty_or_nonempty with empty|⟨n,hn⟩
  · simp [empty]
  have h := each n hn
  have c12 := diff_small hr hs h.top h.first h.second
  have c13 := diff_small hr hv h.top h.first h.third
  have c23 := diff_small hs hv h.top h.second h.third
  have cprod := Nat.mul_pos h.pos13 h.pos23
  have cap1 := divisor_cap cprod (show difference (r,v) A F*difference (s,v) B F<2^2074 by
    calc _ < (2^1037)*(2^1037) := Nat.mul_lt_mul_of_lt_of_le c13 c23.le (by positivity)
         _ = _ := by decide +kernel)
  have cap2 := divisor_cap (pow_pos h.pos12 2) (show (difference (r,s) A B)^2<2^2074 by
    calc _ < ((2:ℕ)^1037)^2 := Nat.pow_lt_pow_left c12 (by decide)
         _ = _ := by decide +kernel)
  have bound := divisor_union (mem_Icc.mp hr).1 (mem_Icc.mp hs).1 cprod h.pos12 P
    (fun a ha => (each a ha).support)
  exact bound.trans (Nat.mul_le_mul cap1.le (Nat.mul_le_mul_left _ cap2.le))

private theorem third_card {r v A : ℕ} (hr : r∈Icc 1 8) (hv : v∈Icc 1 8)
    (ls : Finset ℕ) (each : ∀ f∈ls, ∃ t:ℝ, Label r 2 A t ∧ Label v 2 f t) : ls.card≤288 := by
  rcases ls.eq_empty_or_nonempty with empty|nonempty
  · simp [empty]
  let low := ls.min' nonempty
  let high := ls.max' nonempty
  obtain ⟨a,a1,a2⟩ := each high (ls.max'_mem nonempty)
  obtain ⟨b,b1,b2⟩ := each low (ls.min'_mem nonempty)
  have bound := second_lt (mem_Icc.mp hr).1 (mem_Icc.mp hv).1
    ((mem_Icc.mp hr).2.trans (by decide : 8≤3^2)) ((mem_Icc.mp hv).2.trans (by decide : 8≤3^2))
    (by decide : 0<2) a1 b1 a2 b2
  have sub : ls ⊆ Icc low high := fun i hi => mem_Icc.mpr ⟨ls.min'_le _ hi,ls.le_max' _ hi⟩
  have count := card_le_card sub
  rw [Nat.card_Icc] at count
  omega

/-- Fixed weights, allowing each product to select independently its three labels. -/
private theorem fixed {r s v : ℕ} (hr : r∈Icc 1 8) (hs : s∈Icc 1 8) (hv : v∈Icc 1 8)
    (P : Finset ℕ) (selects : ∀ n∈P, ∃ A B F, Row r s v A B F n) : P.card≤fixedCap := by
  classical
  choose A B F rows using fun n : P => selects n n.property
  let as := univ.image A
  let bs (a : ℕ) := (univ.filter (fun n : P => A n=a)).image B
  let fs (a : ℕ) := (univ.filter (fun n : P => A n=a)).image F
  let cell (a b f : ℕ) := P.filter (Row r s v a b f)
  have sub : P ⊆ as.biUnion (fun a => (bs a).biUnion (fun b => (fs a).biUnion (cell a b))) := by
    intro n hn
    let i : P := ⟨n,hn⟩
    have ai : A i ∈ as := mem_image_of_mem _ (mem_univ i)
    have same : i ∈ univ.filter (fun n : P => A n=A i) := mem_filter.mpr ⟨mem_univ _,rfl⟩
    exact mem_biUnion.mpr ⟨_,ai,mem_biUnion.mpr ⟨_,mem_image_of_mem _ same,mem_biUnion.mpr
      ⟨_,mem_image_of_mem _ same,mem_filter.mpr ⟨hn,rows i⟩⟩⟩⟩
  have firsts (a : ℕ) (ha : a∈as) : ∃ t:ℝ, 0≤t ∧ t≤2*X ∧ Label r 2 a t := by
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    exact ⟨Real.sqrt i.val,Real.sqrt_nonneg _,by exact_mod_cast (rows i).top,(rows i).first⟩
  have pairs (a b : ℕ) (hb : b∈bs a) : ∃ t:ℝ, Label r 2 a t ∧ Label s 2 b t := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hb
    rw [←(mem_filter.mp hi).2]
    exact ⟨_,(rows i).first,(rows i).second⟩
  have thirds (a : ℕ) : (fs a).card≤288 := by
    apply third_card (A:=a) hr hv
    intro f hf
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hf
    rw [←(mem_filter.mp hi).2]
    exact ⟨_,(rows i).first,(rows i).third⟩
  have firstPair := trace_pairs (mem_Icc.mp hr).1 (mem_Icc.mp hs).1
    ((mem_Icc.mp hr).2.trans (by decide : 8≤3^2)) ((mem_Icc.mp hs).2.trans (by decide : 8≤3^2))
    (by decide : 0<2) (by decide +kernel : 64*(24*2+1)≤X) as bs firsts
    (fun a _ b hb => pairs a b hb)
  have two (a b : ℕ) : ((fs a).biUnion (cell a b)).card≤288*fiberCap := by
    exact (card_biUnion_le_card_mul _ _ _ (fun f _ => fiber hr hs hv _ (fun _ h => (mem_filter.mp h).2))).trans
      (Nat.mul_le_mul_right _ (thirds a))
  calc
    _ ≤ _ := card_le_card sub
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ a∈as, (bs a).card*(288*fiberCap) :=
      sum_le_sum fun a _ => card_biUnion_le_card_mul _ _ _ (fun b _ => two a b)
    _ = (∑ a∈as, (bs a).card)*(288*fiberCap) := (sum_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ firstPair

/-- All 512 ordered weight triples are tried in the upper count. -/
theorem population (P : Finset ℕ) (each : ∀ n∈P, Reached n) :
    2^475*P.card < MixedPrefixSample.eligible.card := by
  classical
  let ws := Icc 1 8
  let cell (r s v : ℕ) := P.filter (fun n => ∃ A B F, Row r s v A B F n)
  have sub : P⊆ws.biUnion (fun r => ws.biUnion (fun s => ws.biUnion (cell r s))) := by
    intro n hn
    obtain ⟨r,hr,s,hs,v,hv,rest⟩ := each n hn
    exact mem_biUnion.mpr ⟨r,hr,mem_biUnion.mpr ⟨s,hs,mem_biUnion.mpr
      ⟨v,hv,mem_filter.mpr ⟨hn,rest⟩⟩⟩⟩
  have count : P.card≤ws.card*(ws.card*(ws.card*fixedCap)) := by
    apply (card_le_card sub).trans
    apply card_biUnion_le_card_mul
    intro r hr
    apply card_biUnion_le_card_mul
    intro s hs
    apply card_biUnion_le_card_mul
    intro v hv
    exact fixed hr hs hv _ (fun _ h => (mem_filter.mp h).2)
  have base : ws.card=8 := by decide
  rw [base] at count
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  apply lt_of_le_of_lt _ ChebyshevPrimeSample.eligible_count
  exact (Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left (2^475) count)).trans (by decide +kernel)

private theorem prime_pairs (S : Finset (ℕ×ℕ))
    (members : ∀ z∈S, z.1.Prime ∧ z.2.Prime ∧ z.1<z.2 ∧ Reached (z.1*z.2)) :
    2^475*S.card < MixedPrefixSample.eligible.card := by
  classical
  let product (z : ℕ×ℕ) := z.1*z.2
  have inj : Set.InjOn product (S : Set (ℕ×ℕ)) := by
    intro x hx y hy eq
    obtain ⟨px,_,lx,_⟩ := members _ hx
    obtain ⟨py,qy,ly,_⟩ := members _ hy
    obtain ⟨one,two⟩ := ordered_semiprime_pair_unique py qy ly.le lx.le px.one_lt eq
    exact Prod.ext one two
  have card : (S.image product).card=S.card := card_image_of_injOn inj
  apply lt_of_eq_of_lt (congrArg (fun n => 2^475*n) card.symm)
  apply population
  intro n hn
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hn
  exact (members _ hz).2.2.2

attribute [local irreducible] MixedPrefixSample.sample MixedPrefixSample.ordered MixedPrefixSample.primes

/-- Any event supported by these triples occupies less than 2⁻⁴⁷⁵ of the
actual population. Each distinct unordered eligible prime pair occurs once. -/
theorem sample_coverage (event : ℕ → Prop)
    (bridge : ∀ n : ℕ, 0<n → Real.sqrt n≤2*(2:ℝ)^1023 → event n → Reached n) :
    2^475*(MixedPrefixSample.sample event).card < MixedPrefixSample.eligible.card := by
  apply prime_pairs
  intro z hz
  obtain ⟨hp,hq,order,upper,reached⟩ := WeightedMultiplierCoverage.sample_data (E:=event) (z:=z) hz
  exact ⟨hp,hq,order,bridge _ (Nat.mul_pos hp.pos hq.pos) upper reached⟩

end PrimeFactors.WeightedTriplePopulation
