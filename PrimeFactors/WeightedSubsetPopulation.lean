import PrimeFactors.WeightedSubsetFiber
import PrimeFactors.WeightedSubsetMenu

/-! Count all supported squarefree excess classes at the sixteen anchors of
the public weighted-label vector, allowing each product to choose its anchor. -/
namespace PrimeFactors.WeightedSubsetPopulation
open Finset WeightedSubsetFiber
open WeightedSubsetMenu (Vector vector)
set_option exponentiation.threshold 20000
set_option maxRecDepth 4096

abbrev Anchor := Fin 8 × Fin 2

/-- The denominator support is fixed by the public menu and anchor. Only the
chosen anchor for a successful product must satisfy the two size inequalities. -/
def Candidate (M : Vector → Anchor → ℕ) (n : ℕ) : Prop :=
  ∃ i : Anchor, 0<M (vector n) i ∧ M (vector n) i<2^(15*1037) ∧
    InFiber (i.1.val+1) (vector n i.1 i.2) (M (vector n) i) (2^517) n

/-- A finite set of distinct products with fixed public support and the
indicated permitted menus needs at most sixteen fixed-label fibers per menu. -/
theorem product_count (M : Vector → Anchor → ℕ) (P : Finset ℕ) (menus : Finset Vector)
    (admitted : ∀ n∈P, vector n∈menus) (hits : ∀ n∈P, Candidate M n) :
    P.card ≤ menus.card*(16*(2^517*2^193)) := by
  classical
  let cell (v : Vector) (i : Anchor) := P.filter fun n => vector n=v ∧
    0<M v i ∧ M v i<2^(15*1037) ∧ InFiber (i.1.val+1) (v i.1 i.2) (M v i) (2^517) n
  let allAnchors : Finset Anchor := univ
  have cover : P⊆menus.biUnion (fun v => allAnchors.biUnion (cell v)) := by
    intro n hn
    obtain ⟨i,pos,short,mem⟩ := hits n hn
    exact mem_biUnion.mpr ⟨_,admitted n hn,mem_biUnion.mpr ⟨i,mem_univ _,
      mem_filter.mpr ⟨hn,rfl,pos,short,mem⟩⟩⟩
  have per (v : Vector) (i : Anchor) : (cell v i).card≤2^517*2^193 := by
    rcases (cell v i).eq_empty_or_nonempty with empty|⟨n,hn⟩
    · simp [empty]
    obtain ⟨_,_,pos,small,_⟩ := mem_filter.mp hn
    exact fiber (Nat.succ_pos i.1.val) pos small _ (fun _ h => (mem_filter.mp h).2.2.2.2)
  apply (card_le_card cover).trans
  apply card_biUnion_le_card_mul
  intro v _
  have anchors : allAnchors.card=16 := by decide +kernel
  exact (card_biUnion_le_card_mul _ _ _ (fun i _ => per v i)).trans_eq
    (congrArg (·*(2^517*2^193)) anchors)

attribute [local irreducible] MixedPrefixSample.ordered MixedPrefixSample.primes MixedPrefixSample.sample
  MixedPrefixSample.eligible

private theorem same_product (S : Finset (ℕ×ℕ))
    (members : ∀ z∈S, z.1.Prime ∧ z.2.Prime ∧ z.1<z.2) :
    Set.InjOn (fun z : ℕ×ℕ => z.1*z.2) (S : Set (ℕ×ℕ)) := by
  intro x hx y hy eq
  obtain ⟨xp,_,xy⟩ := members x hx
  obtain ⟨yp,yq,yy⟩ := members y hy
  obtain ⟨a,b⟩ := ordered_semiprime_pair_unique yp yq yy.le xy.le xp.one_lt eq
  exact Prod.ext a b

private theorem eligible_of_mem {E : ℕ → Prop} {z : ℕ×ℕ} (hz : z∈MixedPrefixSample.sample E) :
    z∈MixedPrefixSample.eligible := by
  rw [MixedPrefixSample.sample,mem_filter] at hz
  rw [MixedPrefixSample.eligible,MixedPrefixSample.sample,mem_filter]
  obtain ⟨p,q,ne,large,_⟩ := (MixedPrefixSample.mem_ordered (z:=z) (E:=E)).mp hz.1
  exact ⟨(MixedPrefixSample.mem_ordered (E:=fun _ => True)).mpr ⟨p,q,ne,large,trivial⟩,hz.2⟩

/-- The absolute bound counts actual prime pairs, with no assumed size condition
on the support of unused anchors or impossible menus. -/
theorem eligible_count (event : ℕ → Prop) (M : Vector → Anchor → ℕ)
    (bridge : ∀ z∈MixedPrefixSample.sample event, Candidate M (z.1*z.2)) :
    (MixedPrefixSample.sample event).card ≤ (153*2^1023+8)*(16*(2^517*2^193)) := by
  classical
  let S := MixedPrefixSample.sample event
  let P := S.image (fun z => z.1*z.2)
  let menus := MixedPrefixSample.eligible.image (fun z => vector (z.1*z.2))
  have primes (z : ℕ×ℕ) (h : z∈S) : z.1.Prime ∧ z.2.Prime ∧ z.1<z.2 := by
    obtain ⟨hp,hq,order,_,_⟩ := WeightedMultiplierCoverage.sample_data (E:=event) (z:=z) h
    exact ⟨hp,hq,order⟩
  have same : P.card=S.card := card_image_of_injOn (same_product S primes)
  have admitted (n : ℕ) (h : n∈P) : vector n∈menus := by
    obtain ⟨z,hz,rfl⟩ := mem_image.mp h
    exact mem_image_of_mem _ (eligible_of_mem hz)
  have supports (n : ℕ) (h : n∈P) : Candidate M n := by
    obtain ⟨z,hz,rfl⟩ := mem_image.mp h
    exact bridge z hz
  exact (same.ge.trans (product_count M P menus admitted supports)).trans
    (Nat.mul_le_mul_right _ WeightedSubsetMenu.eligible_menus)

/-- Under a pointwise support proof on every successful eligible pair, the
fraction of the entire target population is strictly less than 2⁻²⁷⁷. -/
theorem eligible_coverage (event : ℕ → Prop) (M : Vector → Anchor → ℕ)
    (bridge : ∀ z∈MixedPrefixSample.sample event, Candidate M (z.1*z.2)) :
    2^277*(MixedPrefixSample.sample event).card < MixedPrefixSample.eligible.card := by
  have count := eligible_count event M bridge
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  apply lt_of_le_of_lt _ ChebyshevPrimeSample.eligible_count
  exact (Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left (2^277) count)).trans (by decide +kernel)

/-- The equivalent product-only interface accepts an event proof on the
balanced range without requiring access to the individual primes. -/
theorem sample_coverage (event : ℕ → Prop) (M : Vector → Anchor → ℕ)
    (bridge : ∀ n : ℕ, 0<n → Real.sqrt n≤2*(2:ℝ)^1023 → event n → Candidate M n) :
    2^277*(MixedPrefixSample.sample event).card < MixedPrefixSample.eligible.card := by
  apply eligible_coverage event M
  intro z hz
  obtain ⟨hp,hq,_,upper,hit⟩ := WeightedMultiplierCoverage.sample_data (E:=event) (z:=z) hz
  exact bridge _ (Nat.mul_pos hp.pos hq.pos) upper hit

end PrimeFactors.WeightedSubsetPopulation
