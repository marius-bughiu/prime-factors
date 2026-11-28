import PrimeFactors.MonotoneSumPopulation
import PrimeFactors.SquareRootPhasePopulation

/-! For prime pairs with a large gap, a product block and an exact sum can
contain at most one pair. The gap condition holds on a certified majority
of the population. -/

namespace PrimeFactors.SeparatedMonotonePopulation

open Finset MixedPrefixSample
open scoped Classical
open private PrimeFactors.MonotoneSumPopulation.data from PrimeFactors.MonotoneSumPopulation
open private PrimeFactors.MixedPrefixSample.mem_sample from PrimeFactors.MixedPrefixSample

set_option exponentiation.threshold 4096
attribute [local irreducible] eligible primes

def G : ℕ := 2^1006
noncomputable def far := eligible.filter fun z => G≤z.2-z.1

@[simp] theorem mem_far {z : ℕ×ℕ} : z∈far ↔ z∈eligible ∧ G≤z.2-z.1 := mem_filter

noncomputable def agreement (g : ℕ→ℕ) (E : ℕ) := far ∩ MonotoneSumPopulation.agreement g E

theorem mem_agreement {z : ℕ×ℕ} {g : ℕ→ℕ} {E : ℕ} :
    z∈agreement g E ↔ z∈far ∧ g (z.1*z.2)≤z.1+z.2+E ∧ z.1+z.2≤g (z.1*z.2)+E := by
  rw [agreement,mem_inter,MonotoneSumPopulation.agreement,mem_filter]
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,(mem_far.mp h.1).1,h.2⟩⟩

attribute [local irreducible] agreement

private theorem prime_first {z : ℕ×ℕ} (mem : z∈eligible) : z.1∈primes := by
  rw [eligible] at mem
  exact (mem_ordered.mp (PrimeFactors.MixedPrefixSample.mem_sample.mp mem).1).1

private theorem gap_count (A : Finset (ℕ×ℕ)) (P : Finset ℕ) (W : ℕ)
    (data : ∀ z∈A, z.1∈P ∧ z.1≤z.2 ∧ z.2-z.1<W) : A.card≤P.card*W := by
  let encode (z : ℕ×ℕ) := (z.1,z.2-z.1)
  have into (z : ℕ×ℕ) (hz : z∈A) : encode z∈P ×ˢ range W := by
    exact mem_product.mpr ⟨(data z hz).1,mem_range.mpr (data z hz).2.2⟩
  have inj : A.toSet.InjOn encode := by
    intro x hx y hy eq
    have px := (data x hx).2.1
    have py := (data y hy).2.1
    change (x.1,x.2-x.1)=(y.1,y.2-y.1) at eq
    obtain ⟨same,gap⟩ := Prod.mk.inj eq
    exact Prod.ext same (by omega)
  simpa only [card_product,card_range] using card_le_card_of_injOn (s:=A) (t:=P ×ˢ range W) encode into inj

/-- Specifying a smaller prime and an integer gap below G describes every
excluded pair. The count includes composite second entries in its upper bound. -/
theorem near_count : (eligible \ far).card≤primes.card*G := by
  apply gap_count (eligible \ far) primes G
  intro z hz
  obtain ⟨he,hf⟩ := mem_sdiff.mp hz
  exact ⟨prime_first (z:=z) he,(PrimeFactors.MonotoneSumPopulation.data (z:=z) he).1.le,
    lt_of_not_ge (fun gap => hf (mem_far.mpr ⟨he,gap⟩))⟩

/-- At least two thirds of the full eligible sample have gap at least G. -/
theorem two_thirds : 2*eligible.card<3*far.card := by
  have price : 131072*(eligible \ far).card<41056*eligible.card := by
    calc
      _ ≤ 131072*(primes.card*G) := Nat.mul_le_mul_left _ near_count
      _ = X*primes.card := by
        rw [show X=131072*G by decide +kernel]
        ac_rfl
      _ < _ := SquareRootPhasePopulation.marginal
  have part := card_sdiff_add_card_eq_card (show far⊆eligible from filter_subset ..)
  omega

private theorem different_blocks {p q r s W : ℕ} (width : 0<W) (strict : p<r)
    (order : r≤s) (gap : W≤s-r) (sum_eq : p+q=r+s) : p*q/W≠r*s/W := by
  intro same
  have prod_eq := FactorSumProductCell.product_identity strict.le order sum_eq
  have one : 1≤r-p := by omega
  have w : W≤q-r := by omega
  have spacing : W≤(r-p)*(q-r) :=
    w.trans (by simpa only [one_mul] using Nat.mul_le_mul_right (q-r) one)
  have lo := Nat.div_mul_le_self (p*q) W
  have hi := Nat.lt_div_mul_add (a:=r*s) width
  rw [←same] at hi
  omega

/-- On an arbitrary set of sorted pairs with gaps at least W, block and sum
together identify any pair. This proof uses no primality assumption. -/
theorem block_sum_injective (A : Finset (ℕ×ℕ)) {W : ℕ} (width : 0<W)
    (wide : ∀ z∈A, W≤z.2-z.1) :
    (A : Set (ℕ×ℕ)).InjOn (fun z => (z.1*z.2/W,z.1+z.2)) := by
  intro x hx y hy eq
  have sx := wide x hx
  have sy := wide y hy
  have block : x.1*x.2/W=y.1*y.2/W := congrArg Prod.fst eq
  have sums : x.1+x.2=y.1+y.2 := congrArg Prod.snd eq
  rcases lt_trichotomy x.1 y.1 with xy|same|yx
  · exact False.elim (different_blocks width xy (by omega) sy sums block)
  · exact Prod.ext same (by omega)
  · exact False.elim (different_blocks width yx (by omega) sx sums.symm block.symm)

attribute [local irreducible] MonotoneSumBlocks.cells far

private theorem count_generic (A : Finset (ℕ×ℕ)) (g : ℕ→ℕ) (mono : Monotone g) (E B W : ℕ)
    (wp : 0<W) (wide : ∀ v∈A,W≤v.2-v.1)
    (data : ∀ v∈A, v.1*v.2<B*W ∧ g (v.1*v.2)-E≤v.1+v.2 ∧ v.1+v.2≤g (v.1*v.2)+E) :
    A.card≤g (B*W)-g 0+(2*E+1)*B := by
  let tag (v : ℕ×ℕ) := (v.1*v.2/W,v.1+v.2)
  have into (v : ℕ×ℕ) (hv : v∈A) : tag v∈MonotoneSumBlocks.cells g B W E :=
    MonotoneSumBlocks.mem_quotient mono wp (data v hv).1 (data v hv).2.1 (data v hv).2.2
  have fit := card_le_card_of_injOn (s:=A) (t:=MonotoneSumBlocks.cells g B W E) tag into
    (block_sum_injective A wp wide)
  exact fit.trans (MonotoneSumBlocks.card_le g mono B W E)

/-- Upper bound for any nondecreasing predictor on the well-separated prime
pairs, with an inclusive absolute tolerance and product blocks of width G. -/
theorem count (g : ℕ→ℕ) (mono : Monotone g) (E : ℕ) :
    (agreement g E).card≤2^1025-1+(2*E+1)*2^1042 := by
  let cap : ℕ := 2^1025-1
  let clipped (n : ℕ) := min (g n) cap
  have pos : 0<G := by decide +kernel
  have m : Monotone clipped := fun _ _ h => min_le_min_right _ (mono h)
  apply (count_generic (agreement g E) clipped m E (2^1042) G pos _ _).trans
  rotate_left
  · intro v hv
    exact (mem_far.mp ((mem_agreement (z:=v) (g:=g) (E:=E)).mp hv).1).2
  · intro v hv
    have info := (mem_agreement (z:=v) (g:=g) (E:=E)).mp hv
    obtain ⟨lt,high⟩ := PrimeFactors.MonotoneSumPopulation.data (z:=v) (mem_far.mp info.1).1
    have sc : v.1+v.2≤cap := by
      dsimp [cap]; have two : 2*2^1024=2^1025 := by decide +kernel
      omega
    refine ⟨?_,Nat.sub_le_of_le_add ((min_le_left ..).trans info.2.1),?_⟩
    · rw [show 2^1042*G=2^1024*2^1024 by decide +kernel]
      exact Nat.mul_lt_mul_of_lt_of_lt (lt.trans high) high
    · by_cases small : g (v.1*v.2)≤cap
      · simpa only [clipped,min_eq_left small] using info.2.2
      · simp only [clipped,min_eq_right (by omega : cap≤g (v.1*v.2))]
        omega
  exact Nat.add_le_add_right ((Nat.sub_le _ _).trans (min_le_right ..)) _

private theorem price {s c M : ℕ} (bound : s≤c) (room : 3*21000000*(M*c)≤2*2^2046) :
    M*s<far.card := by
  have first := Nat.mul_le_mul_left (3*21000000) (Nat.mul_le_mul_left M bound)
  have second := Nat.mul_lt_mul_of_pos_left ChebyshevPrimeSample.eligible_count (by decide : 0<2)
  have third := Nat.mul_lt_mul_of_pos_left two_thirds (by decide : 0<21000000)
  apply Nat.lt_of_mul_lt_mul_left (a:=3*21000000)
  calc
    _ ≤ _ := first
    _ ≤ _ := room
    _ < _ := second
    _ = 21000000*(2*eligible.card) := by ac_rfl
    _ < _ := third
    _ = _ := by ac_rfl

theorem exact_fraction (g : ℕ→ℕ) (mono : Monotone g) :
    2^979*(agreement g 0).card<far.card :=
  price (count g mono 0) (by decide +kernel)

theorem tolerance_128 (g : ℕ→ℕ) (mono : Monotone g) :
    2^850*(agreement g (2^128)).card<far.card :=
  price (count g mono _) (by decide +kernel)

end PrimeFactors.SeparatedMonotonePopulation
