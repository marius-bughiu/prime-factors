import PrimeFactors.HighWordSuffixRanking
import PrimeFactors.FirstSumMenuPopulation

/-! The population of prime products covered by the entire early word block,
even when the choice of row uses every bit of the input. -/

namespace PrimeFactors.WordBlockFrequency

open Finset MixedPrefixSample

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

def B : ℕ := 2^1024

def start (N : ℕ) : ℕ := (B*(N/B)+(B-1)).sqrt

noncomputable def covered (P : ℕ) : Finset (ℕ×ℕ) :=
  eligible.filter fun z =>
    z.1+z.2 ∈ (Icc (start (z.1*z.2)) (start (z.1*z.2)+P)).image (2*·)

/-- If an odd pair's midpoint is in the block, its half-gap lies below
sqrt((2P+1)B). This uses only the word width and the factor width. -/
theorem small_gap {p q u v P : ℕ} (high : q<B) (smaller : p+v=u) (larger : u+v=q)
    (inside : u∈Icc (start (p*q)) (start (p*q)+P)) :
    v^2<(2*P+1)*B := by
  let a := start (p*q)
  obtain ⟨lo,hi⟩ := mem_Icc.mp inside
  change a≤u at lo
  change u≤a+P at hi
  have word := Nat.mul_div_le (p*q) B
  have route := Nat.sqrt_le' (B*((p*q)/B)+(B-1))
  change a^2≤_ at route
  have bp : 0<B := by unfold B; decide +kernel
  have aWord : a^2<p*q+B := by omega
  let j := u-a
  have split : u=a+j := by dsimp [j]; omega
  have bound : j*(u+a)≤P*(2*B) :=
    Nat.mul_le_mul (by dsimp [j]; omega) (by omega)
  have diff : u^2=a^2+j*(u+a) := by rw [split]; ring
  have prod : u^2=p*q+v^2 := by rw [←larger,←smaller]; ring
  nlinarith only [aWord,bound,diff,prod]

attribute [local irreducible] eligible primes ordered sample start covered B

private theorem pair_data {z : ℕ×ℕ} (hz : z∈eligible) :
    z.1∈primes ∧ z.1<z.2 ∧ z.2<B ∧ 2*X^2≤z.1*z.2 := by
  rw [eligible,sample,mem_filter] at hz
  obtain ⟨p,q,_,big,_⟩ := mem_ordered.mp hz.1
  rw [primes,mem_filter] at q
  obtain ⟨band,_⟩ := q
  exact ⟨p,hz.2,by simpa only [B,X] using (mem_Ico.mp band).2,big⟩

private def label (z : ℕ×ℕ) := (z.1,(z.2-z.1)/2)

private theorem label_data {P D : ℕ} (width : (2*P+1)*B≤D^2) {z : ℕ×ℕ}
    (hz : z∈covered P) : z.1∈primes ∧ z.2=z.1+2*(label z).2 ∧ (label z).2<D := by
  rw [covered,mem_filter] at hz
  obtain ⟨he,hm⟩ := hz
  obtain ⟨prime,lt,high,_⟩ := pair_data he
  obtain ⟨u,inBlock,sum⟩ := mem_image.mp hm
  change 2*u=z.1+z.2 at sum
  let v := (label z).2
  have vp : v=(z.2-z.1)/2 := rfl
  have small : z.1+v=u := by omega
  have large : u+v=z.2 := by omega
  have cap := (small_gap high small large inBlock).trans_le width
  exact ⟨prime,by omega,(Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp cap⟩

private theorem count_labels (S : Finset (ℕ×ℕ)) (A : Finset ℕ) (D : ℕ)
    (data : ∀ z∈S, z.1∈A ∧ z.2=z.1+2*(label z).2 ∧ (label z).2<D) :
    S.card≤A.card*D := by
  have included : ∀ z∈S, label z∈A ×ˢ range D := by
    intro z hz
    exact mem_product.mpr ⟨(data z hz).1,mem_range.mpr (data z hz).2.2⟩
  have injective : Set.InjOn label (S : Set (ℕ×ℕ)) := by
    intro u hu v hv eq
    have fst := congrArg Prod.fst eq
    change u.1=v.1 at fst
    have snd := congrArg Prod.snd eq
    exact Prod.ext fst (by rw [(data u hu).2.1,(data v hv).2.1,fst,snd])
  simpa only [card_product,card_range] using card_le_card_of_injOn label included injective

/-- The first prime and half-gap uniquely label every covered product. -/
theorem upper_count {P D : ℕ} (width : (2*P+1)*B≤D^2) :
    (covered P).card≤primes.card*D :=
  count_labels _ _ _ fun _ hz => label_data width hz

/-- Even a perfect chooser supplied with the entire product cannot recover
more than this proportion by trying the 121 rows of the mod-120 block. -/
theorem upper_121 : 2^491*(covered 120).card<eligible.card := by
  have h := upper_count (P:=120) (D:=2^516) (by unfold B; decide +kernel)
  have numeric : 41056*2^491*2^516≤X := by decide +kernel
  apply Nat.lt_of_mul_lt_mul_left (a:=41056)
  calc
    41056*(2^491*(covered 120).card) ≤ 41056*2^491*(primes.card*2^516) := by
      rw [←Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h
    _ = (41056*2^491*2^516)*primes.card := by ring
    _ ≤ X*primes.card := Nat.mul_le_mul_right _ numeric
    _ < 41056*eligible.card := SquareRootPhasePopulation.marginal

/-- All of the first P ordinary Fermat midpoints lie in the P+1 word block
for a sorted pair of the target widths. -/
theorem first_subset (P : ℕ) : sample (FirstSumMenuPopulation.event P) ⊆ covered P := by
  intro z hz
  obtain ⟨inside,hit⟩ := FirstSumMenuPopulation.mem_sample_iff.mp hz
  obtain ⟨_,ord,high,big⟩ := pair_data inside
  let N := z.1*z.2
  let w := N/B
  let T := B*w+(B-1)
  have bl : 0<B := by unfold B; decide +kernel
  have wl : B/2≤w := by
    apply (Nat.le_div_iff_mul_le bl).mpr
    have scale : B/2*B=2*X^2 := by unfold B; decide +kernel
    rw [scale]
    exact big
  have wh : w<B := (Nat.div_lt_iff_lt_mul bl).mpr
    (Nat.mul_lt_mul_of_lt_of_le (ord.trans high) high.le (by omega))
  have fw := HighWordSumRankingBounds.endpoints (by decide : 14≤1024) (h:=w) (by simpa only [B] using wl) (by simpa only [B] using wh)
  have nt : N≤T := by
    have hn := Nat.lt_mul_div_succ N bl
    rw [Nat.mul_add,Nat.mul_one] at hn
    change N≤B*(N/B)+(B-1)
    omega
  have below : T.sqrt≤ceilSqrt N := by
    have prev := fw.prev
    rw [show 2^1024=B from (by unfold B; rfl)] at prev
    change (T.sqrt-1)^2<B*w at prev
    have base : B*w≤N := Nat.mul_div_le N B
    have rc : N≤(ceilSqrt N)^2 := ceilSqrt_le_iff.mp le_rfl
    by_contra! bad
    have := Nat.pow_le_pow_left (by omega : ceilSqrt N≤T.sqrt-1) 2
    omega
  have above : ceilSqrt N≤T.sqrt+1 := ceilSqrt_le_iff.mpr
    (nt.trans (Nat.lt_succ_sqrt' T).le)
  obtain ⟨i,hi,found⟩ := mem_image.mp hit
  have cap := mem_range.mp hi
  rw [covered,mem_filter]
  refine And.intro inside (mem_image.mpr ⟨ceilSqrt N+i,mem_Icc.mpr ?_,found⟩)
  unfold start
  change T.sqrt≤ceilSqrt N+i ∧ ceilSqrt N+i≤T.sqrt+P
  omega

/-- A guaranteed population in the same block follows by placing the
upper-band primes into short buckets and counting pairs in the same bucket. -/
theorem lower_121 : eligible.card < 2^514*(covered 120).card := by
  have cnt := ChebyshevPrimeSample.prime_count
  change 11*X<35500*(upperPrimes.card-1) at cnt
  have enough : 35500*(2*2^507)≤11*X := by decide +kernel
  have h := FirstSumMenuPopulation.frequency (b:=2^507) (D:=2^516) (J:=120)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega)
  have incl := card_le_card (first_subset 120)
  exact h.trans_le (Nat.mul_le_mul (by decide +kernel) incl)

end PrimeFactors.WordBlockFrequency
