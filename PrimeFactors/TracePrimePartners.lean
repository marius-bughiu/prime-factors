import PrimeFactors.TraceHitFrequency

/-! Conditional short-interval refinements of the true weighted-trace hit count.
The local prime count and the population comparison are explicit hypotheses.
All subsequent steps are finite integer inequalities. -/

namespace PrimeFactors.TracePrimePartners

open Finset TraceHitFrequency

set_option exponentiation.threshold 8192

/-- There are at most b+1 possible numerators at denominator b, even before
checking coprimality. -/
theorem triangular (k : ℕ) : (directions k).card ≤ k*(k+3)/2 := by
  classical
  let row (i : ℕ) := (Icc (i+1) (2*(i+1))).image (fun a => (a,i+1))
  have sub : directions k ⊆ (range k).biUnion row := by
    intro w hw
    obtain ⟨⟨_,den⟩,lo,hi,_⟩ := mem_filter.mp hw |>.imp_left mem_product.mp
    obtain ⟨pos,cap⟩ := mem_Icc.mp den
    have eq : w.2-1+1=w.2 := by omega
    refine mem_biUnion.mpr ⟨w.2-1,mem_range.mpr (by omega),?_⟩
    exact mem_image.mpr ⟨w.1,mem_Icc.mpr (by simpa only [eq] using And.intro lo hi),by simp [eq]⟩
  have count : (directions k).card ≤ ∑ i∈range k, (i+2) := calc
    _ ≤ _ := card_le_card sub
    _ ≤ ∑ i∈range k, (row i).card := card_biUnion_le
    _ ≤ _ := by
      apply sum_le_sum; intro i _; apply card_image_le.trans; rw [Nat.card_Icc]; omega
  have eq (K : ℕ) : 2*(∑ i∈range K, (i+2))=K*(K+3) := by
    induction K with
    | zero => simp
    | succ K ih => rw [sum_range_succ,Nat.mul_add,ih]; ring
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
  simpa only [mul_comm _ 2,eq] using Nat.mul_le_mul_left 2 count

/-- Width of the full integer partner interval for 2^64 starting powers and
up to 2^64 giant blocks per slope. -/
def width : ℕ := 2^582+1

def Eligible (q : ℕ) : Prop := q.Prime ∧ 2^1023≤q ∧ q<2^1024

private instance (q : ℕ) : Decidable (Eligible q) := by unfold Eligible; infer_instance

/-- Only eligible primes are counted, including when the interval extends
beyond the factor range. The starting integer may be arbitrary. -/
def ShortBound (s : ℕ) : Prop := ∀ a : ℕ,
  ((Ico a (a+width)).filter Eligible).card ≤ width/s

/-- The accessible trace may use product-dependent weights and either
assignment of coefficients as specified by `Accessible`. -/
def Supported (pairs : Finset (ℕ×ℕ)) (first : Finset ℕ) (k : ℕ) : Prop :=
  ∀ x∈pairs, x.1∈first ∧ Eligible x.2 ∧ Accessible x (directions k) (2^64)

theorem partner_count {pairs : Finset (ℕ×ℕ)} {first : Finset ℕ} {k s : ℕ}
    (density : ShortBound s) (support : Supported pairs first k) :
    pairs.card ≤ first.card*((directions k).card*(width/s)) := by
  classical
  let low (p : ℕ) (w : ℕ×ℕ) := w.1*p/w.2-2^581
  let partners (p : ℕ) (w : ℕ×ℕ) := (Ico (low p w) (low p w+width)).filter Eligible
  let row (p : ℕ) (w : ℕ×ℕ) := (partners p w).image (fun q => (p,q))
  have sub : pairs ⊆ first.biUnion (fun p => (directions k).biUnion (row p)) := by
    intro x hx
    obtain ⟨mem,prime,h⟩ := support x hx
    obtain ⟨w,hw,hq⟩ := accessible_window (by decide +kernel : 0<2^64) h
    obtain ⟨below,above⟩ := mem_Icc.mp hq
    rw [show (2:ℕ)^517*2^64=2^581 by decide +kernel] at below above
    refine mem_biUnion.mpr ⟨x.1,mem,mem_biUnion.mpr ⟨w,hw,mem_image.mpr ⟨x.2,?_,rfl⟩⟩⟩
    apply mem_filter.mpr; refine ⟨mem_Ico.mpr ⟨below,?_⟩,prime⟩
    have W : width=2*2^581+1 := by decide +kernel
    dsimp only [low]; rw [W]; omega
  apply (card_le_card sub).trans (card_biUnion_le_card_mul _ _ _ ?_)
  intro p _; apply card_biUnion_le_card_mul; intro w _
  exact card_image_le.trans (density (low p w))

private theorem fraction_of_count {A F pop W d L : ℕ} (count : A≤F*W)
    (den : 2^1023*F<d*pop) (w : 0<W) (l : 0<L) (budget : L*d*W≤2^1023) : L*A<pop := by
  apply Nat.lt_of_mul_lt_mul_left (a:=2^1023)
  calc
    _ ≤ 2^1023*(L*(F*W)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ count)
    _ = (2^1023*F)*(L*W) := by ac_rfl
    _ < (d*pop)*(L*W) := Nat.mul_lt_mul_of_pos_right den (Nat.mul_pos l w)
    _ = (L*d*W)*pop := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ budget

private theorem price_fraction {pairs : Finset (ℕ×ℕ)} {first : Finset ℕ} {k S d pop s L : ℕ}
    (density : ShortBound s) (den : 2^1023*first.card<d*pop) (support : Supported pairs first k)
    (card : (directions k).card≤S) (pos : 0<S*(width/s)) (lp : 0<L)
    (budget : L*d*(S*(width/s))≤2^1023) : L*pairs.card<pop :=
  fraction_of_count ((partner_count density support).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ card)))
    den pos lp budget

private theorem large_card {k : ℕ} (cap : k≤2^32) : (directions k).card ≤ 2^32*(2^32+3)/2 :=
  (triangular k).trans (Nat.div_le_div_right (Nat.mul_le_mul cap (Nat.add_le_add_right cap 3)))

/-- The two bounds with the existing population comparison and local divisor 709. -/
theorem at_709 {pairs : Finset (ℕ×ℕ)} {first : Finset ℕ} {pop : ℕ}
    (density : ShortBound 709) (den : 2^1023*first.card<44331*pop) :
    (Supported pairs first 8 → 2^430*pairs.card<pop) ∧
    (∀ k≤2^32, Supported pairs first k → 2^372*pairs.card<pop) := by
  constructor
  · intro h; exact price_fraction density den h (by decide +kernel : (directions 8).card≤23)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k hk h; exact price_fraction density den h (large_card hk)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- A weaker short-interval estimate still gives finite improvements at both cutoffs. -/
theorem at_201 {pairs : Finset (ℕ×ℕ)} {first : Finset ℕ} {pop : ℕ}
    (density : ShortBound 201) (den : 2^1023*first.card<44331*pop) :
    (Supported pairs first 8 → 2^428*pairs.card<pop) ∧
    (∀ k≤2^32, Supported pairs first k → 2^370*pairs.card<pop) := by
  constructor
  · intro h; exact price_fraction density den h (by decide +kernel : (directions 8).card≤23)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k hk h; exact price_fraction density den h (large_card hk)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- With the stated sharper total population bound, the exponents increase to 433 and 375. -/
theorem at_709_sharp {pairs : Finset (ℕ×ℕ)} {first : Finset ℕ} {pop : ℕ}
    (density : ShortBound 709) (den : 2^1023*first.card<4200*pop) :
    (Supported pairs first 8 → 2^433*pairs.card<pop) ∧
    (∀ k≤2^32, Supported pairs first k → 2^375*pairs.card<pop) := by
  constructor
  · intro h; exact price_fraction density den h (by decide +kernel : (directions 8).card≤23)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k hk h; exact price_fraction density den h (large_card hk)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Without any short-interval prime estimate or any restriction on the
partner's primality, triangular catalogue counting still saves two bits. -/
theorem integer_only {pairs : Finset (ℕ×ℕ)} {first : Finset ℕ} {k pop : ℕ}
    (cap : k≤2^32) (den : 2^1023*first.card<44331*pop)
    (support : ∀ x∈pairs, x.1∈first ∧ Accessible x (directions k) (2^64)) :
    2^362*pairs.card<pop := by
  have count := population (by decide +kernel : 0<2^64) support
  have bound := count.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (large_card cap)))
  exact fraction_of_count bound den (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PrimeFactors.TracePrimePartners
