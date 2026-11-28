import PrimeFactors.ComplementaryQuarticPopulation

/-! Population upper bounds for testing bounded denominators with the two
fourth-root recognizers. Counts allow the denominator to be chosen from the
whole menu separately for each input. -/
namespace PrimeFactors.ScaledQuarticMenuBound

open Finset
open MixedPrefixSample (eligible)
open ComplementaryQuarticProducts (choices)
open private PrimeFactors.QuarticPrimePopulation.eligible_bounds
  PrimeFactors.QuarticPrimePopulation.bounded_encodings from PrimeFactors.QuarticPrimePopulation
open scoped Classical
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible

private def encode (d : ℕ) (v : ℕ×ℕ) := d^4*(v.1*v.2)

private theorem inject {S : Finset (ℕ×ℕ)} {d : ℕ} (pos : 0<d)
    (valid : ∀ v∈S,v.1.Prime ∧ v.2.Prime ∧ v.1<v.2) : Set.InjOn (encode d) (S : Set (ℕ×ℕ)) := by
  intro v hv w hw eq
  obtain ⟨p,q,vo⟩ := valid v hv
  obtain ⟨u,_,wo⟩ := valid w hw
  change d^4*(v.1*v.2)=d^4*(w.1*w.2) at eq
  have same_prod := Nat.eq_of_mul_eq_mul_left (pow_pos pos 4) eq
  have same := ordered_semiprime_pair_unique p q vo.le wo.le u.one_lt same_prod.symm
  exact (Prod.ext same.1 same.2).symm

private theorem scale_bound {v : ℕ×ℕ} (hv : v∈eligible) {d : ℕ} (fit : d≤2^11) :
    encode d v<2^2092 := by
  have size := (PrimeFactors.QuarticPrimePopulation.eligible_bounds hv).2.1
  calc
    _ ≤ (2^11)^4*(v.1*v.2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left fit 4)
    _ < (2^11)^4*2^2048 := Nat.mul_lt_mul_of_pos_left size (by positivity)
    _ = _ := by decide +kernel

/-- The leading coordinate fits in 523 bits. The remainder coordinate has
at most 393 bits in the first branch or 394 bits in the second. -/
private theorem boxes {n x y : ℕ} (small : n<2^2092) (form : n=x^4+4*y^4) :
    (n<(x+1)^4 → x<2^523 ∧ y<2^393) ∧ (n<4*(y+1)^4 → x<2^394 ∧ y<2^523) := by
  have edge : ((2:ℕ)^523)^4=2^2092 := by decide +kernel
  have xlarge : x<2^523 := (Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp (by rw [edge]; omega)
  have ylarge : y<2^523 := (Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp (by rw [edge]; omega)
  constructor
  · intro gap
    have cap : y^4<(x+1)^3 := by rw [form] at gap; nlinarith only [gap,Nat.zero_le x,Nat.zero_le (x^2)]
    refine ⟨xlarge,(Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp ?_⟩
    exact (cap.trans_le (Nat.pow_le_pow_left xlarge 3)).trans_le (by decide +kernel)
  · intro gap
    have cap : x^4<16*(y+1)^3 := by rw [form] at gap; nlinarith only [gap,Nat.zero_le y,Nat.zero_le (y^2)]
    refine ⟨(Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp ?_,ylarge⟩
    exact (cap.trans_le (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left ylarge 3))).trans_le (by decide +kernel)

noncomputable def family (d : ℕ) := eligible.filter (fun v => (choices (encode d v)).Nonempty)

private theorem side (S : Finset (ℕ×ℕ)) (d a b : ℕ) (pos : 0<d) (incl : S⊆eligible)
    (cover : ∀ v∈S,∃ x<a,∃ y<b, x^4+4*y^4=encode d v) : S.card≤a*b := by
  apply PrimeFactors.QuarticPrimePopulation.bounded_encodings S a b (encode d) (fun z => z.1^4+4*z.2^4) _ cover
  apply inject pos
  intro v hv
  obtain ⟨_,ord,_,p,q,_⟩ := SumGridPopulation.eligible_data.mp (incl hv)
  exact ⟨p,q,ord⟩

theorem one {d : ℕ} (pos : 0<d) (fit : d≤2^11) : (family d).card≤3*2^916 := by
  let F := eligible.filter (fun v => ∃ x<2^523,∃ y<2^393,x^4+4*y^4=encode d v)
  let R := eligible.filter (fun v => ∃ x<2^394,∃ y<2^523,x^4+4*y^4=encode d v)
  have union : family d⊆F∪R := by
    intro v hv
    obtain ⟨mem,ab,hit⟩ := mem_filter.mp hv
    obtain ⟨x,y,_,_,form,gap,_⟩ := ComplementaryQuarticProducts.mem_choices.mp hit
    have both := boxes (scale_bound mem fit) form
    rcases gap with left|right
    · have b := both.1 left
      exact mem_union_left _ (mem_filter.mpr ⟨mem,x,b.1,y,b.2,form.symm⟩)
    · have b := both.2 right
      exact mem_union_right _ (mem_filter.mpr ⟨mem,x,b.1,y,b.2,form.symm⟩)
  have left := side F d (2^523) (2^393) pos (filter_subset ..) (fun _ h => (mem_filter.mp h).2)
  have right := side R d (2^394) (2^523) pos (filter_subset ..) (fun _ h => (mem_filter.mp h).2)
  exact (((card_le_card union).trans (card_union_le F R)).trans (Nat.add_le_add left right)).trans_eq (by decide +kernel)

noncomputable def covered (D : Finset ℕ) := D.biUnion family

theorem menu (D : Finset ℕ) (budget : ∀ d∈D,0<d ∧ d≤2^11) :
    (covered D).card≤D.card*(3*2^916) := by
  have cap := Finset.sum_le_sum (s:=D) (fun d hd => one (budget d hd).1 (budget d hd).2)
  exact (card_biUnion_le.trans cap).trans_eq (by simp)

private theorem share {D : Finset ℕ} (budget : ∀ d∈D,0<d ∧ d≤2^11) (k : ℕ)
    (small : 21000000*(k*(D.card*(3*2^916)))<2^2046) : k*(covered D).card<eligible.card :=
  Nat.lt_of_mul_lt_mul_left ((Nat.mul_le_mul_left _ (Nat.mul_le_mul_left k (menu D budget))).trans_lt
    (small.trans (MixedPrefixSample.denominator ChebyshevPrimeSample.prime_count)))

theorem three : 2^1102*(covered {1,725,1517}).card<eligible.card :=
  share (by simp) _ (by decide +kernel)

theorem all_bounded : 2^1093*(covered (Icc 1 2048)).card<eligible.card := by
  apply share
  · intro d hd
    exact mem_Icc.mp hd
  · rw [Nat.card_Icc]
    decide +kernel

end PrimeFactors.ScaledQuarticMenuBound
