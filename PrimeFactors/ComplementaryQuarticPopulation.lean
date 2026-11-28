import PrimeFactors.QuarticPrimePopulation
import PrimeFactors.ComplementaryQuarticProducts

/-! Upper counts for the reciprocal fourth-power gap and for the union of
the two recognition regions, on the full-width sorted semiprime population. -/
namespace PrimeFactors.ComplementaryQuarticPopulation

open Finset
open MixedPrefixSample (eligible)
open RecognizingQuarticProducts (factors recognize)
open ComplementaryQuarticProducts (recognizeY choices)
open private PrimeFactors.QuarticPrimePopulation.eligible_bounds
  PrimeFactors.QuarticPrimePopulation.odd_parameter PrimeFactors.QuarticPrimePopulation.bounded_encodings
  from PrimeFactors.QuarticPrimePopulation
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible

def InFamily (n : ℕ) := ∃ x y : ℕ, 0<x ∧ 0<y ∧ n=x^4+4*y^4 ∧ n<4*(y+1)^4

noncomputable def family := eligible.filter (fun v => InFamily (v.1*v.2))
noncomputable def combined := QuarticPrimePopulation.family ∪ family

theorem mem_family {v : ℕ×ℕ} : v∈family ↔ v∈eligible ∧ InFamily (v.1*v.2) := mem_filter

theorem mem_combined {v : ℕ×ℕ} : v∈combined ↔ v∈QuarticPrimePopulation.family ∨ v∈family := mem_union

attribute [local irreducible] family combined QuarticPrimePopulation.family

/-- The two product-width endpoints restrict y to an interval of length 2^509.
The maximum gap 4((y+1)⁴−y⁴) then bounds x. -/
theorem parameters {n x y : ℕ} (large : 2^2047≤n) (small : n<2^2048)
    (form : n=x^4+4*y^4) (gap : n<4*(y+1)^4) :
    19*2^507≤y ∧ y<23*2^507 ∧ x<25*2^380 := by
  have lo : 19*2^507≤y := by
    by_contra! bad
    have py := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (show y+1≤19*2^507 by omega) 4)
    have edge : 4*(19*(2:ℕ)^507)^4<2^2047 := by decide +kernel
    exact (not_le_of_gt (py.trans_lt edge)) (large.trans gap.le)
  have hi : y<23*2^507 := by
    by_contra! bad
    have py := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left bad 4)
    have edge : 2^2048≤4*(23*(2:ℕ)^507)^4 := by decide +kernel
    omega
  have cap : x^4<16*(y+1)^3 := by
    rw [form] at gap
    nlinarith only [gap,Nat.zero_le y,Nat.zero_le (y^2)]
  have fit := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hi 3)
  have edge : 16*(23*(2:ℕ)^507)^3<(25*2^380)^4 := by decide +kernel
  exact ⟨lo,hi,(Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp (cap.trans (fit.trans_lt edge))⟩

private theorem reverse_iff {n : ℕ} : (recognizeY n).isSome=true ↔ InFamily n := by
  constructor
  · intro yes
    cases eq : recognizeY n with
    | none => simp [eq] at yes
    | some ab =>
      obtain ⟨x,y,xp,yp,form,gap,_⟩ := ComplementaryQuarticProducts.soundY eq
      exact ⟨x,y,xp,yp,form,gap⟩
  · rintro ⟨x,y,xp,yp,form,gap⟩
    rw [ComplementaryQuarticProducts.completeY xp yp form gap]; rfl

theorem recognition {v : ℕ×ℕ} : v∈family ↔ v∈eligible ∧ (recognizeY (v.1*v.2)).isSome=true :=
  mem_family.trans (and_congr_right' reverse_iff.symm)

private theorem canonical {v : ℕ×ℕ} (hv : v∈eligible) {x y : ℕ} (xp : 0<x) (yp : 0<y)
    (form : v.1*v.2=x^4+4*y^4) : factors x y=v := by
  have large := (PrimeFactors.QuarticPrimePopulation.eligible_bounds hv).1
  have diff : (x,y)≠(1,1) := by
    rintro eq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    norm_num at form
    omega
  obtain ⟨lower,ord,_⟩ := (RecognizingQuarticProducts.proper_iff xp yp).mpr diff
  obtain ⟨_,sorted,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp hv
  have same := ordered_semiprime_pair_unique pp qp sorted.le ord.le lower
    ((RecognizingQuarticProducts.factor_product x y).trans form.symm)
  exact Prod.ext same.1 same.2

/-- Membership is equivalent to the two-way recognizer returning the actual
canonical pair for this product. -/
theorem combined_recognition {v : ℕ×ℕ} : v∈combined ↔ v∈eligible ∧ v∈choices (v.1*v.2) := by
  rw [mem_combined,QuarticPrimePopulation.mem_family,mem_family,ComplementaryQuarticProducts.mem_choices]
  constructor
  · rintro (⟨hv,x,y,xp,yp,form,gap⟩|⟨hv,x,y,xp,yp,form,gap⟩)
    · exact ⟨hv,x,y,xp,yp,form,.inl gap,(canonical hv xp yp form).symm⟩
    · exact ⟨hv,x,y,xp,yp,form,.inr gap,(canonical hv xp yp form).symm⟩
  · rintro ⟨hv,x,y,xp,yp,form,(left|right),_⟩
    · exact .inl ⟨hv,x,y,xp,yp,form,left⟩
    · exact .inr ⟨hv,x,y,xp,yp,form,right⟩

theorem disjoint : Disjoint QuarticPrimePopulation.family family := by
  apply Finset.disjoint_left.mpr
  intro v hf hr
  obtain ⟨hv,left⟩ := QuarticPrimePopulation.recognition.mp hf
  obtain ⟨_,right⟩ := recognition.mp hr
  obtain ⟨_,ord,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp hv
  have big := (by decide +kernel : (2:ℕ)^34≤2^2047).trans
    (PrimeFactors.QuarticPrimePopulation.eligible_bounds hv).1
  rcases ComplementaryQuarticProducts.disjoint_on_semiprimes pp qp ord.le big with miss|miss
  · simp [miss] at left
  · simp [miss] at right

private theorem count_parameters (S : Finset (ℕ×ℕ))
    (prime : ∀ v∈S, v.1.Prime ∧ v.2.Prime ∧ v.1<v.2)
    (params : ∀ v∈S, ∃ x y : ℕ, 19*2^507≤y ∧ y<23*2^507 ∧ x<25*2^380 ∧
      x%2=1 ∧ v.1*v.2=x^4+4*y^4) : S.card≤25*2^888 := by
  let prod (v : ℕ×ℕ) := v.1*v.2
  have inj : Set.InjOn prod (S:Set (ℕ×ℕ)) := by
    intro v hv w hw eq
    obtain ⟨p,q,vo⟩ := prime v hv
    obtain ⟨u,_,wo⟩ := prime w hw
    have same := ordered_semiprime_pair_unique p q vo.le wo.le u.one_lt eq.symm
    exact (Prod.ext same.1 same.2).symm
  let decode (z : ℕ×ℕ) := (2*z.1+1)^4+4*(z.2+19*2^507)^4
  have bound : S.card≤(25*2^379)*2^509 := by
    apply PrimeFactors.QuarticPrimePopulation.bounded_encodings S _ _ prod decode inj
    intro v hv
    obtain ⟨x,y,lo,hi,xc,odd,form⟩ := params v hv
    have cx : x/2<25*2^379 ∧ 2*(x/2)+1=x := by omega
    have cy : y-19*2^507<2^509 ∧ y-19*2^507+19*2^507=y := by omega
    exact ⟨x/2,cx.1,y-19*2^507,cy.1,by simp only [prod,decode,cx.2,cy.2,form]⟩
  exact bound.trans_eq (by decide +kernel)

/-- At most 25·2^379 odd-x positions times 2^509 y positions. -/
theorem family_card : family.card≤25*2^888 := by
  apply count_parameters family
  · intro v hv
    obtain ⟨_,ord,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp (mem_family.mp hv).1
    exact ⟨pp,qp,ord⟩
  · intro v hv
    obtain ⟨member,x,y,_,_,form,gap⟩ := mem_family.mp hv
    obtain ⟨large,small,odd⟩ := PrimeFactors.QuarticPrimePopulation.eligible_bounds member
    obtain ⟨lo,hi,xc⟩ := parameters large small form gap
    exact ⟨x,y,lo,hi,xc,PrimeFactors.QuarticPrimePopulation.odd_parameter odd form,form⟩

theorem combined_card_eq : combined.card=QuarticPrimePopulation.family.card+family.card := by
  unfold combined; exact card_union_of_disjoint disjoint

theorem combined_card : combined.card≤49*2^888 := by
  rw [combined_card_eq]
  exact (Nat.add_le_add QuarticPrimePopulation.family_card family_card).trans_eq (by decide +kernel)

private theorem share {k c m : ℕ} (bound : m≤c) (small : 21000000*(k*c)<2^2046) :
    k*m<eligible.card :=
  Nat.lt_of_mul_lt_mul_left ((Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left k bound)).trans_lt
    (small.trans (MixedPrefixSample.denominator ChebyshevPrimeSample.prime_count)))

theorem population : 2^1129*family.card<eligible.card := share family_card (by decide +kernel)

theorem combined_population : 2^1128*combined.card<eligible.card := share combined_card (by decide +kernel)

end PrimeFactors.ComplementaryQuarticPopulation
