import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.SumGridPopulation
import PrimeFactors.FactorSum
import PrimeFactors.RecognizingQuarticProducts

/-! Count positive representations N=x⁴+4y⁴ below the next fourth power in
the full-width balanced semiprime population. The population bound uses every
allowable parameter pair, without assuming that either quartic factor is prime. -/
namespace PrimeFactors.QuarticPrimePopulation

open Finset
open MixedPrefixSample (eligible)
open RecognizingQuarticProducts (recognize factors)
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible

/-- Representations in the single fourth-power gap starting at x⁴. -/
def InFamily (n : ℕ) := ∃ x y : ℕ, 0<x ∧ 0<y ∧ n=x^4+4*y^4 ∧ n<(x+1)^4

noncomputable def family := eligible.filter (fun v => InFamily (v.1*v.2))

theorem mem_family {v : ℕ×ℕ} : v∈family ↔ v∈eligible ∧ InFamily (v.1*v.2) := mem_filter

theorem recognition {v : ℕ×ℕ} : v∈family ↔ v∈eligible ∧ (recognize (v.1*v.2)).isSome=true :=
  mem_family.trans (and_congr_right' RecognizingQuarticProducts.recognizes_iff.symm)

attribute [local irreducible] family

/-- When the product has 2048 bits, both the lower and upper edges restrict x.
The excess over x⁴ bounds y, even at the upper edge of its gap. -/
theorem parameters {n x y : ℕ} (large : 2^2047≤n) (small : n<2^2048)
    (form : n=x^4+4*y^4) (gap : n<(x+1)^4) :
    13*2^508≤x ∧ x<2^512 ∧ y<2^384 ∧ 6*y≤x := by
  have xTop : x<2^512 := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp
    rw [show ((2:ℕ)^512)^4=2^2048 by decide +kernel]
    omega
  have xLow : 13*2^508≤x := by
    by_contra! bad
    have low := Nat.pow_le_pow_left (show x+1≤13*2^508 by omega) 4
    have edge : (13*(2:ℕ)^508)^4<2^2047 := by decide +kernel
    exact not_le_of_gt (low.trans_lt edge) (large.trans gap.le)
  have ySmall : y^4<(x+1)^3 := by
    rw [form] at gap
    nlinarith only [gap,Nat.zero_le (x^2),Nat.zero_le x]
  have yTop : y<2^384 := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp
    exact ySmall.trans_le ((Nat.pow_le_pow_left xTop 3).trans_eq (by decide +kernel))
  exact ⟨xLow,xTop,yTop,by omega⟩

/-- On positive representations with x≥6y, the larger returned factor is
strictly less than twice the smaller one. -/
theorem balanced {x y : ℕ} (hy : 0<y) (room : 6*y≤x) :
    1<(factors x y).1 ∧ (factors x y).1<(factors x y).2 ∧ (factors x y).2<2*(factors x y).1 := by
  have proper := (RecognizingQuarticProducts.proper_iff (by omega : 0<x) hy).mpr
    (fun (h : (x,y)=(1,1)) => by cases h; omega)
  refine ⟨proper.1,proper.2.1,?_⟩
  have offset := Nat.mul_le_mul_right x room
  have pos : 0<y^2 := pow_pos hy _
  have order := two_mul_le_add_sq x y
  have sub : 2*x*y≤x^2+2*y^2 := by omega
  have add := Nat.sub_add_cancel sub
  dsimp [factors]
  nlinarith only [offset,pos,add]

private theorem eligible_bounds {v : ℕ×ℕ} (hv : v∈eligible) :
    2^2047≤v.1*v.2 ∧ v.1*v.2<2^2048 ∧ Odd (v.1*v.2) := by
  obtain ⟨pl,ord,qu,pp,qp,large⟩ := SumGridPopulation.eligible_data.mp hv
  have top := Nat.mul_lt_mul_of_pos_right (ord.trans qu) qp.pos
  have bound := top.trans_le (Nat.mul_le_mul_left B qu.le)
  have lower := (by decide +kernel : 2<X).trans_le pl
  exact ⟨large,bound.trans_eq (by decide +kernel),
    (pp.odd_of_ne_two lower.ne').mul (qp.odd_of_ne_two (lower.trans ord).ne')⟩

private theorem odd_parameter {n x y : ℕ} (odd : Odd n) (form : n=x^4+4*y^4) : x%2=1 := by
  have par := Nat.odd_iff.mp odd
  by_contra bad
  have even : x%2=0 := by omega
  have rem : x^4%2=0 := by rw [Nat.pow_mod,even]
  omega

private theorem bounded_encodings {α : Type*} (S : Finset α) (a b : ℕ)
    (prod : α→ℕ) (decode : ℕ×ℕ→ℕ) (inj : Set.InjOn prod (S:Set α))
    (code : ∀ v∈S, ∃ i<a, ∃ j<b, decode (i,j)=prod v) : S.card≤a*b := by
  choose i hi j hj value using (fun v : S => code v.val v.property)
  let f (v : S) : Fin a×Fin b := (⟨i v,hi v⟩,⟨j v,hj v⟩)
  have inject : Function.Injective f := by
    intro u v eq
    have x : i u=i v := congrArg (fun z : Fin a×Fin b => z.1.val) eq
    have y : j u=j v := congrArg (fun z : Fin a×Fin b => z.2.val) eq
    exact Subtype.ext (inj u.property v.property ((value u).symm.trans
      ((congrArg decode (Prod.ext x y)).trans (value v))))
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using
    Nat.card_le_card_of_injective f inject

private theorem count_parameters (S : Finset (ℕ×ℕ))
    (prime : ∀ v∈S, v.1.Prime ∧ v.2.Prime ∧ v.1<v.2)
    (params : ∀ v∈S, ∃ x y : ℕ, 13*2^508≤x ∧ x<2^512 ∧ x%2=1 ∧
      y<2^384 ∧ v.1*v.2=x^4+4*y^4) : S.card≤3*2^891 := by
  let prod (v : ℕ×ℕ) := v.1*v.2
  have inject : Set.InjOn prod (S:Set (ℕ×ℕ)) := by
    intro v hv w hw eq
    obtain ⟨p,q,vo⟩ := prime v hv
    obtain ⟨u,_,wo⟩ := prime w hw
    have same := ordered_semiprime_pair_unique p q vo.le wo.le u.one_lt eq.symm
    exact (Prod.ext same.1 same.2).symm
  let decode (z : ℕ×ℕ) := (2*(z.1+13*2^507)+1)^4+4*z.2^4
  have encoded : S.card≤(3*2^507)*2^384 := by
    apply bounded_encodings S _ _ prod decode inject
    intro v hv
    obtain ⟨x,y,lo,hi,par,yt,form⟩ := params v hv
    let i := x/2-13*2^507
    have code : i<3*2^507 ∧ 2*(i+13*2^507)+1=x := by dsimp only [i]; omega
    exact ⟨i,code.1,y,yt,by simp only [decode,code.2,prod,form]⟩
  exact encoded.trans_eq (by decide +kernel)

/-- Encoding odd x by its offset from the lower endpoint gives at most
3·2^507 first coordinates, with fewer than 2^384 possible y values. -/
theorem family_card : family.card≤3*2^891 := by
  apply count_parameters family
  · intro v hv
    obtain ⟨_,ord,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp (mem_family.mp hv).1
    exact ⟨pp,qp,ord⟩
  · intro v hv
    obtain ⟨eligibleV,x,y,_,_,form,gap⟩ := mem_family.mp hv
    obtain ⟨large,small,odd⟩ := eligible_bounds eligibleV
    obtain ⟨lo,hi,yt,_⟩ := parameters large small form gap
    exact ⟨x,y,lo,hi,odd_parameter odd form,yt,form⟩

/-- Strict unconditional upper share over sorted, distinct 1024-bit primes
whose product has 2048 bits. No quartic prime-value conjecture enters. -/
theorem population : 2^1129*family.card<eligible.card := by
  have lo := MixedPrefixSample.denominator ChebyshevPrimeSample.prime_count
  have cap := Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left (2^1129) family_card)
  have lim : 21000000*((2:ℕ)^1129*(3*2^891))<2^2046 := by decide +kernel
  exact Nat.lt_of_mul_lt_mul_left (cap.trans_lt (lim.trans lo))

end PrimeFactors.QuarticPrimePopulation
