import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! Covering pairs by a polynomial whose coefficients encode a finite set
of selected entries. With prime entries these are precisely the semiprime
pairs having a selected factor. No primality assumption is needed for the
polynomial identity or for the cardinalities. -/
namespace PrimeFactors.PrimeSumPolynomialStars

open Finset MvPolynomial
open scoped Classical

variable {K : Type*} [CommRing K] [IsDomain K]

/-- One linear condition in the product (variable zero) and sum (variable one). -/
noncomputable def line (a : K) : MvPolynomial (Fin 2) K :=
  X 0 + (C (-a)*X 1+C (a^2))

/-- The selected entries occur explicitly in the factors of this polynomial. -/
noncomputable def stars (E : Finset K) := ∏ a∈E,line a

omit [IsDomain K] in
theorem eval_line (a p q : K) :
    eval ![p*q,p+q] (line a)=(p-a)*(q-a) := by
  simp [line]
  ring

theorem eval_zero (E : Finset K) (p q : K) :
    eval ![p*q,p+q] (stars E)=0 ↔ p∈E ∨ q∈E := by
  simp only [stars,map_prod,eval_line,prod_eq_zero_iff,mul_eq_zero,sub_eq_zero]
  constructor
  · rintro ⟨a,ha,h|h⟩ <;> subst a <;> tauto
  · rintro (h|h)
    · exact ⟨p,h,Or.inl rfl⟩
    · exact ⟨q,h,Or.inr rfl⟩

private theorem degree_line_le (a : K) : (line a).totalDegree≤1 := by
  have coeff : (C (-a)*X (1:Fin 2)).totalDegree≤1 :=
    (totalDegree_mul ..).trans (by simp)
  apply (totalDegree_add ..).trans
  exact max_le (by simp) ((totalDegree_add ..).trans (max_le coeff
    (by rw [totalDegree_C]; decide)))

omit [IsDomain K] in
/-- The polynomial is monic of degree one in the product variable. -/
private theorem univariate_line (a : K) :
    finSuccEquiv K 1 (line a) =
      Polynomial.X + Polynomial.C (C (-a)*X (0:Fin 1)+C (a^2)) := by
  have liftC (v : K) : finSuccEquiv K 1 (C v) = Polynomial.C (C v) := by
    rw [finSuccEquiv_apply,eval₂Hom_C]
    rfl
  have x1 : finSuccEquiv K 1 (X (1:Fin 2))=Polynomial.C (X (0:Fin 1)) :=
    finSuccEquiv_X_succ (j:=0)
  simp only [line,map_add,map_mul,finSuccEquiv_X_zero,liftC,x1]

theorem stars_ne_zero (E : Finset K) : stars E≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro a _ zero
  have image := univariate_line a
  rw [zero,map_zero] at image
  exact (Polynomial.monic_X_add_C _).ne_zero image.symm

/-- Both the total degree and the degree in the product variable are exactly
the number of selected entries, including the empty-set case. -/
theorem degrees (E : Finset K) :
    (stars E).degreeOf 0=E.card ∧ (stars E).totalDegree=E.card := by
  have deg : (stars E).degreeOf 0=E.card := by
    rw [←natDegree_finSuccEquiv,stars,map_prod]
    simp only [univariate_line]
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun a _ => Polynomial.monic_X_add_C _)]
    simp only [Polynomial.natDegree_X_add_C,sum_const,nsmul_eq_mul,Nat.cast_id,mul_one]
  refine ⟨deg,le_antisymm ?_ (deg ▸ degreeOf_le_totalDegree (stars E) 0)⟩
  calc
    _ ≤ ∑ a∈E,(line a).totalDegree := totalDegree_finset_prod ..
    _ ≤ ∑ _a∈E,1 := sum_le_sum (fun a _ => degree_line_le a)
    _ = _ := by simp

/-- Ordered pairs, including the diagonal. -/
theorem grid_count (A E : Finset K) (sub : E⊆A) :
    ((A×ˢA).filter (fun v => eval ![v.1*v.2,v.1+v.2] (stars E)=0)).card =
      A.card^2-(A.card-E.card)^2 := by
  let P (v : K×K) := eval ![v.1*v.2,v.1+v.2] (stars E)=0
  have misses : ((A×ˢA).filter (fun v => ¬P v))=(A\E)×ˢ(A\E) := by
    ext ⟨p,q⟩
    simp only [P,mem_filter,mem_product,eval_zero,mem_sdiff]
    tauto
  have census := filter_card_add_filter_neg_card_eq_card (s:=A×ˢA) P
  rw [misses,card_product,card_sdiff sub,card_product] at census
  change ((A×ˢA).filter P).card=_
  rw [pow_two,pow_two]
  omega

/-- Ordered distinct pairs. When A consists of primes each supported
semiprime appears in exactly the two possible orders. -/
theorem distinct_count (A E : Finset K) (sub : E⊆A) :
    (A.offDiag.filter (fun v => eval ![v.1*v.2,v.1+v.2] (stars E)=0)).card =
      (A.card^2-A.card)-((A.card-E.card)^2-(A.card-E.card)) := by
  let P (v : K×K) := eval ![v.1*v.2,v.1+v.2] (stars E)=0
  have misses : (A.offDiag.filter (fun v => ¬P v))=(A\E).offDiag := by
    ext ⟨p,q⟩
    simp only [P,mem_filter,mem_offDiag,eval_zero,mem_sdiff]
    tauto
  have census := filter_card_add_filter_neg_card_eq_card (s:=A.offDiag) P
  rw [misses,offDiag_card,card_sdiff sub,offDiag_card] at census
  change (A.offDiag.filter P).card=_
  rw [pow_two,pow_two]
  omega

omit [CommRing K] [IsDomain K] in
/-- Counting each two-element subset once removes both the diagonal
and duplication from the order of its two entries. -/
theorem unordered_count (A E : Finset K) (sub : E⊆A) :
    ((A.powersetCard 2).filter fun pair => (pair∩E).Nonempty).card =
      A.card.choose 2-(A.card-E.card).choose 2 := by
  have misses : ((A.powersetCard 2).filter (fun pair => ¬(pair∩E).Nonempty)) =
      (A\E).powersetCard 2 := by
    ext pair
    simp only [mem_filter,mem_powersetCard,subset_iff,Finset.Nonempty,mem_inter,mem_sdiff]
    constructor
    · rintro ⟨⟨inside,size⟩,miss⟩
      exact ⟨fun x hx => ⟨inside hx,fun hxE => miss ⟨x,hx,hxE⟩⟩,size⟩
    · rintro ⟨inside,size⟩
      exact ⟨⟨fun _ hx => (inside hx).1,size⟩,fun ⟨_,hx,hxE⟩ => (inside hx).2 hxE⟩
  have census := filter_card_add_filter_neg_card_eq_card (s:=A.powersetCard 2)
    (fun pair => (pair∩E).Nonempty)
  rw [misses,card_powersetCard,card_sdiff sub,card_powersetCard] at census
  omega

end PrimeFactors.PrimeSumPolynomialStars
