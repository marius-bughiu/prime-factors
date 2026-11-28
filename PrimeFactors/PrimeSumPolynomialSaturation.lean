import PrimeFactors.PrimeSumPolynomialExtremum
import PrimeFactors.PrimeSumPolynomialStars

/-! Equality in the distinct-pair root bound forces the polynomial to
recognize all pairs containing one of a fixed number of field elements. -/

namespace PrimeFactors.PrimeSumPolynomialSaturation

open MvPolynomial Finset PrimeSumPolynomialGrid PrimeSumPolynomialExtremum
open scoped Classical

variable {K : Type*} [Field K] [Infinite K]

/-- Entries of the finite alphabet at which the relation holds for every
value of the other factor, as a polynomial identity. -/
noncomputable def whole (A : Finset K) (F : MvPolynomial (Fin 2) K) : Finset K :=
  A.filter (fun a => slice F a=0)

private theorem forced_card {k d n : ℕ} (kd : k≤d) (small : d<n-1)
    (bound : d*(n-1)+(n-d)*d ≤ k*(n-1)+(n-k)*d) : k=d := by
  by_contra neq
  have gap : k<d := lt_of_le_of_ne kd neq
  have dn : d≤n := by omega
  have kn := kd.trans dn
  have strict := Nat.mul_lt_mul_of_pos_left small (Nat.sub_pos_of_lt gap)
  zify [kd,dn,kn] at strict bound
  nlinarith only [strict,bound]

/-- Strictly below degree n−1, equality forces exactly d whole slices. -/
theorem whole_card (A : Finset K) (F : MvPolynomial (Fin 2) K) (nz : F≠0)
    (small : F.totalDegree<A.card-1)
    (saturated : ((hits A F).filter (fun z => z.1≠z.2)).card =
      F.totalDegree*(A.card-1)+(A.card-F.totalDegree)*F.totalDegree) :
    (whole A F).card=F.totalDegree := by
  apply forced_card (zero_slices A F nz) small
  rw [←saturated]
  simpa [whole] using count_by_slices A F true

omit [Field K] [Infinite K] in
private theorem impossible_extra (E : Finset K) {x : K} (out : x∉E) {d : ℕ}
    (full : E.card=d) (bound : (insert x E).card≤d) : False := by
  rw [card_insert_of_not_mem out,full] at bound
  omega

/-- Once d distinct whole slices are known, their entries characterize the
complete root relation on pairs from the field, including outside the grid. -/
theorem field_support (F : MvPolynomial (Fin 2) K) (nz : F≠0) (E : Finset K)
    (full : E.card=F.totalDegree) (entire : ∀ x∈E, slice F x=0) (a b : K) :
    eval ![a*b,a+b] F=0 ↔ a∈E ∨ b∈E := by
  have head {x : K} (hx : x∈E) (y : K) : eval ![x*y,x+y] F=0 := by
    rw [←eval_slice,entire x hx,Polynomial.eval_zero]
  have tail (x : K) {y : K} (hy : y∈E) : eval ![x*y,x+y] F=0 := by
    rw [mul_comm,add_comm]
    exact head hy x
  refine ⟨?_,fun h => h.elim (fun ha => head ha b) (tail a)⟩
  intro root
  by_contra! outside
  obtain ⟨ha,hb⟩ := outside
  have nzrow : slice F a≠0 := by
    intro z
    apply impossible_extra E ha full
    have all : (insert a E).filter (fun x => slice F x=0)=insert a E := by
      apply filter_eq_self.mpr
      intro x hx
      rcases mem_insert.mp hx with rfl|hx
      · exact z
      · exact entire x hx
    rw [←all]
    exact zero_slices (insert a E) F nz
  apply impossible_extra E hb full
  apply le_trans _ (degree_slice F a)
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  apply (Polynomial.mem_roots nzrow).mpr
  rw [Polynomial.IsRoot.def,eval_slice]
  rcases mem_insert.mp hx with rfl|hx
  · exact root
  · exact tail a hx

/-- Attaining the distinct-pair bound determines the zero pattern globally.
Exactly the pairs with at least one entry in `whole A F` satisfy F. -/
theorem classification (A : Finset K) (F : MvPolynomial (Fin 2) K) (nz : F≠0)
    (small : F.totalDegree<A.card-1)
    (saturated : ((hits A F).filter (fun z => z.1≠z.2)).card =
      F.totalDegree*(A.card-1)+(A.card-F.totalDegree)*F.totalDegree) :
    (whole A F).card=F.totalDegree ∧
    ∀ a b : K, eval ![a*b,a+b] F=0 ↔ a∈whole A F ∨ b∈whole A F := by
  have card := whole_card A F nz small saturated
  exact ⟨card,field_support F nz _ card (fun _ h => (mem_filter.mp h).2)⟩

private theorem distinct_area {n d : ℕ} (small : d<n-1) :
    (n^2-n)-((n-d)^2-(n-d))=d*(n-1)+(n-d)*d := by
  have square (m : ℕ) : m≤m^2 := by cases m <;> nlinarith
  have dn : d≤n := by omega
  have pos : 1≤n := by omega
  apply Nat.sub_eq_of_eq_add
  zify [square n,square (n-d),dn,pos]
  ring

/-- The number of whole slices also suffices for equality. -/
theorem saturation_iff (A : Finset K) (F : MvPolynomial (Fin 2) K) (nz : F≠0)
    (small : F.totalDegree<A.card-1) :
    ((hits A F).filter (fun z => z.1≠z.2)).card =
      F.totalDegree*(A.card-1)+(A.card-F.totalDegree)*F.totalDegree ↔
    (whole A F).card=F.totalDegree := by
  refine ⟨whole_card A F nz small,?_⟩
  intro full
  let E := whole A F
  have support := field_support F nz E full (fun _ h => (mem_filter.mp h).2)
  have eq : (hits A F).filter (fun z => z.1≠z.2) =
      A.offDiag.filter (fun v => eval ![v.1*v.2,v.1+v.2] (PrimeSumPolynomialStars.stars E)=0) := by
    ext ⟨a,b⟩
    simp only [mem_filter,mem_hits,mem_offDiag,support,PrimeSumPolynomialStars.eval_zero]
    tauto
  rw [eq,PrimeSumPolynomialStars.distinct_count A E (filter_subset ..),show E.card=F.totalDegree from full]
  exact distinct_area small

/-- At the excluded endpoint n=2, d=1, the line S=3 covers both distinct
ordered pairs on {1,2} although no factor gives a whole slice. -/
theorem endpoint_example :
    let F : MvPolynomial (Fin 2) ℚ := X 1+C (-3)
    F.totalDegree=1 ∧
    (∀ a∈({1,2} : Finset ℚ), ∀ b∈({1,2} : Finset ℚ), a≠b → eval ![a*b,a+b] F=0) ∧
    (∀ a : ℚ, slice F a≠0) := by
  dsimp only
  constructor
  · rw [totalDegree_add_eq_left_of_totalDegree_lt (by simp),totalDegree_X]
  constructor
  · intro a ha b hb ne
    simp only [mem_insert,mem_singleton] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> norm_num at *
  · intro a h
    have e := congrArg (Polynomial.eval (4-a)) h
    rw [eval_slice,Polynomial.eval_zero] at e
    simp at e
    linarith

end PrimeFactors.PrimeSumPolynomialSaturation
