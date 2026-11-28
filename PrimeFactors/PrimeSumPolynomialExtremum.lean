import PrimeFactors.PrimeSumPolynomialGrid
import Mathlib.Algebra.MvPolynomial.Funext

/-! Exact finite-grid bounds for polynomial relations between a product
and its factor sum. Fixing either factor gives a univariate polynomial
whose degree is at most the total degree of the original relation. -/
namespace PrimeFactors.PrimeSumPolynomialExtremum

open Finset MvPolynomial PrimeSumPolynomialGrid
open scoped Classical

variable {K : Type*} [Field K]

noncomputable def slice (F : MvPolynomial (Fin 2) K) (a : K) : Polynomial K :=
  aeval ![Polynomial.C a*Polynomial.X,Polynomial.C a+Polynomial.X] F

theorem eval_slice (F : MvPolynomial (Fin 2) K) (a b : K) :
    (slice F a).eval b = eval ![a*b,a+b] F := by
  change Polynomial.aeval b (aeval _ F) = _
  rw [MvPolynomial.comp_aeval_apply]
  change aeval _ F = aeval _ F
  apply congrArg (fun v : Fin 2 → K => aeval v F)
  funext i
  fin_cases i <;> simp

theorem degree_slice (F : MvPolynomial (Fin 2) K) (a : K) :
    (slice F a).natDegree ≤ F.totalDegree := by
  classical
  let v : Fin 2 → Polynomial K := ![Polynomial.C a*Polynomial.X,Polynomial.C a+Polynomial.X]
  have small (i : Fin 2) : (v i).natDegree≤1 := by
    fin_cases i
    · exact (Polynomial.natDegree_C_mul_le ..).trans (by simp)
    · simp [v]
  change (F.eval₂ Polynomial.C v).natDegree ≤ _
  rw [eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply (Polynomial.natDegree_C_mul_le ..).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  have cap := MvPolynomial.le_totalDegree hm
  rw [Finsupp.sum_fintype m (fun _ e => e) (fun _ => rfl)] at cap
  apply le_trans _ cap
  exact sum_le_sum fun i _ => (Polynomial.natDegree_pow_le ..).trans
    ((Nat.mul_le_mul_left _ (small i)).trans (by simp))

private theorem root_bound [DecidableEq K] (A : Finset K) (f : Polynomial K) (nz : f≠0) :
    (A.filter (fun x => f.eval x=0)).card≤f.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  exact (Polynomial.mem_roots nz).mpr (mem_filter.mp hx).2

/-- At most d factors can make the whole one-variable equation vanish. -/
theorem zero_slices [Infinite K] [DecidableEq (Polynomial K)] (A : Finset K)
    (F : MvPolynomial (Fin 2) K) (nz : F≠0) :
    (A.filter (fun x => slice F x=0)).card≤F.totalDegree := by
  classical
  have witness : ∃ v : Fin 2 → K, eval v (pull F)≠0 := by
    by_contra! zero
    exact pull_ne_zero nz (MvPolynomial.funext (fun v => by simp [zero]))
  obtain ⟨v,hv⟩ := witness
  have nonzero : slice F (v 1)≠0 := by
    intro h
    apply hv
    have e := congrArg (Polynomial.eval (v 0)) h
    simpa only [eval_pull,eval_slice,Polynomial.eval_zero,mul_comm,add_comm] using e
  apply le_trans _ (degree_slice F (v 1))
  apply le_trans _ (root_bound A _ nonzero)
  apply card_le_card
  intro x hx
  obtain ⟨mem,zero⟩ := mem_filter.mp hx
  refine mem_filter.mpr ⟨mem,?_⟩
  have e := congrArg (Polynomial.eval (v 1)) zero
  simpa only [eval_slice,Polynomial.eval_zero,mul_comm,add_comm] using e

/-- Degree and the number of entire rows together control the number of
hits. The optional distinctness condition removes the diagonal exactly. -/
theorem count_by_slices (A : Finset K) (F : MvPolynomial (Fin 2) K)
    (distinct : Bool) :
    let d := F.totalDegree
    let n := A.card
    let h := if distinct then 1 else 0
    let k := (A.filter (fun x => slice F x=0)).card
    ((hits A F).filter (fun z => distinct=true → z.1≠z.2)).card
      ≤ k*(n-h)+(n-k)*d := by
  classical
  let d := F.totalDegree
  let n := A.card
  let h : ℕ := if distinct then 1 else 0
  let E := A.filter (fun x => slice F x=0)
  let k := E.card
  let R (x y : K) := (slice F x).eval y=0 ∧ (distinct=true → x≠y)
  have rows :
      ((hits A F).filter (fun z => distinct=true → z.1≠z.2)).card=
        ∑ x∈A, (A.filter (R x)).card := by
    have eq : (hits A F).filter (fun z => distinct=true → z.1≠z.2) =
        (A×ˢA).filter (fun z => R z.1 z.2) := by
      ext z
      simp only [mem_filter,mem_hits,mem_product,R,eval_slice]
      tauto
    simp only [eq,card_filter,sum_product]
  have whole (x : K) (mem : x∈A) : (A.filter (R x)).card≤n-h := by
    cases distinct with
    | false => exact card_filter_le ..
    | true =>
      have sub : A.filter (R x) ⊆ A.erase x := by
        intro y hy
        obtain ⟨ay,_,diff⟩ := mem_filter.mp hy
        exact mem_erase.mpr ⟨(diff rfl).symm,ay⟩
      exact (card_le_card sub).trans (card_erase_of_mem mem).le
  have rest (x : K) (mem : x∈A) (out : x∉E) : (A.filter (R x)).card≤d := by
    have sx : slice F x≠0 := fun zero => out (mem_filter.mpr ⟨mem,zero⟩)
    apply le_trans _ ((root_bound A _ sx).trans (degree_slice F x))
    apply card_le_card
    intro y hy
    obtain ⟨ym,root,_⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨ym,root⟩
  have ex := filter_subset (fun x => slice F x=0) A
  rw [rows,←sum_sdiff ex (f:=fun x => (A.filter (R x)).card)]
  calc
    _ ≤ (∑ _x∈A\E, d)+(∑ _x∈E, (n-h)) :=
      Nat.add_le_add (sum_le_sum fun x hx => rest x (mem_sdiff.mp hx).1 (mem_sdiff.mp hx).2)
        (sum_le_sum fun x hx => whole x (ex hx))
    _ = _ := by
      have size : (A\E).card=n-k := card_sdiff ex
      simp only [sum_const,nsmul_eq_mul,size]
      exact Nat.add_comm ..

private theorem row_count [Infinite K] (A : Finset K) (F : MvPolynomial (Fin 2) K)
    (nz : F≠0) (distinct : Bool) :
    let d := F.totalDegree
    let n := A.card
    let h := if distinct then 1 else 0
    d≤n-h →
      ((hits A F).filter (fun z => distinct=true → z.1≠z.2)).card
        ≤ d*(n-h)+(n-d)*d := by
  classical
  let E := A.filter (fun x => slice F x=0)
  let k := E.card
  dsimp only
  let d := F.totalDegree
  let n := A.card
  let h : ℕ := if distinct then 1 else 0
  have ke : k≤d := zero_slices A F nz
  have kn : k≤n := card_le_card (filter_subset ..)
  intro dn
  apply (count_by_slices A F distinct).trans
  change k*(n-h)+(n-k)*d ≤ d*(n-h)+(n-d)*d
  change d≤n-h at dn
  have dn' := dn.trans (Nat.sub_le n h)
  have loss := Nat.mul_le_mul_left (d-k) dn
  zify [ke,kn,dn'] at loss ⊢
  nlinarith only [loss]

/-- The exact upper bound on the full ordered grid of n entries is
n²−(n−d)² when d≤n. A polynomial encoding any d entries attains it. -/
theorem full_grid [Infinite K] (A : Finset K) (F : MvPolynomial (Fin 2) K)
    (nz : F≠0) (cap : F.totalDegree≤A.card) :
    (hits A F).card≤A.card^2-(A.card-F.totalDegree)^2 := by
  have bound := row_count A F nz false (by simpa using cap)
  simp at bound
  have sub := Nat.sub_add_cancel cap
  have area : A.card^2=(A.card-F.totalDegree)^2+
      (F.totalDegree*A.card+(A.card-F.totalDegree)*F.totalDegree) := by
    nlinarith only [congrArg (fun x : ℕ => x^2) sub,
      congrArg (fun x : ℕ => F.totalDegree*x) sub]
  omega

/-- Removing the diagonal improves the sharp bound by d. Both ordered
copies of a pair of different factors are included in the count. -/
theorem distinct_grid [Infinite K] (A : Finset K) (F : MvPolynomial (Fin 2) K)
    (nz : F≠0) (cap : F.totalDegree≤A.card-1) :
    ((hits A F).filter (fun z => z.1≠z.2)).card ≤
      F.totalDegree*(A.card-1)+(A.card-F.totalDegree)*F.totalDegree := by
  simpa using row_count A F nz true (by simpa using cap)

end PrimeFactors.PrimeSumPolynomialExtremum
