import PrimeFactors.PrimeSumPolynomialPopulation

/-! An additive error window for a fixed integer polynomial in the product.
The integer prediction gives one shifted graph per permitted signed error.
The bounds below concern integer-coefficient polynomials evaluated exactly. -/

namespace PrimeFactors.PrimeSumPolynomialWindow

open Finset MvPolynomial PrimeSumPolynomialPopulation
open MixedPrefixSample (eligible)

set_option exponentiation.threshold 2048

abbrev Poly := MvPolynomial (Fin 2) ℚ

private noncomputable def prediction (P : Polynomial ℤ) : Poly :=
  ∑ i∈P.support, C (P.coeff i : ℚ)*(X 0)^i

private theorem eval_prediction (P : Polynomial ℤ) (n s : ℤ) :
    eval ![(n:ℚ),(s:ℚ)] (prediction P)=((P.eval n:ℤ):ℚ) := by
  simp [prediction,Polynomial.eval_eq_sum,Polynomial.sum_def]

/-- The graph with signed error j; variable 0 is the product and 1 is the sum. -/
noncomputable def graph (P : Polynomial ℤ) (j : ℤ) : Poly := X 1-prediction P-C (j:ℚ)

theorem eval_graph (P : Polynomial ℤ) (j n s : ℤ) :
    eval ![(n:ℚ),(s:ℚ)] (graph P j)=((s-P.eval n-j:ℤ):ℚ) := by
  simp [graph,eval_prediction]

theorem graph_ne_zero (P : Polynomial ℤ) (j : ℤ) : graph P j≠0 := by
  intro h
  have ev := eval_graph P j 0 (P.eval 0+j+1)
  rw [h,map_zero] at ev
  have e : (0:ℤ)=(P.eval 0+j+1)-P.eval 0-j := by exact_mod_cast ev
  omega

theorem graph_degree (P : Polynomial ℤ) (j : ℤ) :
    (graph P j).totalDegree≤max 1 P.natDegree := by
  have d : (prediction P).totalDegree≤P.natDegree := by
    apply totalDegree_finsetSum_le
    intro i hi
    exact (totalDegree_mul ..).trans (by
      simpa only [totalDegree_C,totalDegree_X_pow,zero_add] using Polynomial.le_natDegree_of_mem_supp _ hi)
  apply (totalDegree_sub ..).trans
  apply max_le _ (by rw [totalDegree_C]; omega)
  exact (totalDegree_sub ..).trans (by simpa only [totalDegree_X] using max_le_max_left 1 d)

/-- Product of all shifted graphs, allowing every integer error from −E to E. -/
noncomputable def window (P : Polynomial ℤ) (E : ℕ) : Poly :=
  ∏ j ∈ Icc (-(E:ℤ)) E, graph P j

theorem window_ne_zero (P : Polynomial ℤ) (E : ℕ) : window P E≠0 :=
  prod_ne_zero_iff.mpr fun j _ => graph_ne_zero P j

theorem window_degree (P : Polynomial ℤ) (E : ℕ) :
    (window P E).totalDegree≤(2*E+1)*max 1 P.natDegree := by
  apply (totalDegree_finset_prod ..).trans
  have card : (Icc (-(E:ℤ)) E).card=2*E+1 := by rw [Int.card_Icc]; omega
  simpa only [sum_const,card,nsmul_eq_mul] using
    (sum_le_sum (s:=Icc (-(E:ℤ)) E) (fun j _ => graph_degree P j))

/-- Exact equivalence between being in an integer error window and lying
on one of its shifted polynomial graphs. -/
theorem window_zero (P : Polynomial ℤ) (E : ℕ) (n s : ℤ) :
    eval ![(n:ℚ),(s:ℚ)] (window P E)=0 ↔ |s-P.eval n|≤E := by
  classical
  simp only [window,map_prod,prod_eq_zero_iff,mem_Icc,eval_graph,Int.cast_eq_zero]
  constructor
  · rintro ⟨j,⟨lo,hi⟩,eq⟩
    rw [abs_le]
    omega
  · intro h
    exact ⟨s-P.eval n,abs_le.mp h,by omega⟩

/-- Eligible prime pairs where the predicted sum meets the stated tolerance. -/
noncomputable abbrev predicted (P : Polynomial ℤ) (E : ℕ) :=
  hits (fun n s => |(s:ℤ)-P.eval (n:ℤ)|≤(E:ℤ))

private theorem same_hits (P : Polynomial ℤ) (E : ℕ) :
    predicted P E=zeros (window P E) := by
  classical
  ext z
  simp only [predicted,zeros,hits,mem_filter]
  apply and_congr_right
  intro _
  simpa only [Int.cast_natCast] using (window_zero P E (z.1*z.2:ℕ) (z.1+z.2:ℕ)).symm

/-- A fixed polynomial and its whole integer error window have no greater
coverage than a single relation with the indicated total-degree budget. -/
theorem budget (P : Polynomial ℤ) (E : ℕ) {k : ℕ} (limit : k≤1007)
    (cap : (2*E+1)*max 1 P.natDegree≤2^k) :
    2^(1007-k)*(predicted P E).card<eligible.card := by
  rw [same_hits]
  exact polynomial_budget (window P E) (window_ne_zero P E) limit ((window_degree P E).trans cap)

/-- Error at most 2^128 and polynomial degree at most 2^32. -/
theorem full_width (P : Polynomial ℤ) (deg : P.natDegree≤2^32) :
    2^845*(predicted P (2^128)).card<eligible.card := by
  apply budget P _ (k:=162) (by decide)
  exact (Nat.mul_le_mul_left _ (max_le (by decide : 1≤2^32) deg)).trans (by decide)

/-- Fixed constant and linear predictions with the same 128-bit radius. -/
theorem linear (P : Polynomial ℤ) (deg : P.natDegree≤1) :
    2^877*(predicted P (2^128)).card<eligible.card := by
  apply budget P _ (k:=130) (by decide)
  rw [max_eq_left deg, mul_one]
  decide

/-- A constant prediction of 20 and radius 2 includes the sums of 7·11 and
5·17 at its endpoints. The sum of 11·13 is the next even value above them. -/
theorem toy :
    eval ![(77:ℚ),(18:ℚ)] (window (Polynomial.C 20) 2)=0 ∧
    eval ![(85:ℚ),(22:ℚ)] (window (Polynomial.C 20) 2)=0 ∧
    eval ![(143:ℚ),(24:ℚ)] (window (Polynomial.C 20) 2)≠0 := by
  have check (n s : ℤ) := window_zero (Polynomial.C 20) 2 n s
  exact ⟨(check 77 18).mpr (by norm_num), (check 85 22).mpr (by norm_num),
    fun h => by have bad := (check 143 24).mp h; norm_num at bad⟩

end PrimeFactors.PrimeSumPolynomialWindow
