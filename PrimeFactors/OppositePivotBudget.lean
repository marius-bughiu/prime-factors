import PrimeFactors.LabelPolynomialBudget
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic

/-! Finite-field nonvanishing and zero counts for intermediate Hurwitz minors
of a split monic polynomial. We build the symbolic minors using positive elementary
symmetric polynomials. Row signs recover the coefficients of ∏ (X − tᵢ). -/
namespace PrimeFactors.OppositePivotBudget

open MvPolynomial Finset
open scoped BigOperators

private def coefficient {R : Type*} [CommRing R] {m : ℕ} (a : Fin m → R) (d : ℕ) : R :=
  if _ : d = 0 then 1 else if h : d ≤ m then a ⟨d-1,by omega⟩ else 0

/-- Row i, column j has the coefficient with one-based index 2j−i.
Negative indices and indices above the true degree give zero. -/
noncomputable def block {R : Type*} [CommRing R] {m : ℕ} (a : Fin m → R) (k : ℕ) :
    Matrix (Fin k) (Fin k) R := fun i j =>
  if i.val+1 ≤ 2*(j.val+1) then coefficient a (2*(j.val+1)-(i.val+1)) else 0

private theorem map_det {R T : Type*} [CommRing R] [CommRing T] {m : ℕ}
    (f : R →+* T) (a : Fin m → R) (k : ℕ) :
    f (block a k).det = (block (fun i => f (a i)) k).det := by
  rw [f.map_det]
  congr 1
  ext i j
  change f (block a k i j) = _
  simp only [block,coefficient]
  split_ifs <;> simp_all

/-- Permutation giving the single nonzero coefficient in each specialized row. -/
private def chosen {k : ℕ} (i : Fin k) : Fin k :=
  ⟨if i.val % 2 = 1 then i.val/2 else i.val/2 + k/2, by split <;> have := i.isLt <;> omega⟩

private theorem chosen_injective (k : ℕ) : Function.Injective (@chosen k) := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  replace h := congrArg Fin.val h
  simp only [chosen] at h
  split_ifs at h <;> omega

/-- Leaving only coefficients at indices 0 and 2⌊k/2⌋+1 turns the minor into
a permutation matrix, with determinant a unit in every coefficient field. -/
theorem determinant_witness {K : Type*} [Field K] {m k : ℕ} (small : k < m) :
    let a : Fin m → K := fun z => if z.val+1=2*(k/2)+1 then 1 else 0
    (block a k).det ≠ 0 := by
  intro a
  let perm := Equiv.ofBijective (@chosen k) ⟨chosen_injective k,
    Finite.surjective_of_injective (chosen_injective k)⟩
  have mat : block a k = (1 : Matrix (Fin k) (Fin k) K).submatrix perm id := by
    ext i j
    have hi := i.isLt
    have hj := j.isLt
    change block a k i j = (1 : Matrix (Fin k) (Fin k) K) (chosen i) j
    rw [Matrix.one_apply]
    by_cases eq : chosen i = j
    · rw [if_pos eq]
      have v := congrArg Fin.val eq
      simp only [chosen] at v
      simp only [block,coefficient,a]
      split_ifs <;> split_ifs at v <;> first | rfl | omega
    · rw [if_neg eq]
      have v : (chosen i).val ≠ j.val := fun h => eq (Fin.ext h)
      simp only [chosen] at v
      simp only [block,coefficient,a]
      split_ifs <;> split_ifs at v <;> first | rfl | omega
  rw [mat, Matrix.det_permute, Matrix.det_one,mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign perm) with h|h <;> simp [h]

/-- The determinant as a polynomial in the m (negated) roots. -/
noncomputable def minor (K : Type*) [Field K] (m k : ℕ) : MvPolynomial (Fin m) K :=
  (block (fun i : Fin m => esymm (Fin m) K (i.val+1)) k).det

theorem minor_ne_zero (K : Type*) [Field K] {m k : ℕ} (small : k < m) :
    minor K m k ≠ 0 := by
  classical
  let A := (block (fun i : Fin m => (X i : MvPolynomial (Fin m) K)) k).det
  have formal : A ≠ 0 := by
    intro h
    let points : Fin m → K := fun z => if z.val+1=2*(k/2)+1 then 1 else 0
    have e := map_det (eval points) (fun i : Fin m => (X i : MvPolynomial (Fin m) K)) k
    change eval points A = _ at e
    rw [h,map_zero] at e
    exact determinant_witness (K:=K) small (by simpa only [eval_X] using e.symm)
  let f := esymmAlgHom (Fin m) K m
  have image : (f A).val = minor K m k := by
    rw [esymmAlgHom_apply]
    unfold A minor
    let g : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K :=
      aeval (fun i : Fin m => esymm (Fin m) K (i.val+1))
    have z := map_det g.toRingHom (fun i : Fin m => (X i : MvPolynomial (Fin m) K)) k
    simpa only [g,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,aeval_X] using z
  intro h
  have vanish : f A = f 0 := by
    apply Subtype.ext
    rw [image,h,map_zero]
    rfl
  exact formal ((esymmAlgHom_fin_injective K le_rfl) vanish)

private theorem degree_esymm {K : Type*} [Field K] (m i : ℕ) :
    (esymm (Fin m) K i).totalDegree ≤ i := by
  classical
  apply totalDegree_finsetSum_le
  intro s hs
  apply (totalDegree_finset_prod _ _).trans
  have size := (mem_powersetCard.mp hs).2
  simp [totalDegree_X,size]

private theorem degree_block {K : Type*} [Field K] {m k : ℕ}
    (i j : Fin k) :
    (block (fun a : Fin m => esymm (Fin m) K (a.val+1)) k i j).totalDegree ≤ m := by
  simp only [block,coefficient]
  split_ifs <;> first | simp | exact (degree_esymm _ _).trans (by omega)

theorem degree_minor (K : Type*) [Field K] (m k : ℕ) :
    (minor K m k).totalDegree ≤ k*m := by
  classical
  unfold minor
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro perm _
  have b : (∏ i, block (fun a : Fin m => esymm (Fin m) K (a.val+1)) k (perm i) i).totalDegree ≤ k*m := by
    apply (totalDegree_finset_prod _ _).trans
    calc _ ≤ ∑ _ : Fin k, m := sum_le_sum fun i _ => degree_block (perm i) i
         _ = _ := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign perm) with h|h <;> simpa [h,Units.smul_def] using b

private theorem degree_block_index {K : Type*} [Field K] {m k : ℕ} (i j : Fin k) :
    (block (fun a : Fin m => esymm (Fin m) K (a.val+1)) k i j).totalDegree ≤
      2*(j.val+1)-(i.val+1) := by
  simp only [block,coefficient]
  split_ifs <;> first | simp | exact (degree_esymm _ _).trans (by omega)

private theorem twice_index_sum (k : ℕ) :
    2 * (∑ i : Fin k, (i.val+1)) = k*(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc,Fin.val_last]
    nlinarith

/-- Every nonzero term uses entries whose indices sum to the triangular
number k(k+1)/2. This degree bound also holds for truncated blocks. -/
theorem degree_minor_triangular (K : Type*) [Field K] (m k : ℕ) :
    (minor K m k).totalDegree ≤ k*(k+1)/2 := by
  classical
  let M := block (fun a : Fin m => esymm (Fin m) K (a.val+1)) k
  unfold minor
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro perm _
  change (Equiv.Perm.sign perm • ∏ i, M (perm i) i).totalDegree ≤ _
  by_cases z : (∏ i, M (perm i) i) = 0
  · simp [z]
  have admissible (i : Fin k) : (perm i).val+1 ≤ 2*(i.val+1) := by
    by_contra! h
    exact z (prod_eq_zero (mem_univ i) (by simp [M,block,not_le.mpr h]))
  have sum_indices :
      (∑ i : Fin k, (2*(i.val+1)-((perm i).val+1))) +
      (∑ i : Fin k, ((perm i).val+1)) = 2 * (∑ i : Fin k, (i.val+1)) := by
    rw [←sum_add_distrib,mul_sum]
    apply sum_congr rfl
    intro i _
    exact Nat.sub_add_cancel (admissible i)
  rw [Equiv.sum_comp perm (fun i : Fin k => i.val+1)] at sum_indices
  have degree : (∏ i, M (perm i) i).totalDegree ≤ k*(k+1)/2 := by
    apply (totalDegree_finset_prod _ _).trans
    calc
      _ ≤ ∑ i : Fin k, (2*(i.val+1)-((perm i).val+1)) :=
        sum_le_sum fun i _ => degree_block_index (perm i) i
      _ ≤ _ := by have := twice_index_sum k; omega
  rcases Int.units_eq_one_or (Equiv.Perm.sign perm) with h|h <;>
    simpa [h,Units.smul_def] using degree

/-- Principal minors with the parity of the Euclidean chain and strictly before
its resultant. Index zero is the empty determinant. -/
noncomputable def pivotIndices (m : ℕ) : Finset ℕ :=
  (range (m-1)).filter (fun k => 0 < k ∧ k%2 ≠ m%2)

/-- Product of all intermediate principal Hurwitz minors in root variables. -/
noncomputable def obstruction (K : Type*) [Field K] (m : ℕ) : MvPolynomial (Fin m) K :=
  ∏ k ∈ pivotIndices m, minor K m k

theorem obstruction_ne_zero (K : Type*) [Field K] (m : ℕ) :
    obstruction K m ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have := mem_range.mp (mem_filter.mp hk).1
  exact minor_ne_zero K (by omega)

theorem obstruction_totalDegree (K : Type*) [Field K] (m : ℕ) :
    (obstruction K m).totalDegree ≤ m^3 := by
  classical
  apply (totalDegree_finset_prod _ _).trans
  calc
    _ ≤ ∑ _ ∈ pivotIndices m, m*m := by
      apply sum_le_sum
      intro k hk
      have := mem_range.mp (mem_filter.mp hk).1
      exact (degree_minor K m k).trans (Nat.mul_le_mul_right m (by omega))
    _ = (pivotIndices m).card * (m*m) := by simp
    _ ≤ m * (m*m) := by
      apply Nat.mul_le_mul_right
      exact (card_filter_le ..).trans (by rw [card_range]; omega)
    _ = m^3 := by ring

/-- Degree budget that retains the actual parity and every intermediate pivot. -/
noncomputable def degreeBudget (m : ℕ) : ℕ := ∑ k ∈ pivotIndices m, k*(k+1)/2

theorem obstruction_totalDegree_parity (K : Type*) [Field K] (m : ℕ) :
    (obstruction K m).totalDegree ≤ degreeBudget m :=
  (totalDegree_finset_prod _ _).trans (sum_le_sum fun k _ => degree_minor_triangular K m k)

private theorem degreeBudget_step {m : ℕ} (hm : 2 ≤ m) :
    degreeBudget (m+2) = (m-1)*m/2 + degreeBudget m := by
  have split : pivotIndices (m+2) = insert (m-1) (pivotIndices m) := by
    ext k
    simp [pivotIndices]
    omega
  have fresh : m-1 ∉ pivotIndices m := by simp [pivotIndices]
  rw [degreeBudget,split,sum_insert fresh]
  simp only [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  rfl

/-- Closed parity formulas for the degree budget, with the equations cleared
of denominators and natural-number subtraction. -/
theorem degreeBudget_even (n : ℕ) :
    6*degreeBudget (2*n+2) + n*(n+1) = 4*n*n*(n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show 2*(n+1)+2 = (2*n+2)+2 by omega,degreeBudget_step (by omega)]
    have tri := Nat.mul_div_cancel' (Nat.even_mul_succ_self (2*n+1)).two_dvd
    rw [show 2*n+1+1 = 2*n+2 by omega] at tri
    simp only [show 2*n+2-1 = 2*n+1 by omega] at *
    nlinarith

theorem degreeBudget_odd (n : ℕ) :
    6*degreeBudget (2*n+3) = n*(n+1)*(4*n+5) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show 2*(n+1)+3 = (2*n+3)+2 by omega,degreeBudget_step (by omega)]
    have tri := Nat.mul_div_cancel' (Nat.even_mul_succ_self (2*n+2)).two_dvd
    rw [show 2*n+2+1 = 2*n+3 by omega] at tri
    simp only [show 2*n+3-1 = 2*n+2 by omega] at *
    nlinarith

/-- Uniform upper bound retaining the leading constant of the two parity formulas. -/
theorem degreeBudget_cubic (m : ℕ) : 12*degreeBudget m ≤ m^3 := by
  rcases m with _ | _ | m
  · decide
  · decide
  rcases Nat.mod_two_eq_zero_or_one m with even | odd
  · have rep : m+1+1 = 2*(m/2)+2 := by omega
    rw [rep]
    nlinarith [degreeBudget_even (m/2)]
  · have rep : m+1+1 = 2*(m/2)+3 := by omega
    rw [rep]
    nlinarith [degreeBudget_odd (m/2)]

private theorem same_sign {K : Type*} [Field K] {a b : ℕ} (h : a%2 = b%2) :
    (-1 : K)^a = (-1)^b := by
  rw [neg_one_pow_eq_pow_mod_two a,h,← neg_one_pow_eq_pow_mod_two b]

/-- Putting the alternating signs of ∏ (X − tᵢ) into the elementary
coefficients multiplies the determinant by a unit, row by row. -/
theorem signed_det {K : Type*} [Field K] {m : ℕ} (a : Fin m → K) (k : ℕ) :
    (block (fun v => (-1 : K)^(v.val+1)*a v) k).det =
      (∏ i : Fin k, (-1 : K)^(i.val+1)) * (block a k).det := by
  classical
  let signs : Fin k → K := fun i => (-1 : K)^(i.val+1)
  have mat : block (fun v => (-1 : K)^(v.val+1)*a v) k = Matrix.diagonal signs * block a k := by
    ext i j
    rw [Matrix.diagonal_mul]
    simp only [block,coefficient,signs]
    split_ifs with h h₀ hₘ
    · have e : (-1 : K)^(i.val+1) = (-1)^0 := same_sign (by omega)
      simp [e]
    · rw [same_sign (K:=K) (a:=2*(j.val+1)-(i.val+1)-1+1) (b:=i.val+1) (by omega)]
    · simp
    · simp
  rw [mat,Matrix.det_mul,Matrix.det_diagonal]

/-- Evaluation on the actual centered roots vanishes precisely on the union of
signed coefficient determinants. -/
theorem obstruction_eval_eq_zero_iff {K : Type*} [Field K] {m : ℕ} (t : Fin m → K) :
    eval t (obstruction K m) = 0 ↔ ∃ k ∈ pivotIndices m,
      (block (fun i : Fin m => (-1 : K)^(i.val+1) *
        eval t (esymm (Fin m) K (i.val+1))) k).det = 0 := by
  classical
  have nz (k : ℕ) : (∏ i : Fin k, (-1 : K)^(i.val+1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  simp only [obstruction,map_prod,Finset.prod_eq_zero_iff,minor,map_det,signed_det]
  simp [nz]

/-- The same zero criterion expressed directly in coefficients of the product
used by the Euclidean test. -/
theorem obstruction_eq_zero_iff_root_polynomial {K : Type*} [Field K] {m : ℕ} (t : Fin m → K) :
    eval t (obstruction K m) = 0 ↔ ∃ k ∈ pivotIndices m,
      (block (fun i : Fin m => (∏ j, (Polynomial.X - Polynomial.C (t j))).coeff
        (m-(i.val+1))) k).det = 0 := by
  have coeff (i : Fin m) :
      (∏ j, (Polynomial.X - Polynomial.C (t j))).coeff (m-(i.val+1)) =
        (-1 : K)^(i.val+1) * eval t (esymm (Fin m) K (i.val+1)) := by
    let s := (univ : Finset (Fin m)).val.map t
    have size : s.card = m := by simp [s]
    have h := Multiset.prod_X_sub_C_coeff s (k:=m-(i.val+1)) (by rw [size]; omega)
    rw [size,Nat.sub_sub_self (by omega : i.val+1≤m)] at h
    change ((univ.val.map (fun j => Polynomial.X - Polynomial.C (t j))).prod).coeff _ = _
    rw [show (univ.val.map (fun j => Polynomial.X - Polynomial.C (t j))) =
      s.map (fun x => Polynomial.X - Polynomial.C x) by simp [s, Function.comp_def],h]
    congr 1
    exact (aeval_esymm_eq_multiset_esymm (Fin m) K (i.val+1) t).symm
  simp only [coeff]
  exact obstruction_eval_eq_zero_iff t

set_option exponentiation.threshold 2050 in
/-- One trillion independent uniform raw draws. The counted event also includes
every setup mask exception in either coordinate. -/
theorem trillion {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (budget : m≤10^12) :
    LabelPolynomialBudget.chance cop (obstruction (ZMod p) m) (obstruction (ZMod q) m) <
      1/(2:ℚ≥0)^902 := by
  apply LabelPolynomialBudget.trillion_twelfth cop pl ql budget
    (obstruction_ne_zero _ _) (obstruction_ne_zero _ _)
  all_goals
    exact (Nat.mul_le_mul_left 12 (obstruction_totalDegree_parity _ m)).trans (degreeBudget_cubic m)

set_option exponentiation.threshold 2050 in
/-- The exact budget for the measured batch of 512 draws. -/
theorem at_512 {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) :
    LabelPolynomialBudget.chance cop (obstruction (ZMod p) 512) (obstruction (ZMod q) 512) <
      1/(2:ℚ≥0)^995 := by
  have b := degreeBudget_even 255
  norm_num at b
  have exactBudget : degreeBudget 512 = 11086720 := by omega
  apply (LabelPolynomialBudget.full_size (M:=512) (D:=11086720) cop pl ql le_rfl
    (obstruction_ne_zero _ _) (obstruction_ne_zero _ _)
    ((obstruction_totalDegree_parity _ _).trans exactBudget.le)
    ((obstruction_totalDegree_parity _ _).trans exactBudget.le)).trans_lt
  rw [←NNRat.coe_lt_coe]
  norm_num

end PrimeFactors.OppositePivotBudget
