import PrimeFactors.HigherDivisorWindow
import PrimeFactors.GapPolynomialScale

/-! Integer Chebyshev coordinates for a divisor window of radius 2U.
The first-kind Dickson polynomial is the monic scaling of the classical Chebyshev
polynomial. The existing Dickson identity bounds it on the closed interval. -/

namespace PrimeFactors.ChebyshevDivisorWindow

open Polynomial Finset
open HigherDivisorWindow (Jets)

/-- Degree zero uses 1 so that every basis polynomial is monic. -/
noncomputable def basis (U : ℕ) : ℕ → ℤ[X]
  | 0 => 1
  | i+1 => dickson 1 ((U:ℤ)^2) (i+1)

abbrev weight := GapPolynomialScale.weight

theorem degree_basis (U i : ℕ) : (basis U i).natDegree = i ∧ (basis U i).Monic := by
  cases i with
  | zero => simp [basis]
  | succ i =>
    exact ((GapPolynomialScale.dickson_monic_degree ((U:ℤ)^2) (i+1)).2 (by omega)).symm

theorem eval_bound (U i : ℕ) (x : ℤ) (near : |x|≤2*(U:ℤ)) :
    |(basis U i).eval x| ≤ (weight U i:ℤ) := by
  cases i with
  | zero => simp [basis,weight,GapPolynomialScale.weight]
  | succ i =>
    have square := mul_self_le_mul_self (abs_nonneg x) near
    have sq : x^2 ≤ 4*(U:ℤ)^2 := by nlinarith only [sq_abs x,square]
    simpa only [basis,weight,GapPolynomialScale.weight,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
      using GapPolynomialScale.dickson_abs_bound (Int.natCast_nonneg U) sq (i+1)

/-- Expand an integer row in the degree-ordered monic basis. -/
noncomputable def expand {r : ℕ} (U : ℕ) (v : Fin r → ℤ) : ℤ[X] :=
  ∑ i, C (v i) * basis U i.val

theorem expand_nonzero {r U : ℕ} {v : Fin r → ℤ} (ne : v ≠ 0) : expand U v ≠ 0 := by
  classical
  let s := univ.filter (fun i => v i ≠ 0)
  have mem (i : Fin r) : i ∈ s ↔ v i ≠ 0 := by simp [s]
  have nonempty : s.Nonempty := by
    by_contra! empty
    apply ne
    funext i
    by_contra h
    exact empty ⟨i,(mem i).mpr h⟩
  let j := s.max' nonempty
  have nz := (mem j).mp (max'_mem s nonempty)
  intro zero
  have coeff := congrArg (fun F : ℤ[X] => F.coeff j.val) zero
  simp only [expand,finset_sum_coeff,coeff_C_mul,coeff_zero] at coeff
  rw [sum_eq_single j] at coeff
  · have lead := (degree_basis U j).2
    rw [Monic,leadingCoeff,(degree_basis U j).1] at lead
    exact nz (by simpa only [lead,mul_one] using coeff)
  · intro i _ diff
    by_cases hi : v i=0
    · simp [hi]
    have le : i≤j := le_max' s i ((mem i).mpr hi)
    rw [coeff_eq_zero_of_natDegree_lt (by simpa only [(degree_basis U i).1] using
      (show i.val<j.val from (lt_of_le_of_ne le diff : i<j))),mul_zero]
  · simp

private theorem expand_sub {r : ℕ} (U : ℕ) (u v : Fin r → ℤ) :
    expand U (u-v) = expand U u - expand U v := by
  simp only [expand,Pi.sub_apply,map_sub,sub_mul,sum_sub_distrib]

theorem expand_bound {r : ℕ} (U : ℕ) (v : Fin r → ℤ) (x : ℤ) (near : |x| ≤ 2*(U:ℤ)) :
    |(expand U v).eval x| ≤ ∑ i, |v i| *(weight U i.val:ℤ) := by
  rw [expand,eval_finset_sum]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro i _
  simp only [eval_mul,eval_C,abs_mul]
  exact mul_le_mul_of_nonneg_left (eval_bound U i x near) (abs_nonneg _)

theorem weight_product (U k : ℕ) :
    (∏ i : Fin (k+1), weight U i.val) = 2^k*U^((k+1).choose 2) := by
  induction k with
  | zero => simp [weight,GapPolynomialScale.weight]
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    change (∏ i : Fin (k+1), weight U i.val) * (2*U^(k+1)) = _
    rw [ih,Nat.choose_succ_succ (k+1) 1,Nat.choose_one_right,pow_add U,pow_succ 2]
    ring

/-- Rows of the integer change of basis, columns in ascending ordinary degree. -/
noncomputable def ordinaryCoefficients (k U : ℕ) : PowerJetContent.Rows k :=
  fun i j => (basis U i.val).coeff j.val

theorem det_ordinaryCoefficients (k U : ℕ) : (ordinaryCoefficients k U).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · have diag (i : Fin (k+1)) : ordinaryCoefficients k U i i = 1 := by
      have lead := (degree_basis U i.val).2
      simpa only [ordinaryCoefficients,Monic,leadingCoeff,(degree_basis U i.val).1] using lead
    simp only [diag,prod_const_one]
  · intro i j lt
    exact coeff_eq_zero_of_natDegree_lt ((degree_basis U i.val).1.trans_lt lt)

/-- Determinant in the scaled Chebyshev coordinates actually used by reduction. -/
theorem scaled_det (k m U : ℕ) (mk : m≤k) (n t : ℤ) :
    ((HigherDivisorWindow.scaledBasis k m n 1 t * (ordinaryCoefficients k U)⁻¹) *
      Matrix.diagonal (fun i : Fin (k+1) => (weight U i.val : ℤ))).det =
      n^(m+m.choose 2)*(2^k*(U:ℤ)^((k+1).choose 2)) := by
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_nonsing_inv,det_ordinaryCoefficients,
    HigherDivisorWindow.scaled_det _ _ mk,Matrix.det_diagonal]
  have weights := weight_product U k
  have cast : (∏ i : Fin (k+1), (weight U i.val : ℤ)) = (2:ℤ)^k*(U:ℤ)^((k+1).choose 2) := by
    exact_mod_cast weights
  simp [cast]

/-- A nonzero polynomial with at most k roots covers every divisor-compatible
offset in the prescribed window as soon as the finite volume comparison holds. -/
theorem relation_exists {k m n U D : ℕ} (hn : 0<n) (hu : 0<U) (hd : 0<D)
    (room : n^(m+m.choose 2)*((k+1)^(k+1)*(2^k*U^((k+1).choose 2))) < (D^m)^(k+1))
    (t : ℤ) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤k ∧ ∀ x d : ℤ, d∣(n:ℤ) → d∣x-t →
      (D:ℤ)≤d → |x|≤2*(U:ℤ) → F.eval x=0 := by
  classical
  letI (i : Fin m) : NeZero (n^(m-i.val)) := ⟨(pow_pos hn _).ne'⟩
  let L := (i : Fin m) → ZMod (n^(m-i.val))
  let tag (p : Fin (k+1) → ℤ) : L := fun i => ((taylor t (expand U p)).coeff i.val : ℤ)
  have size : Fintype.card L * ((k+1)^(k+1) * ∏ i : Fin (k+1), weight U i.val) < (D^m)^(k+1) := by
    simpa only [L,Fintype.card_pi,ZMod.card,prod_pow_eq_pow_sum,HigherDivisorWindow.tag_sum,
      weight_product] using room
  have pos (i : Fin (k+1)) : 0 < weight U i.val := by cases i.val <;> simp [weight,GapPolynomialScale.weight,hu]
  obtain ⟨u,v,ne,eq,short⟩ := HigherDivisorWindow.finite_collision (by omega) (pow_pos hd m) _ pos size tag
  let F := expand U (u-v)
  refine ⟨F,expand_nonzero (sub_ne_zero.mpr ne),?_,?_⟩
  · apply (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_C_mul_le _ _).trans ((degree_basis U i.val).1.le.trans (by omega))
  · have jets : Jets m n t F := by
      intro j
      simp only [F,expand_sub,map_sub,coeff_sub,← Nat.cast_pow,← ZMod.intCast_zmod_eq_zero_iff_dvd,
        Int.cast_sub,sub_eq_zero]
      exact congrFun eq j
    intro x d divides offset floor near
    apply Int.eq_zero_of_abs_lt_dvd (HigherDivisorWindow.dvd_eval_of_jets jets divides offset)
    exact ((expand_bound U (u-v) x near).trans_lt (by simpa using short)).trans_le
      (pow_le_pow_left₀ (Int.natCast_nonneg _) floor _)

/-- Dimension-indexed form for schedules whose public budget specifies a row count. -/
theorem relation_at_dimension {r m n U D : ℕ} (hr : 0<r) (hn : 0<n) (hu : 0<U) (hd : 0<D)
    (room : n^(m+m.choose 2)*(r^r*(2^(r-1)*U^(r.choose 2))) < (D^m)^r) (t : ℤ) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤r-1 ∧ ∀ x d : ℤ, d∣(n:ℤ) → d∣x-t →
      (D:ℤ)≤d → |x|≤2*(U:ℤ) → F.eval x=0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  exact relation_exists hn hu hd room t

end PrimeFactors.ChebyshevDivisorWindow
