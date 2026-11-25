import PrimeFactors.HigherDivisorWindow
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.Index

/-! Integer-valued binomial coordinates on the finite one-sided window 0 ≤ x ≤ H.
The Taylor divisibilities concern a cleared integer polynomial. Coprimality with
the common factorial denominator lets the height test use the smaller integer value. -/

namespace PrimeFactors.BinomialDivisorWindow

open Polynomial Finset
open HigherDivisorWindow (Jets)

/-- The common denominator divided by the denominator of coefficient i. -/
def multiplier (k i : ℕ) := k.factorial/i.factorial

theorem multiplier_exact {i k : ℕ} (le : i≤k) : multiplier k i*i.factorial=k.factorial :=
  Nat.div_mul_cancel (Nat.factorial_dvd_factorial le)

/-- Integer polynomial obtained after multiplying the entire binomial expansion by k!. -/
noncomputable def cleared (k : ℕ) (v : Fin (k+1) → ℤ) : ℤ[X] :=
  ∑ i, C (v i * (multiplier k i:ℤ)) * descPochhammer ℤ i.val

noncomputable def value {k : ℕ} (v : Fin (k+1) → ℤ) (x : ℕ) : ℤ :=
  ∑ i, v i*(x.choose i.val:ℤ)

theorem eval_cleared (k : ℕ) (v : Fin (k+1) → ℤ) (x : ℕ) :
    (cleared k v).eval (x:ℤ) = (k.factorial:ℤ)*value v x := by
  simp only [cleared,value,eval_finset_sum,eval_mul,eval_C,descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul,mul_sum]
  apply sum_congr rfl
  intro i _
  have scale : (multiplier k i:ℤ) * (i.val.factorial:ℤ)=k.factorial := by
    exact_mod_cast multiplier_exact (by omega : i.val ≤ k)
  linear_combination v i*(x.choose i.val:ℤ)*scale

theorem value_bound {k H x : ℕ} (v : Fin (k+1) → ℤ) (inWindow : x≤H) :
    |value v x|≤∑ i, |v i| *(H.choose i.val:ℤ) := by
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro i _
  rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.choose_le_choose i.val inWindow) (abs_nonneg _)

theorem cleared_nonzero {k : ℕ} {v : Fin (k+1) → ℤ} (ne : v≠0) : cleared k v≠0 := by
  classical
  let s := univ.filter (fun i => v i≠0)
  have mem (i : Fin (k+1)) : i∈s ↔ v i≠0 := by simp [s]
  have nonempty : s.Nonempty := by
    by_contra! empty
    apply ne
    funext i
    by_contra h
    exact empty ⟨i,(mem i).mpr h⟩
  let j := s.min' nonempty
  have nz := (mem j).mp (min'_mem s nonempty)
  intro zero
  have hit := eval_cleared k v j.val
  rw [zero,eval_zero] at hit
  have vanish := (mul_eq_zero.mp hit.symm).resolve_left (by exact_mod_cast k.factorial_ne_zero)
  rw [value,sum_eq_single j] at vanish
  · exact nz (by simpa using vanish)
  · intro i _ diff
    by_cases nonzero : v i≠0
    · have lt : j < i := lt_of_le_of_ne (min'_le s i ((mem i).2 nonzero)) diff.symm
      simp [Nat.choose_eq_zero_of_lt (show j.val < i.val from lt)]
    · simp [not_ne_iff.mp nonzero]
  · simp

theorem degree_bound (k : ℕ) (v : Fin (k+1) → ℤ) : (cleared k v).natDegree≤k := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le _ _).trans (by rw [descPochhammer_natDegree]; omega)

private theorem cleared_sub (k : ℕ) (u v : Fin (k+1) → ℤ) :
    cleared k (u-v)=cleared k u-cleared k v := by
  simp only [cleared,Pi.sub_apply,sub_mul,map_sub,sum_sub_distrib]

/-- A chosen row applies to all divisor-compatible indices with a denominator
coprime to d. The argument cancels k! before applying the strict height bound. -/
theorem vanishes {k m n H D x : ℕ} {v : Fin (k+1) → ℤ} {d t : ℤ}
    (jets : Jets m n t (cleared k v)) (short : (∑ i, |v i| *(H.choose i.val:ℤ))<(D:ℤ)^m)
    (divides : d∣(n:ℤ)) (offset : d∣(x:ℤ)-t) (floor : (D:ℤ)≤d)
    (coprime : IsCoprime d (k.factorial:ℤ)) (near : x≤H) : (cleared k v).eval (x:ℤ)=0 := by
  have dvd := HigherDivisorWindow.dvd_eval_of_jets jets divides offset
  rw [eval_cleared] at dvd ⊢
  have dividesValue : d^m∣value v x := coprime.pow_left.dvd_of_dvd_mul_left dvd
  have bound := (value_bound v near).trans_lt (short.trans_le (pow_le_pow_left₀ (Int.natCast_nonneg _) floor _))
  rw [Int.eq_zero_of_abs_lt_dvd dividesValue bound,mul_zero]

/-- A nonzero short binomial-coordinate row satisfies the Taylor congruences. -/
theorem short_row {k m n H D : ℕ} (hn : 0<n) (hkH : k≤H) (hd : 0<D)
    (room : n^(m+m.choose 2)*((k+1)^(k+1)*∏ i : Fin (k+1), H.choose i.val) < (D^m)^(k+1))
    (t : ℤ) :
    ∃ v : Fin (k+1) → ℤ, v≠0 ∧ Jets m n t (cleared k v) ∧
      (∑ i, |v i| * (H.choose i.val:ℤ)) < (D:ℤ)^m := by
  classical
  letI (i : Fin m) : NeZero (n^(m-i.val)) := ⟨(pow_pos hn _).ne'⟩
  let L := (i : Fin m) → ZMod (n^(m-i.val))
  let tag (p : Fin (k+1) → ℤ) : L := fun i => ((taylor t (cleared k p)).coeff i.val : ℤ)
  have size : Fintype.card L * ((k+1)^(k+1)*∏ i : Fin (k+1), H.choose i.val) < (D^m)^(k+1) := by
    simpa only [L,Fintype.card_pi,ZMod.card,prod_pow_eq_pow_sum,HigherDivisorWindow.tag_sum] using room
  have pos (i : Fin (k+1)) : 0<H.choose i.val := Nat.choose_pos (by omega)
  obtain ⟨u,v,ne,eq,short⟩ := HigherDivisorWindow.finite_collision (by omega) (pow_pos hd m) _ pos size tag
  have jets : Jets m n t (cleared k (u-v)) := by
    intro j
    simp only [cleared_sub,map_sub,coeff_sub,← Nat.cast_pow,← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_sub,sub_eq_zero]
    exact congrFun eq j
  exact ⟨u-v,sub_ne_zero.mpr ne,jets,by simpa using short⟩

/-- One row for the entire integer window. The weights count the maximum values
of the individual binomial functions on the actual grid, including its endpoints. -/
theorem relation_exists {k m n H D : ℕ} (hn : 0<n) (hkH : k≤H) (hd : 0<D)
    (room : n^(m+m.choose 2)*((k+1)^(k+1)*∏ i : Fin (k+1), H.choose i.val) < (D^m)^(k+1))
    (t : ℤ) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤k ∧ ∀ (x : ℕ) (d : ℤ),
      d∣(n:ℤ) → d∣(x:ℤ)-t → (D:ℤ)≤d → IsCoprime d (k.factorial:ℤ) → x≤H → F.eval (x:ℤ)=0 := by
  obtain ⟨v,ne,jets,short⟩ := short_row hn hkH hd room t
  refine ⟨cleared k v,cleared_nonzero ne,
    (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (degree_bound _ _)),?_⟩
  intro x d divides offset floor coprime near
  exact vanishes jets short divides offset floor coprime near

theorem prime_denominator {p k : ℕ} (hp : p.Prime) (bigger : k<p) :
    IsCoprime (p:ℤ) (k.factorial:ℤ) :=
  (hp.coprime_iff_not_dvd.mpr (fun h => (not_le_of_gt bigger) (hp.dvd_factorial.mp h))).isCoprime

open scoped Matrix

/-- Rows of the cleared basis in ordinary Taylor coordinates at a public integer anchor. -/
noncomputable def taylorRows (k : ℕ) (t : ℤ) : PowerJetContent.Rows k :=
  fun i j => (multiplier k i:ℤ)*(taylor t (descPochhammer ℤ i.val)).coeff j.val

theorem det_taylorRows (k : ℕ) (t : ℤ) :
    (taylorRows k t).det=∏ i : Fin (k+1), (multiplier k i:ℤ) := by
  rw [Matrix.det_of_lowerTriangular]
  · apply prod_congr rfl
    intro i _
    have monic := (monic_descPochhammer ℤ i.val).comp (monic_X_add_C t) (by rw [natDegree_X_add_C]; decide)
    change (taylor t (descPochhammer ℤ i.val)).Monic at monic
    rw [Monic,leadingCoeff,natDegree_taylor,descPochhammer_natDegree] at monic
    simp [taylorRows,monic]
  · intro i j lt
    rw [taylorRows,coeff_eq_zero_of_natDegree_lt (by simpa only [natDegree_taylor,
      descPochhammer_natDegree] using lt),mul_zero]

private theorem coeff_vecMul (k : ℕ) (t : ℤ) (v : Fin (k+1) → ℤ) (j : Fin (k+1)) :
    (taylor t (cleared k v)).coeff j.val=(v ᵥ* taylorRows k t) j := by
  simp only [cleared,map_sum,finset_sum_coeff,taylor_mul,taylor_C,coeff_C_mul,
    Matrix.vecMul,dotProduct,taylorRows,mul_assoc]

/-- The coefficient homomorphism records the distinct Taylor conditions charged in the size bound. -/
noncomputable def labels (k m n : ℕ) (t : ℤ) :
    (Fin (k+1) → ℤ) →+ ((j : Fin m) → ZMod (n^(m-j.val))) where
  toFun v j := ((taylor t (cleared k v)).coeff j.val : ℤ)
  map_zero' := by ext; simp [cleared]
  map_add' v w := by
    ext j
    simp only [cleared,Pi.add_apply,add_mul,map_add,sum_add_distrib,map_sum,
      finset_sum_coeff,coeff_add,Int.cast_add]

/-- If n is coprime to k!, every admissible jet label can be prescribed. Bézout and the
adjugate give an integer preimage of an arbitrary target modulo n^m. -/
theorem labels_surjective {k m n : ℕ} (coprime : n.Coprime k.factorial) (depth : m≤k+1)
    (t : ℤ) : Function.Surjective (labels k m n t) := by
  let M := taylorRows k t
  have detUnit : IsCoprime M.det (n:ℤ) := by
    rw [det_taylorRows]
    apply IsCoprime.prod_left
    intro i _
    apply coprime.symm.isCoprime.of_isCoprime_of_dvd_left
    exact_mod_cast (show multiplier k i∣k.factorial from ⟨i.val.factorial,
      (multiplier_exact (by omega : i.val ≤ k)).symm⟩)
  obtain ⟨g,b,bez⟩ := detUnit.pow_right (n:=m)
  intro target
  choose lift hit using fun i : Fin m => ZMod.intCast_surjective (target i)
  let z (j : Fin (k+1)) : ℤ := if h : j.val<m then lift ⟨j.val,h⟩ else 0
  let v := g • (z ᵥ* M.adjugate)
  refine ⟨v,?_⟩
  funext i
  let j : Fin (k+1) := ⟨i.val,i.isLt.trans_le depth⟩
  have slot : z j=lift i := by simp [z,j,i.isLt]
  have coord : (v ᵥ* M) j=g*(z j*M.det) := by
    simp only [v,Matrix.vecMul_smul,Matrix.vecMul_vecMul,Matrix.adjugate_mul,Pi.smul_apply,
      smul_eq_mul]
    congr 1
    simp [Matrix.vecMul,dotProduct,Matrix.one_apply,smul_eq_mul,mul_ite]
  change (((taylor t (cleared k v)).coeff j.val : ℤ) : ZMod (n^(m-i.val)))=target i
  rw [coeff_vecMul,show taylorRows k t=M from rfl,coord,slot,← hit i,
    ZMod.intCast_eq_intCast_iff_dvd_sub,Nat.cast_pow]
  apply (pow_dvd_pow (n:ℤ) (Nat.sub_le m i.val)).trans
  use b*lift i
  linear_combination -(lift i)*bez

/-- The subgroup of binomial-coordinate rows satisfying all jets has precisely
n^(m(m+1)/2) cosets. In particular the determinant price from clearing the
basis denominators does not enter the number of congruence classes. -/
theorem kernel_index {k m n : ℕ} (hn : 0<n) (coprime : n.Coprime k.factorial) (depth : m≤k+1)
    (t : ℤ) : (labels k m n t).ker.index=n^(m+m.choose 2) := by
  letI (i : Fin m) : NeZero (n^(m-i.val)) := ⟨(pow_pos hn _).ne'⟩
  rw [AddSubgroup.index_ker,AddMonoidHom.range_eq_top.mpr (labels_surjective coprime depth t)]
  rw [Nat.card_congr (AddSubgroup.topEquiv.toEquiv),Nat.card_eq_fintype_card]
  simp only [Fintype.card_pi,ZMod.card,prod_pow_eq_pow_sum,HigherDivisorWindow.tag_sum]

/-- Embedding the coefficients in scaled integer coordinates charges their window maxima. -/
noncomputable def scale (k H : ℕ) : (Fin (k+1) → ℤ) →+ (Fin (k+1) → ℤ) where
  toFun v i := (H.choose i.val:ℤ)*v i
  map_zero' := by ext; simp
  map_add' v w := by ext; simp [mul_add]

/-- Exact index of the scaled lattice where one would apply integer lattice reduction. -/
theorem scaled_index {k m n H : ℕ} (hn : 0<n) (coprime : n.Coprime k.factorial)
    (depth : m≤k+1) (wide : k≤H) (t : ℤ) :
    ((labels k m n t).ker.map (scale k H)).index = n^(m+m.choose 2)*∏ i : Fin (k+1), H.choose i.val := by
  have injective : Function.Injective (scale k H) := by
    intro v w eq
    funext i
    exact mul_left_cancel₀ (by exact_mod_cast (Nat.choose_pos (show i.val≤H by omega)).ne') (congrFun eq i)
  have image : (scale k H).range=AddSubgroup.pi Set.univ
      (fun i : Fin (k+1) => AddSubgroup.zmultiples (H.choose i.val:ℤ)) := by
    ext v
    simp only [AddMonoidHom.mem_range,AddSubgroup.mem_pi,Set.mem_univ,true_implies,Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨w,rfl⟩ i
      exact ⟨w i,rfl⟩
    · intro dvd
      choose w hw using dvd
      exact ⟨w,funext fun i => (hw i).symm⟩
  rw [AddSubgroup.index_map_of_injective _ injective,kernel_index hn coprime depth,image,AddSubgroup.index_pi]
  simp

end PrimeFactors.BinomialDivisorWindow
