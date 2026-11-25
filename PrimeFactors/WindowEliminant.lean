import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Roots
import PrimeFactors.HigherDivisorWindow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-! Elimination in the public window label. A family specified by polynomial
coefficients can be tested jointly, provided its determinant is nonzero.
A translation of fixed offset equations preserves that determinant. -/

namespace PrimeFactors.WindowEliminant

open Polynomial Matrix Finset

/-- A joint solution in the integer label and offset forces a zero of the
determinant in the label alone. The offset vector starts with 1. -/
theorem eval_det_zero {r : ℕ} (M : Matrix (Fin (r+1)) (Fin (r+1)) ℤ[X]) {t x : ℤ}
    (vanish : ∀ i, ∑ j, (M i j).eval t*x^j.val=0) : M.det.eval t=0 := by
  let h := Polynomial.evalRingHom t
  change h M.det=0
  rw [h.map_det]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨fun j => x^j.val,?_,?_⟩
  · intro zero
    have eq := congrFun zero (0 : Fin (r+1))
    simp at eq
  · funext i
    simpa only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply,
      h, Polynomial.coe_evalRingHom, Pi.zero_apply] using vanish i

/-- The eliminant pays once for each input row's degree in the label. -/
theorem degree_det_le {ι R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R[X])
    (b : ι → ℕ) (cap : ∀ i j, (M i j).natDegree≤b i) : M.det.natDegree≤∑ i, b i := by
  classical
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  have s : (Equiv.Perm.sign σ • ∏ i, M (σ i) i).natDegree=(∏ i, M (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e|e
    · rw [e,one_smul]
    · rw [e,Units.neg_smul,one_smul,natDegree_neg]
  rw [s]
  calc
    _ ≤ ∑ i, (M (σ i) i).natDegree := natDegree_prod_le ..
    _ ≤ ∑ i, b (σ i) := sum_le_sum fun i _ => cap _ _
    _ = ∑ i, b i := Equiv.sum_comp σ b

/-- E+1 snapshots at distinct labels determine the eliminant if the global
degree bound has already been established. -/
theorem det_from_samples {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K[X]) {b : ι→ℕ} (cap : ∀ i j, (M i j).natDegree≤b i)
    {E : ℕ} (small : ∑ i, b i ≤ E) (node : Fin (E+1)→K) (inj : Function.Injective node) :
    M.det = Lagrange.interpolate univ node (fun i => ((evalRingHom (node i)).mapMatrix M).det) := by
  classical
  apply Lagrange.eq_interpolate_of_eval_eq _ inj.injOn
  · rw [card_univ,Fintype.card_fin]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le ((degree_det_le M b cap).trans small))
  · intro i _
    exact (evalRingHom (node i)).map_det M

/-- The same public finite set serves every possible offset. -/
theorem candidate_labels {r : ℕ} (M : Matrix (Fin (r+1)) (Fin (r+1)) ℤ[X])
    (nz : M.det≠0) (b : Fin (r+1) → ℕ) (cap : ∀ i j, (M i j).natDegree≤b i) :
    M.det.roots.toFinset.card ≤ ∑ i, b i ∧
    ∀ t x : ℤ, (∀ i, ∑ j, (M i j).eval t*x^j.val=0) → t∈M.det.roots.toFinset := by
  refine ⟨(Multiset.toFinset_card_le _).trans ((card_roots' _).trans (degree_det_le M b cap)),?_⟩
  intro t x hit
  exact Multiset.mem_toFinset.mpr ((mem_roots nz).mpr (eval_det_zero M hit))

/-- Substituting X+H(T) in the offset variable multiplies coefficient rows
by this lower-triangular Pascal matrix. -/
def shift {R : Type*} [CommRing R] (r : ℕ) (h : R) : Matrix (Fin r) (Fin r) R :=
  fun i j => (i.val.choose j.val:R)*h^(i.val-j.val)

theorem shift_coeff {R : Type*} [CommRing R] {r : ℕ} (a : Fin r → R) (h : R) (j : Fin r) :
    (∑ i, C (a i)*(X+C h)^i.val).coeff j.val = ∑ i, a i*shift r h i j := by
  simp only [finset_sum_coeff,coeff_C_mul,coeff_X_add_C_pow,shift]
  apply sum_congr rfl; intro i _; ring

theorem det_shift {R : Type*} [CommRing R] (r : ℕ) (h : R) : (shift r h).det=1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [shift]
  · intro i j lt
    change i<j at lt
    simp [shift,Nat.choose_eq_zero_of_lt (show i.val<j.val from lt)]

/-- Translation and determinant-one row operations leave the eliminant fixed,
even when the substitution and row operations depend on the label. -/
theorem equivalent_det {R : Type*} [CommRing R] {r : ℕ} (M A : Matrix (Fin r) (Fin r) R)
    (h : R) (unimodular : A.det=1) : (A*M*shift r h).det=M.det := by
  rw [Matrix.det_mul,Matrix.det_mul,unimodular,det_shift,one_mul,mul_one]

/-- A separate exact summary of arbitrary linear root labels distinguishes
every word, even if the second family tests a single block and field value. -/
theorem summary_injective {ι K M : Type*} (pack : (ι→K)→M) (accept : M→ι→K→Prop)
    (correct : ∀ a i x, accept (pack a) i x ↔ a i=x) : Function.Injective pack := by
  intro a b same
  funext i
  have hit := (correct a i (a i)).mpr rfl
  rw [same] at hit
  exact ((correct b i (a i)).mp hit).symm

theorem summary_states {ι K M : Type*} [Fintype ι] [Fintype K] [Fintype M]
    (pack : (ι→K)→M) (accept : M→ι→K→Prop) (correct : ∀ a i x, accept (pack a) i x ↔ a i=x) :
    Fintype.card K ^ Fintype.card ι ≤ Fintype.card M := by
  classical
  simpa using Fintype.card_le_of_injective pack (summary_injective pack accept correct)

/-- A residue modulo a monic degree-s polynomial has s scalar coordinates. -/
theorem summary_words {K : Type*} [Fintype K] {n s : ℕ} (size : 1<Fintype.card K)
    (pack : (Fin n→K)→(Fin s→K)) (accept : (Fin s→K)→Fin n→K→Prop)
    (correct : ∀ a i x, accept (pack a) i x ↔ a i=x) : n≤s := by
  have h := summary_states pack accept correct
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.pow_le_pow_iff_right size] using h

/-- Even two fully linear families, with at most one matching label promised,
force injectivity as soon as the alphabet supplies a third value. -/
theorem same_label_injective {ι K M : Type*} (avoid : ∀ u v : K, ∃ c, c≠u ∧ c≠v)
    (pack : (ι→K)→M) (accept : M→(ι→K)→Prop)
    (correct : ∀ a b : ι→K, (∀ i j, a i=b i → a j=b j → i=j) →
      (accept (pack a) b ↔ ∃ i, a i=b i)) : Function.Injective pack := by
  classical
  intro a a' eq
  funext i
  by_contra diff
  choose c ha hb using fun j => avoid (a j) (a' j)
  let b (j : ι) := if j=i then a i else c j
  have aa (j : ι) (h : a j=b j) : j=i := by
    by_contra ne
    exact ha j (by simpa only [b,if_neg ne] using h.symm)
  have same : a i=b i := by simp [b]
  have none (j : ι) : a' j≠b j := by
    by_cases e : j=i
    · subst j; simpa only [b,if_pos rfl] using Ne.symm diff
    · simpa only [b,if_neg e] using Ne.symm (hb j)
  have hit := (correct a b (fun j k hj hk => (aa j hj).trans (aa k hk).symm)).mpr ⟨i,same⟩
  rw [eq] at hit
  obtain ⟨j,hj⟩ := (correct a' b (fun j _ hj _ => (none j hj).elim)).mp hit
  exact none j hj

/-- Powers of the offset absorb every required Taylor constraint at zero.
After removing this common factor the residual is unrestricted by those
divisibilities alone. -/
theorem residual_free (m n : ℕ) (P : ℤ[X]) : HigherDivisorWindow.Jets m n 0 (X^m*P) := by
  intro i
  rw [taylor_zero,coeff_X_pow_mul',if_neg (Nat.not_le_of_gt i.isLt)]
  exact dvd_zero _

/-- For distinct label nodes, ordinary interpolation attains the n-coordinate
bound and preserves every single-block query. -/
theorem interpolate_labels {K : Type*} [Field K] {n : ℕ} (node : Fin n→K)
    (inj : Function.Injective node) (a : Fin n→K) :
    ∃ P : K[X], P.natDegree≤n-1 ∧ ∀ i, P.eval (node i)=a i := by
  classical
  refine ⟨Lagrange.interpolate univ node a,?_,fun i => Lagrange.eval_interpolate_at_node a inj.injOn (mem_univ i)⟩
  have h := natDegree_le_of_degree_le (Lagrange.degree_interpolate_le a (s:=univ) inj.injOn)
  change (Lagrange.interpolate univ node a).natDegree ≤ univ.card-1 at h
  simpa using h

/-- The second list has the same product after its labels are interchanged.
A product common root can therefore belong to different labels. -/
theorem crossed_linear_rows :
    ((X-C 1)*(X-C 3) : ℤ[X])=(X-C 3)*(X-C 1) ∧
    (∃ i : Fin 2, (![1,2] : Fin 2→ℤ) i=(![1,3] : Fin 2→ℤ) i) ∧
    ¬∃ i : Fin 2, (![1,2] : Fin 2→ℤ) i=(![3,1] : Fin 2→ℤ) i := by
  exact ⟨mul_comm ..,by decide,by decide⟩

/-- The public candidate at offset x in block t. -/
private noncomputable def trial (x : ℤ) : ℤ[X] := C (9903+2*x)+C 4*X

private noncomputable def test (x : ℤ) : ℤ[X] := trial x*(C 20100-trial x)-C 101000651

/-- Coefficients of f(x) and x f(x) after reducing modulo x(x−1). -/
noncomputable def exampleMatrix : Matrix (Fin 2) (Fin 2) ℤ[X] :=
  !![test 0, test 1-test 0; 0, test 1]

/-- The quartic label polynomial has two integral roots on the entire integer
line. Its other two rational roots lie halfway between consecutive labels. -/
theorem example_roots (t : ℤ) : exampleMatrix.det.eval t=0 ↔ t=26 ∨ t=47 := by
  have formula : exampleMatrix.det.eval t =
      (4*t-104)*(190-4*t)*(4*t-102)*(188-4*t) := by
    simp [exampleMatrix,Matrix.det_fin_two,test,trial]
    ring
  rw [formula]
  simp only [mul_eq_zero]
  omega

/-- A sum bound proved from the public interval, before identifying any divisor. -/
theorem example_sum {d q : ℤ} (prod : d*q=101000651) (lo : 9903≤d) (hi : d≤10049) :
    d+q=20100 := by
  have qp : 0<q := by
    by_contra! non
    have v := mul_nonpos_of_nonneg_of_nonpos (show 0≤d by omega) non
    omega
  have lower : 20099 < d+q := by
    by_contra! h
    have v := mul_nonneg (by omega : 0≤20099-d-q) (by omega : 0≤20099+d+q)
    nlinarith only [v,sq_nonneg (d-q),prod]
  have upper : d+q < 20102 := by
    by_contra! h
    have a := mul_nonneg (by omega : 0≤d-9903) (by omega : 0≤10199-d)
    have b := mul_nonneg (by omega : 0≤d) (by omega : 0≤q+d-20102)
    nlinarith only [a,b,prod]
  have o : Odd d ∧ Odd q := Int.odd_mul.mp (prod ▸ (by decide : Odd (101000651:ℤ)))
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := o
  omega

/-- Publicly 37 two-position blocks cover the 74 odd possibilities. Every
factor in that range is in block 26, where its exact value is 10007. -/
theorem example_block {d q t x : ℤ} (prod : d*q=101000651) (lo : 9903≤d) (hi : d≤10049)
    (lab : d=9903+4*t+2*x) (ox : x=0 ∨ x=1) : t=26 ∧ d=10007 := by
  have sum := example_sum prod lo hi
  have f : (test x).eval t=0 := by
    simp only [test,trial,eval_sub,eval_mul,eval_C,eval_add,eval_X]
    have v : 9903+2*x+4*t=d := by omega
    rw [v,show 20100-d=q by omega,prod,sub_self]
  have root : exampleMatrix.det.eval t=0 := by
    simp [exampleMatrix,Matrix.det_fin_two]
    rcases ox with rfl|rfl
    · exact Or.inl f
    · exact Or.inr f
  rcases (example_roots t).mp root with rfl|rfl
  · constructor
    · rfl
    · rcases ox with rfl|rfl
      · omega
      · nlinarith only [lab,prod,sum]
  · omega

theorem example_cover {d q : ℤ} (prod : d*q=101000651) (lo : 9903≤d) (hi : d≤10049) :
    let t := (d-9903)/4
    0≤t ∧ t<37 ∧ t=26 ∧ d=10007 := by
  let t := (d-9903)/4
  let x := ((d-9903)%4)/2
  obtain ⟨a,da⟩ := (Int.odd_mul.mp (prod ▸ (by decide : Odd (101000651:ℤ)))).1
  have lab : d=9903+4*t+2*x := by dsimp [t,x]; omega
  have ox : x=0 ∨ x=1 := by dsimp [x]; omega
  have found := example_block prod lo hi lab ox
  dsimp only
  exact ⟨by omega,by omega,found⟩

theorem public_endpoints :
    Nat.sqrt 101000651=10049 ∧ 10051-Nat.sqrt (10051^2-101000651)=9903 ∧
    (10049-9903)/2+1=74 := by
  have first : Nat.sqrt 101000651=10049 := (Nat.eq_sqrt.mpr (by decide +kernel)).symm
  have second : Nat.sqrt (10051^2-101000651)=148 := (Nat.eq_sqrt.mpr (by decide +kernel)).symm
  rw [first,second]
  decide

theorem example_primes : Nat.Prime 10007 ∧ Nat.Prime 10093 ∧
    101000651=10007*10093 := by norm_num

end PrimeFactors.WindowEliminant
