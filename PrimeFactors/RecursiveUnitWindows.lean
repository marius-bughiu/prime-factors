import PrimeFactors.RecursiveUnitScale

/-! Rounding in the previously reduced integer-valued rows keeps all lower
errors on the same scale. The reduction theorem works with any eligible subset
of the nonnegative integers and any divisibility chain of fixed divisors. -/

namespace PrimeFactors.RecursiveUnitWindows

open Polynomial Finset

/-- A degree-ordered monic family supplies integral coordinates even for a
finite initial segment. A coefficient cutoff also covers the empty segment. -/
private theorem initial_expansion {i : ℕ} (B : Fin i → ℤ[X]) (deg : ∀ j, (B j).natDegree=j.val)
    (mon : ∀ j, (B j).Monic) (P : ℤ[X]) (cut : ∀ n, i≤n → P.coeff n=0) :
    ∃ a : Fin i → ℤ, P=∑ j, C (a j)*B j := by
  induction i generalizing P with
  | zero =>
    refine ⟨Fin.elim0,?_⟩
    simpa using (ext fun n => (cut n (Nat.zero_le _)).trans (coeff_zero ..).symm : P=0)
  | succ i ih =>
    let j := Fin.last i
    let Q := P-C (P.coeff i)*B j
    have top : (B j).coeff i=1 := by
      rw [show i=(B j).natDegree from (deg j).symm,(mon j).coeff_natDegree]
    have sub (n : ℕ) (h : i≤n) : Q.coeff n=0 := by
      rw [show Q=P-C (P.coeff i)*B j by rfl,coeff_sub,coeff_C_mul]
      rcases eq_or_lt_of_le h with rfl|lt
      · simp [top]
      · rw [cut n lt,coeff_eq_zero_of_natDegree_lt ((deg j).trans_lt lt)]; simp
    obtain ⟨a,eq⟩ := ih (fun h => B h.castSucc) (fun h => deg _) (fun h => mon _) Q sub
    refine ⟨Fin.lastCases (P.coeff i) a,?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc,Fin.lastCases_last,←eq]
    exact (sub_add_cancel ..).symm

/-- Normalization by a common fixed divisor at an eligible argument. -/
def Good (S : ℕ → Prop) (D W : ℕ → ℕ) (i : ℕ) (P : ℤ[X]) : Prop :=
  P.natDegree=i ∧ P.Monic ∧ ∀ x : ℕ, S x →
    ∃ y : ℤ, P.eval (x:ℤ)=(D i:ℤ)*y ∧ |y|≤(W i:ℤ)

/-- Round a monic target in previously bounded coordinates. The factor 2 in
the budget is the error bound for symmetric division, including ties. -/
theorem rounded_rows {k : ℕ} (S : ℕ → Prop) (D W Cb : ℕ → ℕ) (pos : ∀ i, 0<D i)
    (chain : ∀ {j i}, j ≤ i → D j∣D i)
    (start : ∀ i, ∃ P : ℤ[X], P.natDegree=i ∧ P.Monic ∧ ∀ x : ℕ, S x → (D i:ℤ)∣P.eval (x:ℤ))
    (target : ∀ i, ∃ P : ℤ[X], P.natDegree=i ∧ P.Monic ∧ ∀ x : ℕ, S x → |P.eval (x:ℤ)|≤(Cb i:ℤ))
    (budget : ∀ i ≤ k, 2*Cb i+D i*(∑ j ∈ range i, W j) ≤ 2*D i*W i) :
    ∀ i ≤ k, ∃ F : ℤ[X], Good S D W i F := by
  classical
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro le
    choose B good using fun j : Fin i => ih j.val j.isLt (j.isLt.le.trans le)
    obtain ⟨P,pd,pm,pval⟩ := start i
    obtain ⟨T,td,tm,tval⟩ := target i
    have cut (j : ℕ) (ij : i≤j) : (T-P).coeff j=0 := by
      rw [coeff_sub]
      rcases eq_or_lt_of_le ij with rfl|lt
      · rw [←td,tm.coeff_natDegree,td,←pd,pm.coeff_natDegree,sub_self]
      · rw [coeff_eq_zero_of_natDegree_lt (td.trans_lt lt),coeff_eq_zero_of_natDegree_lt (pd.trans_lt lt),sub_self]
    obtain ⟨a,exp⟩ := initial_expansion B (fun j => (good j).1) (fun j => (good j).2.1) (T-P) cut
    let num (j : Fin i) : ℤ := a j*(D j.val:ℤ)
    let q (j : Fin i) := (num j).bdiv (D i)
    let sc (j : Fin i) : ℤ := (D i / D j.val:ℕ)
    have scale (j : Fin i) : sc j*(D j.val:ℤ)=D i := by
      dsimp only [sc]; exact_mod_cast Nat.div_mul_cancel (chain j.isLt.le)
    let Cj (j : Fin i) := C (q j*sc j)*B j
    let F := P+∑ j, Cj j
    have low (j : Fin i) : (Cj j).natDegree < i :=
      (natDegree_C_mul_le ..).trans_lt ((good j).1.trans_lt j.isLt)
    have lead : F.coeff i=1 := by
      have h (j : Fin i) : (Cj j).coeff i=0 := coeff_eq_zero_of_natDegree_lt (low j)
      simp only [F,coeff_add,finset_sum_coeff,h,sum_const_zero,add_zero]
      rw [←pd,pm.coeff_natDegree]
    have lim : F.natDegree ≤ i := (natDegree_add_le ..).trans
      (max_le pd.le (natDegree_sum_le_of_forall_le _ _ (fun j _ => (low j).le)))
    have degree := natDegree_eq_of_le_of_coeff_ne_zero lim (lead ▸ one_ne_zero)
    refine ⟨F,degree,by simpa only [Monic,leadingCoeff,degree] using lead,?_⟩
    intro x hx
    obtain ⟨p,ep⟩ := pval x hx
    choose y ey small using fun j : Fin i => (good j).2.2 x hx
    let z := p+∑ j, q j*y j
    have rowEval : F.eval (x:ℤ)=(D i:ℤ)*z := by
      simp only [F,eval_add,ep,eval_finset_sum,Cj,eval_mul,eval_C,ey,z,mul_add,mul_sum]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      linear_combination q j*y j*scale j
    refine ⟨z,rowEval,?_⟩
    have ev : T.eval (x:ℤ)-(D i:ℤ)*p=∑ j, num j*y j := by
      rw [←ep,←eval_sub,exp,eval_finset_sum]
      simp only [eval_mul,eval_C,ey,num,mul_assoc]
    have diff : T.eval (x:ℤ)-(D i:ℤ)*z=∑ j, (num j).bmod (D i)*y j := by
      simp only [z,mul_add,mul_sum,sub_add_eq_sub_sub,ev,←sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      rw [Int.bmod_eq_self_sub_mul_bdiv]; dsimp only [q]; ring
    have err : 2*|T.eval (x:ℤ)-(D i:ℤ)*z|≤(D i:ℤ)*∑ j : Fin i, (W j.val:ℤ) := by
      rw [diff,mul_sum]
      apply (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs ..) (by decide : (0:ℤ)≤2)).trans
      rw [mul_sum]
      refine sum_le_sum fun j _ => ?_
      rw [abs_mul,←mul_assoc]
      have smallr := RoundedChebyshevWindows.half_error (num j) (pos i)
      rw [←Int.bmod_eq_self_sub_mul_bdiv] at smallr
      exact mul_le_mul smallr (small j) (abs_nonneg _) (Int.natCast_nonneg _)
    have tri := abs_sub_le ((D i:ℤ)*z) (T.eval (x:ℤ)) 0
    rw [abs_sub_comm ((D i:ℤ)*z) (T.eval (x:ℤ))] at tri
    simp only [sub_zero,abs_mul,abs_of_nonneg (Int.natCast_nonneg _)] at tri
    have hb : 2*(Cb i:ℤ)+(D i:ℤ)*(∑ j ∈ range i, (W j:ℤ))≤2*(D i:ℤ)*(W i:ℤ) := by
      exact_mod_cast budget i le
    rw [Fin.sum_univ_eq_sum_range (fun j => (W j:ℤ)) i] at err
    apply le_of_mul_le_mul_left (a:=(2:ℤ)*(D i:ℤ))
    · nlinarith only [hb,tri,err,tval x hx]
    · exact mul_pos (by decide) (by exact_mod_cast pos i)

/-- Explicit integral weights for the recursive reduction. -/
def weight (D : ℕ → ℕ) (U i : ℕ) := 4*U^i/D i

theorem recursive_budget {k U : ℕ} {D : ℕ → ℕ} (start : D 0=1) (pos : ∀ i, 0<D i)
    (step : ∀ i, D (i+1)≤3*(i+1)*D i) (wide : 6*k≤U) (i : ℕ) (le : i≤k) :
    2*ChebyshevDivisorWindow.weight U i+D i*(∑ j ∈ range i, weight D U j) ≤
      2*D i*weight D U i := by
  have double (j : ℕ) (jle : j<k) : 2*weight D U j ≤ weight D U (j+1) := by
    apply (Nat.le_div_iff_mul_le (pos _)).mpr
    have bound := Nat.div_mul_le_self (4*U^j) (D j)
    have size : 6*(j+1)≤U := by omega
    calc
      2*weight D U j*D (j+1) ≤ 2*weight D U j*(3*(j+1)*D j) :=
        Nat.mul_le_mul_left _ (step j)
      _ = 6*(j+1)*(weight D U j*D j) := by ring
      _ ≤ U*(4*U^j) := Nat.mul_le_mul size bound
      _ = 4*U^(j+1) := by ring
  have sum (j : ℕ) (lt : j≤k) : (∑ a ∈ range j, weight D U a)+1 ≤ weight D U j := by
    induction j with
    | zero => simp [weight,start]
    | succ j ih =>
      rw [sum_range_succ]
      have a := ih (by omega)
      have b := double j (by omega)
      omega
  have tar : 2*ChebyshevDivisorWindow.weight U i ≤ 4*U^i := by
    cases i with
    | zero => simp [ChebyshevDivisorWindow.weight,GapPolynomialScale.weight]
    | succ j => simp only [ChebyshevDivisorWindow.weight,GapPolynomialScale.weight]; omega
  have upper := Nat.lt_mul_div_succ (4*U^i) (pos i)
  change 4*U^i<D i*(weight D U i+1) at upper
  have ss := Nat.mul_le_mul_left (D i) (sum i le)
  nlinarith only [tar,upper,ss]

/-- The 3-unit rows from the quadratic construction meet the recursively
reduced bounds whenever U is at least six times the maximum degree. -/
theorem unit_rows {k U : ℕ} (s : ℤ)
    (step : ∀ i, ThreeUnitFactorialWindows.denominator (i+1)≤
      3*(i+1)*ThreeUnitFactorialWindows.denominator i) (wide : 6*k≤U) :
    ∀ i ≤ k, ∃ F : ℤ[X], Good (fun x : ℕ => (¬(3:ℤ)∣(x:ℤ)+s) ∧ x≤4*U)
      ThreeUnitFactorialWindows.denominator (weight ThreeUnitFactorialWindows.denominator U) i F := by
  apply rounded_rows _ _ _ (ChebyshevDivisorWindow.weight U) ThreeUnitFactorialWindows.denominator_pos
    ThreeUnitFactorialWindows.denominator_dvd
  · intro i
    obtain ⟨P,deg,mon,hit⟩ := ThreeUnitFactorialWindows.monic_row s i
    exact ⟨P,deg,mon,fun x h => hit x h.1⟩
  · intro i
    let P := (ChebyshevDivisorWindow.basis U i).comp (X-C (2*(U:ℤ)))
    have deg : P.natDegree=i := by
      dsimp only [P]
      rw [natDegree_comp,(ChebyshevDivisorWindow.degree_basis U i).1,natDegree_X_sub_C,mul_one]
    have mon : P.Monic := (ChebyshevDivisorWindow.degree_basis U i).2.comp (monic_X_sub_C _)
      (by rw [natDegree_X_sub_C]; decide)
    refine ⟨P,deg,mon,?_⟩
    intro x hx
    have near := hx.2
    simp only [P,eval_comp,eval_sub,eval_X,eval_C]
    exact ChebyshevDivisorWindow.eval_bound U i _ (abs_le.mpr (by omega))
  · exact recursive_budget (by decide) ThreeUnitFactorialWindows.denominator_pos step wide

/-- Use any bounded integer-valued row family in the finite Taylor-label argument. -/
theorem relation_of_rows {k m n L : ℕ} (S : ℕ→Prop) (D W : ℕ→ℕ)
    (pos : ∀ i, 0<D i) (chain : ∀ {j i}, j ≤ i → D j∣D i)
    (rows : ∀ i ≤ k, ∃ P : ℤ[X], Good S D W i P)
    (hn : 0<n) (hl : 0<L) (hw : ∀ i ≤ k, 0<W i)
    (room : n^(m+m.choose 2)*((k+1)^(k+1)*∏ i : Fin (k+1), W i.val)<(L^m)^(k+1))
    (t : ℤ) : ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤k ∧ ∀ (x : ℕ) (d : ℤ),
      d∣(n:ℤ) → d∣(x:ℤ)-t → (L:ℤ)≤d → IsCoprime d (D k:ℤ) → S x → F.eval (x:ℤ)=0 := by
  classical
  choose Q good using rows
  let P (i : ℕ) := if h : i≤k then Q i h else X^i
  have degree (i : ℕ) : (P i).natDegree=i := by
    dsimp only [P]; split
    · exact (good ..).1
    · exact natDegree_X_pow i
  have mon (i : ℕ) : (P i).Monic := by
    dsimp only [P]; split
    · exact (good ..).2.1
    · exact monic_X_pow _
  let seq : Polynomial.Sequence ℤ := ⟨P,fun i => by
    rw [Polynomial.degree_eq_natDegree (mon i).ne_zero,degree i]⟩
  have li : LinearIndependent ℤ (fun i : Fin (k+1) => P i.val) :=
    seq.linearIndependent.comp (fun i : Fin (k+1) => i.val) Fin.val_injective
  let scale (i : Fin (k+1)) : ℤ := (D k / D i.val:ℕ)
  have sc (i : Fin (k+1)) : scale i*(D i.val:ℤ)=D k := by
    dsimp only [scale]
    exact_mod_cast Nat.div_mul_cancel (chain (show i.val≤k by omega))
  have nzScale (i : Fin (k+1)) : scale i≠0 := by
    intro h; have e := sc i; rw [h,zero_mul] at e
    exact (pos k).ne' (by exact_mod_cast e.symm)
  let F (v : Fin (k+1) → ℤ) := ∑ i, C (v i*scale i)*P i.val
  letI (i : Fin m) : NeZero (n^(m-i.val)) := ⟨(pow_pos hn _).ne'⟩
  let T := (i : Fin m) → ZMod (n^(m-i.val))
  let tag (v : Fin (k+1) → ℤ) : T := fun i => ((taylor t (F v)).coeff i.val:ℤ)
  have size : Fintype.card T * ((k+1)^(k+1)*∏ i : Fin (k+1), W i.val)<(L^m)^(k+1) := by
    simpa only [T,Fintype.card_pi,ZMod.card,prod_pow_eq_pow_sum,HigherDivisorWindow.tag_sum] using room
  obtain ⟨u,v,ne,eq,short⟩ := HigherDivisorWindow.finite_collision (by omega : 0<k+1) (pow_pos hl m)
    (fun i : Fin (k+1) => W i.val) (fun i => hw _ (by omega)) size tag
  let w := u-v
  have nonzero : F w≠0 := by
    intro zero
    have z := (Fintype.linearIndependent_iff.mp li) (fun i => w i*scale i)
      (by simpa only [F,Polynomial.smul_eq_C_mul] using zero)
    exact (sub_ne_zero.mpr ne) (_root_.funext fun i => (mul_eq_zero.mp (z i)).resolve_right (nzScale i))
  refine ⟨F w,nonzero,?_,?_⟩
  · apply (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_C_mul_le _ _).trans ((degree i.val).trans_le (by omega))
  · have jets : HigherDivisorWindow.Jets m n t (F w) := by
      have sub : F w=F u-F v := by simp [w,F,sub_mul,sum_sub_distrib]
      intro i
      rw [sub,map_sub,coeff_sub,←Nat.cast_pow,←ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,sub_eq_zero]
      exact congrFun eq i
    intro x d factor offset floor coprime unit
    have eval (i : Fin (k+1)) : ∃ a : ℤ, (P i.val).eval (x:ℤ)=(D i.val:ℤ)*a ∧ |a|≤(W i.val:ℤ) := by
      have le : i.val≤k := by omega
      simpa only [P,dif_pos le] using (good i.val le).2.2 x unit
    choose val evVal bound using eval
    let y := ∑ i, w i*val i
    have ev : (F w).eval (x:ℤ) = (D k:ℤ)*y := by
      simp only [F,eval_finset_sum,eval_mul,eval_C,y,mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [evVal i]
      linear_combination w i*val i*sc i
    have div := HigherDivisorWindow.dvd_eval_of_jets jets factor offset
    rw [ev] at div ⊢
    have smallVal : |y|≤∑ i, |u i - v i| * (W i.val:ℤ) := by
      refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (bound i) (abs_nonneg _)
    have zero := Int.eq_zero_of_abs_lt_dvd (coprime.pow_left.dvd_of_dvd_mul_left div)
      ((smallVal.trans_lt (by simpa using short : _ < (L:ℤ)^m)).trans_le
        (pow_le_pow_left₀ (Int.natCast_nonneg _) floor m))
    rw [zero,mul_zero]

/-- Every eligible divisor across both ternary residue classes shares one
public relation under the recursive weights. -/
theorem unit_window {k m n U L : ℕ} (hk : 2≤k) (hn : 0<n) (hl : 0<L)
    (step : ∀ i, ThreeUnitFactorialWindows.denominator (i+1)≤3*(i+1)*ThreeUnitFactorialWindows.denominator i)
    (wide : 6*k≤U) (cop : n.Coprime (ThreeUnitFactorialWindows.denominator k))
    (room : n^(m+m.choose 2)*((k+1)^(k+1)*∏ i : Fin (k+1), weight ThreeUnitFactorialWindows.denominator U i.val)<
      (L^m)^(k+1))
    {c t : ℤ} (odd : IsCoprime (2:ℤ) (n:ℤ)) (anchor : (n:ℤ)∣c+2*t) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤k ∧ ∀ (x : ℕ) (d : ℤ),
      d∣(n:ℤ) → d=c+2*(x:ℤ) → (L:ℤ)≤d → x≤4*U → F.eval (x:ℤ)=0 := by
  have posU : 0<U := by omega
  have hw (i : ℕ) (le : i≤k) : 0<weight ThreeUnitFactorialWindows.denominator U i := by
    have h := recursive_budget (by decide : ThreeUnitFactorialWindows.denominator 0=1)
      ThreeUnitFactorialWindows.denominator_pos step wide i le
    have hc : 0<ChebyshevDivisorWindow.weight U i := by
      cases i <;> simp [ChebyshevDivisorWindow.weight,GapPolynomialScale.weight,pow_pos posU]
    by_contra! no
    rw [Nat.eq_zero_of_le_zero no,mul_zero] at h
    omega
  obtain ⟨F,nz,count,all⟩ := relation_of_rows _ ThreeUnitFactorialWindows.denominator
    (weight ThreeUnitFactorialWindows.denominator U) ThreeUnitFactorialWindows.denominator_pos
    ThreeUnitFactorialWindows.denominator_dvd (unit_rows (2*c) step wide) hn hl hw room t
  refine ⟨F,nz,count,?_⟩
  intro x d factor pos floor near
  have dc := cop.isCoprime.of_isCoprime_of_dvd_left factor
  have three : (3:ℕ)∣ThreeUnitFactorialWindows.denominator k :=
    (by decide : (3:ℕ)∣ThreeUnitFactorialWindows.denominator 2).trans (ThreeUnitFactorialWindows.denominator_dvd hk)
  have nonunit : ¬(3:ℤ)∣d := by
    intro h
    exact (by decide : ¬(3:ℤ)∣1) (dc.isUnit_of_dvd' h (by exact_mod_cast three)).dvd
  exact all x d factor (QuarticDivisorWindow.progression_offset odd anchor factor pos) floor dc ⟨by omega,near⟩

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

/-- A single equation covers a chosen 2^526-index span in the balanced
smaller-factor range. The center, anchor, and denominator gcd are public. -/
theorem uniform_window {n : ℕ} (large : 2^2047≤n)
    (cop : n.Coprime (ThreeUnitFactorialWindows.denominator 24575))
    {c t : ℤ} (odd : IsCoprime (2:ℤ) (n:ℤ)) (anchor : (n:ℤ)∣c+2*t) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤24575 ∧ ∀ (x : ℕ) (d : ℤ),
      d∣(n:ℤ) → d=c+2*(x:ℤ) → (CoupledDivisorWindow.lower n:ℤ)≤d →
      x≤2^526 → F.eval (x:ℤ)=0 := by
  have hn := (by positivity : 0<(2:ℕ)^2047).trans_le large
  have hd := (by positivity : 0<(2:ℕ)^1023).trans_le (CoupledDivisorWindow.lower_size large)
  let W := weight ThreeUnitFactorialWindows.denominator (2^524)
  have room := RecursiveUnitScale.finite_room (CoupledDivisorWindow.lower_size large)
    (CoupledDivisorWindow.product_le n) W (fun i _ => Nat.div_mul_le_self ..)
  dsimp only at room
  rw [← Fin.prod_univ_eq_prod_range] at room
  dsimp only [W, FeasibleDivisorCover.dimension, FeasibleDivisorCover.multiplicity] at room
  rw [show (24576:ℕ)=24575+1 by rfl] at room
  simpa only [show 4*(2:ℕ)^524=2^526 by decide +kernel] using
    unit_window (k:=24575) (m:=12287) (U:=2^524) (by decide) hn hd RecursiveUnitScale.denominator_step
      (by decide +kernel) cop room odd anchor

end PrimeFactors.RecursiveUnitWindows
