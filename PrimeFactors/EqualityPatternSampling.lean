import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Independent uniform samples observed only through the equality of their labels.
A new label receives its index in first-occurrence order, starting at zero. -/
namespace PrimeFactors.EqualityPatternSampling

open Finset

/-- Expected payoff of a test on a future equality transcript, starting with k
known distinct labels among m. Used only on attainable states. -/
noncomputable def expect (m : ℕ) : ℕ → ℕ → (List ℕ → ℝ) → ℝ
  | 0, _, f => f []
  | t+1, k, f =>
    ((∑ i ∈ range k, expect m t k (fun h => f (i::h))) +
      ((m:ℝ)-k)*expect m t (k+1) (fun h => f (k::h))) / m

theorem expect_bounds {m t k : ℕ} (positive : 0<m) (room : k+t≤m) (f : List ℕ→ℝ)
    (bounded : ∀ h, 0≤f h ∧ f h≤1) : 0≤expect m t k f ∧ expect m t k f≤1 := by
  induction t generalizing k f with
  | zero => exact bounded []
  | succ t ih =>
    have old (i : ℕ) := ih (k:=k) (by omega) (fun h => f (i::h)) (fun _ => bounded _)
    have fresh := ih (k:=k+1) (by omega) (fun h => f (k::h)) (fun _ => bounded _)
    have mass : 0≤(m:ℝ)-k := by
      apply sub_nonneg.mpr
      exact_mod_cast (show k≤m by omega)
    have pos : 0<(m:ℝ) := by exact_mod_cast positive
    rw [expect]
    constructor
    · exact div_nonneg (add_nonneg (sum_nonneg fun i _ => (old i).1) (mul_nonneg mass fresh.1)) pos.le
    · apply (div_le_iff₀ pos).mpr
      have hsum := sum_le_card_nsmul (range k) _ (1:ℝ) (fun i _ => (old i).2)
      simp only [card_range,nsmul_eq_mul,mul_one] at hsum
      linarith only [hsum,mul_le_mul_of_nonneg_left fresh.2 mass]

/-- Equality pattern of chronological draws, independent of label names. -/
def Same {t k m : ℕ} (code : Fin t→Fin k) (x : Fin t→Fin m) : Prop :=
  ∀ i j, code i=code j ↔ x i=x j

/-- Each labeling of k occupied classes is an injection into the sample universe. -/
noncomputable def labeling {t k m : ℕ} (code : Fin t→Fin k) (sur : Function.Surjective code) :
    (Fin k ↪ Fin m) ≃ {x : Fin t→Fin m // Same code x} where
  toFun e := ⟨fun j => e (code j),fun _ _ => e.injective.eq_iff.symm⟩
  invFun x := ⟨fun i => x.val (Function.surjInv sur i),by
    intro i j h
    simpa only [Function.surjInv_eq] using (x.property _ _).mpr h⟩
  left_inv e := by
    apply Function.Embedding.ext
    intro i
    change e (code (Function.surjInv sur i))=e i
    exact congrArg e (Function.surjInv_eq sur i)
  right_inv x := by
    apply Subtype.ext
    funext i
    exact (x.property _ _).mp (Function.surjInv_eq sur (code i))

/-- The count for one specified partition into k nonempty classes is (m)_k,
also when k>m. Independent uniform samples divide this count by m^t. -/
theorem count {t k m : ℕ} (code : Fin t→Fin k) (sur : Function.Surjective code) :
    Nat.card {x : Fin t→Fin m // Same code x} = m.descFactorial k := by
  classical
  rw [←Nat.card_congr (labeling code sur),Nat.card_eq_fintype_card,Fintype.card_embedding_eq]
  simp

private def append {m k : ℕ} (e : Fin k ↪ Fin m) (a : Fin m)
    (fresh : ¬∃ i,e i=a) : Fin (k+1) ↪ Fin m where
  toFun := Fin.snoc (α:=fun _ => Fin m) e a
  inj' := by
    intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases
    · exact fun _ => rfl
    · intro eq
      exact (fresh ⟨_,(by simpa using eq.symm)⟩).elim
    · intro eq
      exact (fresh ⟨_,(by simpa using eq)⟩).elim
    · intro eq
      exact congrArg Fin.castSucc (e.injective (by simpa using eq))

/-- Indices of actual draws relative to the previously seen distinct labels e.
A first occurrence appends its label to the end of that list. -/
noncomputable def read {m : ℕ} : (t k : ℕ) → (Fin k ↪ Fin m) → (Fin t → Fin m) → List ℕ
  | 0, _, _, _ => []
  | t+1, k, e, x =>
    if seen : ∃ i, e i=x 0 then seen.choose.val::read t k e (Fin.tail x)
    else k::read t (k+1) (append e (x 0) seen) (Fin.tail x)

/-- Starting with no known labels gives the observed equality transcript. -/
noncomputable def transcript {m t : ℕ} (x : Fin t→Fin m) : List ℕ :=
  read t 0 ⟨Fin.elim0,fun i => Fin.elim0 i⟩ x

/-- Existing names match where they reappear, and every pair of future draws has
the same equality outcome. The two underlying universes may have different sizes. -/
private def Consistent {m n k t : ℕ} (e : Fin k ↪ Fin m) (g : Fin k ↪ Fin n)
    (x : Fin t→Fin m) (y : Fin t→Fin n) : Prop :=
  (∀ i j, x i=x j ↔ y i=y j) ∧ (∀ a i,e a=x i ↔ g a=y i)

private theorem old_tail {m n k t : ℕ} {e : Fin k ↪ Fin m} {g : Fin k ↪ Fin n}
    {x : Fin (t+1)→Fin m} {y : Fin (t+1)→Fin n} {a : Fin k}
    (ex : e a=x 0) (gy : g a=y 0) :
    Consistent e g x y ↔ Consistent e g (Fin.tail x) (Fin.tail y) := by
  constructor
  · rintro ⟨h,q⟩
    exact ⟨fun i j => h i.succ j.succ, fun v i => q v i.succ⟩
  · rintro ⟨h,q⟩
    constructor
    · intro i j
      induction i using Fin.cases <;> induction j using Fin.cases
      · simp
      · rename_i j
        exact ex ▸ gy ▸ q a j
      · rename_i i
        exact Iff.trans eq_comm ((ex ▸ gy ▸ q a i).trans eq_comm)
      · exact h _ _
    · intro v i
      induction i using Fin.cases
      · rw [←ex,←gy,e.injective.eq_iff,g.injective.eq_iff]
      · exact q v _

private theorem fresh_tail {m n k t : ℕ} {e : Fin k ↪ Fin m} {g : Fin k ↪ Fin n}
    {x : Fin (t+1)→Fin m} {y : Fin (t+1)→Fin n}
    (ex : ¬∃ i,e i=x 0) (gy : ¬∃ i,g i=y 0) :
    Consistent e g x y ↔ Consistent (append e (x 0) ex) (append g (y 0) gy)
      (Fin.tail x) (Fin.tail y) := by
  constructor
  · rintro ⟨h,q⟩
    refine ⟨fun i j => h i.succ j.succ,?_⟩
    intro a i
    induction a using Fin.lastCases
    · simpa [append,Fin.tail] using h 0 i.succ
    · rename_i a
      simpa [append,Fin.tail] using q a i.succ
  · rintro ⟨h,q⟩
    have first (i : Fin t) : x 0=x i.succ ↔ y 0=y i.succ := by
      simpa [append,Fin.tail] using q (Fin.last k) i
    constructor
    · intro i j
      induction i using Fin.cases <;> induction j using Fin.cases
      · simp
      · exact first _
      · exact eq_comm.trans ((first _).trans eq_comm)
      · exact h _ _
    · intro a i
      induction i using Fin.cases
      · exact iff_of_false (fun bad => ex ⟨a,bad⟩) (fun bad => gy ⟨a,bad⟩)
      · rename_i i
        simpa [append,Fin.tail] using q a.castSucc i

private theorem read_iff {m n : ℕ} (t k : ℕ) (e : Fin k ↪ Fin m) (g : Fin k ↪ Fin n)
    (x : Fin t→Fin m) (y : Fin t→Fin n) : read t k e x=read t k g y ↔ Consistent e g x y := by
  classical
  induction t generalizing k with
  | zero =>
    simp only [read,true_iff]
    exact ⟨fun i => i.elim0,fun _ i => i.elim0⟩
  | succ t ih =>
    by_cases ex : ∃ i,e i=x 0 <;> by_cases gy : ∃ i,g i=y 0
    · simp only [read,dif_pos ex,dif_pos gy,List.cons.injEq]
      by_cases same : ex.choose=gy.choose
      · rw [old_tail (g:=g) (y:=y) ex.choose_spec (same ▸ gy.choose_spec),ih]
        simp [same]
      · apply iff_of_false
        · exact fun h => same (Fin.ext h.1)
        · intro con
          exact same (g.injective (((con.2 _ _).mp ex.choose_spec).trans gy.choose_spec.symm))
    · simp only [read,dif_pos ex,dif_neg gy,List.cons.injEq]
      exact iff_of_false (fun h => (Nat.ne_of_lt ex.choose.isLt) h.1)
        (fun c => gy ⟨_,(c.2 _ _).mp ex.choose_spec⟩)
    · simp only [read,dif_neg ex,dif_pos gy,List.cons.injEq]
      exact iff_of_false (fun h => (Nat.ne_of_lt gy.choose.isLt) h.1.symm)
        (fun c => ex ⟨_,(c.2 _ _).mpr gy.choose_spec⟩)
    · simp only [read,dif_neg ex,dif_neg gy,List.cons.injEq,true_and]
      exact (ih _ _ _ _ _).trans (fresh_tail ex gy).symm

/-- Two actual observations have the same transcript precisely when every
pairwise equality agrees, even for words drawn from different universes. -/
theorem transcript_eq_iff {t m n : ℕ} (x : Fin t→Fin m) (y : Fin t→Fin n) :
    transcript x=transcript y ↔ Same x y := by
  rw [transcript,transcript,read_iff]
  exact ⟨And.left,fun h => ⟨h,fun a => a.elim0⟩⟩

private theorem sum_labels {m k : ℕ} (e : Fin k ↪ Fin m) (old : Fin k→ℝ) (fresh : ℝ) :
    (∑ a : Fin m, if h : ∃ i,e i=a then old h.choose else fresh) =
    (∑ i,old i)+((m:ℝ)-k)*fresh := by
  classical
  let A := (univ : Finset (Fin k)).image e
  let g (a : Fin m) := if h : ∃ i,e i=a then old h.choose else fresh
  change ∑ a,g a=_
  have previous (i : Fin k) : g (e i)=old i := by
    dsimp [g]
    rw [dif_pos (show ∃ j,e j=e i from ⟨i,rfl⟩)]
    congr 1
    exact e.injective (Exists.choose_spec (show ∃ j,e j=e i from ⟨i,rfl⟩))
  have repeat_sum : ∑ a∈A,g a=∑ i,old i := by
    dsimp [A]
    rw [sum_image e.injective.injOn]
    exact sum_congr rfl fun i _ => previous i
  have cardA : A.card=k := by simp [A,card_image_of_injective _ e.injective]
  have km : k≤m := by simpa using Fintype.card_le_of_injective e e.injective
  have new_sum : ∑ a∈Aᶜ,g a=((m:ℝ)-k)*fresh := by
    calc
      _ = ∑ _a∈Aᶜ,fresh := sum_congr rfl (fun a ha => by
        have h : ¬∃ i,e i=a := by simpa [A] using ha
        simp [g,h])
      _ = _ := by simp [card_compl,cardA,Nat.cast_sub km]
  rw [←sum_add_sum_compl A g,repeat_sum,new_sum]

/-- The recursive experiment is the exact finite sum over the m^t equally likely
draw sequences. No independence assumption on abstract transcript labels occurs. -/
theorem read_total {m : ℕ} (pos : 0<m) (t k : ℕ) (e : Fin k ↪ Fin m) (f : List ℕ→ℝ) :
    ∑ x : Fin t→Fin m, f (read t k e x) = (m:ℝ)^t*expect m t k f := by
  classical
  induction t generalizing k f with
  | zero => simp [read,expect]
  | succ t ih =>
    let g (x : Fin (t+1)→Fin m) := f (read (t+1) k e x)
    change ∑ x,g x=_
    rw [←(Fin.consEquiv (fun _ : Fin (t+1) => Fin m)).sum_comp g,Fintype.sum_prod_type]
    have one (a : Fin m) :
        ∑ x : Fin t→Fin m, g ((Fin.consEquiv (fun _ : Fin (t+1) => Fin m)) (a,x)) =
          (m:ℝ)^t*(if h : ∃ i,e i=a then expect m t k (fun l => f (h.choose.val::l))
            else expect m t (k+1) (fun l => f (k::l))) := by
      change (∑ x : Fin t→Fin m, f (read (t+1) k e (Fin.cons a x)))=_
      by_cases h : ∃ i,e i=a
      · simp only [read,Fin.cons_zero,Fin.tail_cons,dif_pos h]
        exact ih k e (fun l => f (h.choose.val::l))
      · simp only [read,Fin.cons_zero,Fin.tail_cons,dif_neg h]
        exact ih (k+1) (append e a h) (fun l => f (k::l))
    rw [sum_congr rfl (fun a _ => one a),←mul_sum,sum_labels e (fun i => expect m t k (fun l => f (i.val::l)))
      (expect m t (k+1) (fun l => f (k::l))),expect,sum_range,pow_succ]
    field_simp [show (m:ℝ)≠0 by exact_mod_cast pos.ne']
    ring

/-- Direct mean over independent uniform draws for an arbitrary test on the full
first-occurrence transcript. -/
theorem uniform {m t : ℕ} (pos : 0<m) (f : List ℕ→ℝ) :
    (∑ x : Fin t→Fin m, f (transcript x))/(m:ℝ)^t=expect m t 0 f := by
  rw [show (∑ x : Fin t→Fin m, f (transcript x))=(m:ℝ)^t*expect m t 0 f from read_total pos t 0 _ f]
  field_simp [show (m:ℝ)≠0 by exact_mod_cast pos.ne']

private theorem bounded_state {m t k : ℕ} (pos : 0<m) (km : k≤m) (f : List ℕ→ℝ)
    (bounded : ∀ h, 0≤f h ∧ f h≤1) : 0≤expect m t k f ∧ expect m t k f≤1 := by
  let e : Fin k ↪ Fin m := ⟨(fun i => ⟨i.val,i.isLt.trans_le km⟩),fun _ _ eq =>
    Fin.ext (congrArg (fun a : Fin m => a.val) eq)⟩
  have total := read_total pos t k e f
  have nn : 0≤∑ x : Fin t→Fin m,f (read t k e x) := sum_nonneg (fun _ _ => (bounded _).1)
  have upper := sum_le_card_nsmul (univ : Finset (Fin t→Fin m)) (fun x => f (read t k e x))
    (1:ℝ) (fun _ _ => (bounded _).2)
  simp only [card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,nsmul_eq_mul,mul_one] at upper
  rw [total] at nn upper
  have p : 0<(m:ℝ)^t := pow_pos (by exact_mod_cast pos) _
  exact ⟨nonneg_of_mul_nonneg_right nn p,by nlinarith only [upper,p]⟩

private noncomputable def mix (m k : ℕ) (f : ℕ→ℝ) (z : ℝ) : ℝ :=
  ((∑ i∈range k,f i)+((m:ℝ)-k)*z)/m

private theorem mix_eq (m k : ℕ) (f : ℕ→ℝ) (z : ℝ) :
    mix m k f z=((∑ i∈range k,f i)+((m:ℝ)-k)*z)/m := rfl

private theorem stable {m k : ℕ} (pos : 0<m) (km : k≤m) (f g : ℕ→ℝ) (y z E : ℝ)
    (repeats : ∀ i∈range k, |f i-g i|≤E)
    (next : k=m ∨ |y-z|≤E) : |mix m k f y-mix m k g z|≤E := by
  have p : 0<(m:ℝ) := by exact_mod_cast pos
  have w : 0≤(m:ℝ)-k := by
    apply sub_nonneg.mpr
    exact_mod_cast km
  rw [mix_eq,mix_eq,←sub_div,abs_div,abs_of_pos p,div_le_iff₀ p]
  rw [show (∑ i∈range k,f i)+((m:ℝ)-k)*y-((∑ i∈range k,g i)+((m:ℝ)-k)*z)=
    (∑ i∈range k,(f i-g i))+((m:ℝ)-k)*(y-z) by rw [sum_sub_distrib];ring]
  have sum_bound := (abs_sum_le_sum_abs _ _).trans (sum_le_sum repeats)
  simp only [sum_const,card_range,nsmul_eq_mul] at sum_bound
  have fresh_bound : |((m:ℝ)-k)*(y-z)|≤((m:ℝ)-k)*E := by
    rcases next with rfl|h
    · simp
    · simpa only [abs_mul,abs_of_nonneg w] using
        (show |(m:ℝ)-k| * |y-z|≤((m:ℝ)-k)*E by rw [abs_of_nonneg w];gcongr)
  exact (abs_add_le ..).trans ((add_le_add sum_bound fresh_bound).trans_eq (by ring))

private theorem change_size {m d k : ℕ} (pos : 0<m) (f : ℕ→ℝ) (z : ℝ)
    (old : ∀ i,0≤f i ∧ f i≤1) (fresh : 0≤z ∧ z≤1) :
    |mix m k f z-mix (m+d) k f z|≤(k:ℝ)*(d/((m:ℝ)*(m+d))) := by
  have mp : 0<(m:ℝ) := by exact_mod_cast pos
  have addp : 0<(m:ℝ)+d := by positivity
  let c := (d:ℝ)/((m:ℝ)*(m+d))
  have id : mix m k f z-mix (m+d) k f z=((∑ i∈range k,f i)-k*z)*c := by
    rw [mix_eq,mix_eq,Nat.cast_add]
    dsimp [c]
    field_simp [mp.ne',addp.ne']
    ring
  have nn : 0≤∑ i∈range k,f i := sum_nonneg (fun i _ => (old i).1)
  have ub := sum_le_card_nsmul (range k) f (1:ℝ) (fun i _ => (old i).2)
  simp only [card_range,nsmul_eq_mul,mul_one] at ub
  have kpos : 0≤(k:ℝ) := by positivity
  have inside : |(∑ i∈range k,f i)-k*z|≤(k:ℝ) := abs_le.mpr ⟨by
    nlinarith only [nn,mul_le_mul_of_nonneg_left fresh.2 kpos],by
    linarith only [ub,mul_nonneg kpos fresh.1]⟩
  have cpos : 0≤c := by dsimp [c]; positivity
  rw [id,abs_mul,abs_of_nonneg cpos]
  exact mul_le_mul_of_nonneg_right inside cpos

private noncomputable def steps (k t : ℕ) : ℝ := (t:ℝ)*(2*k+t-1)/2

private theorem coupling_from {m d t k : ℕ} (pos : 0<m) (km : k≤m) (f : List ℕ→ℝ)
    (bounded : ∀ h,0≤f h ∧ f h≤1) :
    |expect m t k f-expect (m+d) t k f|≤steps k t*(d/((m:ℝ)*(m+d))) := by
  by_cases zero : d=0
  · subst d; simp
  let c := (d:ℝ)/((m:ℝ)*(m+d))
  have cp : 0≤c := by dsimp [c];positivity
  change _≤steps k t*c
  induction t generalizing k f with
  | zero => simp [expect,steps]
  | succ t ih =>
    let o (n i : ℕ) := expect n t k (fun l => f (i::l))
    let a (n : ℕ) := expect n t (k+1) (fun l => f (k::l))
    have left : expect m (t+1) k f=mix m k (o m) (a m) := (mix_eq ..).symm
    have right : expect (m+d) (t+1) k f=mix (m+d) k (o (m+d)) (a (m+d)) := (mix_eq ..).symm
    have inc : steps k t≤steps (k+1) t := by
      simp only [steps,Nat.cast_add,Nat.cast_one]
      nlinarith only [Nat.cast_nonneg (α:=ℝ) t]
    have past (i : ℕ) (_ : i∈range k) : |o m i-o (m+d) i| ≤ steps (k+1) t*c :=
      (ih km (fun l => f (i::l)) (fun _ => bounded _)).trans (mul_le_mul_of_nonneg_right inc cp)
    have fresh : k=m ∨ |a m-a (m+d)|≤steps (k+1) t*c := by
      by_cases full : k=m
      · exact Or.inl full
      · exact Or.inr (ih (by omega : k+1≤m) (fun l => f (k::l)) (fun _ => bounded _))
    have first := stable pos km (o m) (o (m+d)) (a m) (a (m+d)) _ past fresh
    have second := change_size (d:=d) (k:=k) pos (o (m+d)) (a (m+d))
      (fun i => bounded_state (by omega) (by omega) _ (fun _ => bounded _))
      (bounded_state (by omega) (by omega) _ (fun _ => bounded _))
    rw [left,right]
    refine (abs_sub_le _ (mix m k (o (m+d)) (a (m+d))) _).trans ((add_le_add first second).trans_eq ?_)
    change steps (k+1) t*c+k*c=steps k (t+1)*c
    simp only [steps,Nat.cast_add,Nat.cast_one]
    ring

/-- Upper bound on the change in acceptance probability of any randomized
equality-transcript test. The payoff may be any real number between zero and
one, and the draw count is unrestricted. -/
theorem coupling {m d t : ℕ} (pos : 0<m) (f : List ℕ→ℝ)
    (bounded : ∀ h,0≤f h ∧ f h≤1) :
    |expect m t 0 f-expect (m+d) t 0 f|≤(t:ℝ)*(t-1)*d/(2*m*(m+d)) := by
  refine (coupling_from (d:=d) (t:=t) pos (Nat.zero_le _) f bounded).trans_eq ?_
  simp only [steps,Nat.cast_zero,mul_zero,zero_add]
  have mp : (m:ℝ)≠0 := by exact_mod_cast pos.ne'
  have addp : 0<(m:ℝ)+d := by positivity
  field_simp [mp,addp.ne']
  ring_nf
  simp


/-- The two-draw event distinguishes the labels being identical with chance 1/m. -/
noncomputable def repeatPair : List ℕ→ℝ
  | [a,b] => if a=b then 1 else 0
  | _ => 0

theorem pair_equal {m : ℕ} (positive : 0<m) : expect m 2 0 repeatPair=1/(m:ℝ) := by
  simp [expect,repeatPair,sum_range_succ,show (m:ℝ)≠0 by exact_mod_cast positive.ne']

theorem numerical : |expect 640 2 0 repeatPair-expect 672 2 0 repeatPair|=1/13440 := by
  rw [pair_equal (by decide),pair_equal (by decide)]
  norm_num

end PrimeFactors.EqualityPatternSampling
