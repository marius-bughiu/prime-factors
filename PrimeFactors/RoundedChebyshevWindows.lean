import PrimeFactors.BinomialDivisorWindow
import PrimeFactors.ChebyshevDivisorWindow
import PrimeFactors.CoupledDivisorWindow
import PrimeFactors.ChebyshevQuarticScale
import Mathlib.Algebra.Polynomial.Sequence

/-! Round a centered Chebyshev polynomial divided by its leading factorial in the
integer-valued binomial basis. The common denominator is canceled only for
eligible divisors coprime to it. -/

namespace PrimeFactors.RoundedChebyshevWindows

open Polynomial Finset
open BinomialDivisorWindow (cleared value)

private theorem falling_expansion (i : ℕ) (P : ℤ[X]) (h : P.natDegree≤ i) :
    ∃ b : Fin (i+1) → ℤ, P=∑ j, C (b j)*descPochhammer ℤ j.val ∧ b (Fin.last i)=P.coeff i := by
  induction i generalizing P with
  | zero =>
    exact ⟨fun _ => P.coeff 0,by simpa using eq_C_of_natDegree_le_zero h,rfl⟩
  | succ i ih =>
    let j := i+1
    let a := P.coeff j
    let Q := P-C a*descPochhammer ℤ j
    have top : (descPochhammer ℤ j).coeff j=1 := by
      simpa only [descPochhammer_natDegree] using (monic_descPochhammer ℤ j).coeff_natDegree
    have low : Q.natDegree≤ i := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro u hu
      simp only [Q,coeff_sub,coeff_C_mul]
      rcases eq_or_lt_of_le (by omega : j≤u) with e|lt
      · subst u; simp [a,top]
      · rw [coeff_eq_zero_of_natDegree_lt (h.trans_lt lt),
          coeff_eq_zero_of_natDegree_lt ((descPochhammer_natDegree ℤ j).trans_lt lt)]
        simp
    obtain ⟨b,eq,_⟩ := ih Q low
    refine ⟨Fin.lastCases a b,?_,Fin.lastCases_last⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc,Fin.coe_castSucc,Fin.lastCases_last,Fin.val_last]
    rw [←eq]; exact (sub_add_cancel ..).symm

/-- Weights use floor divisions. The final 1 ensures a positive scale at every
radius and degree. -/
noncomputable def weight (U i : ℕ) := ChebyshevDivisorWindow.weight U i / i.factorial +
  (∑ j ∈ range i, (4*U)^j/j.factorial)+1

private theorem choose_upper (H j : ℕ) : H.choose j≤H^j/j.factorial := by
  apply (Nat.le_div_iff_mul_le j.factorial_pos).mpr
  simpa only [Nat.descFactorial_eq_factorial_mul_choose,mul_comm] using Nat.descFactorial_le_pow H j

/-- Symmetric division rounds a Newton coefficient to within one half, including ties. -/
theorem half_error (b : ℤ) {m : ℕ} (hm : 0<m) : 2*|b-(m:ℤ)*b.bdiv m|≤(m:ℤ) := by
  rw [←Int.bmod_eq_self_sub_mul_bdiv]
  have l := Int.le_bmod (x:=b) hm
  have r := Int.bmod_lt (x:=b) hm
  rcases le_or_gt 0 (b.bmod m) with h|h
  · rw [abs_of_nonneg h]; omega
  · rw [abs_of_neg h]; omega

/-- A unitriangular integer row approximates the monic degree-i Chebyshev divided
by i!. Only the earlier binomial coordinates acquire rounding errors. -/
theorem rounded_row (U i : ℕ) : ∃ v : Fin (i+1) → ℤ, v (Fin.last i)=1 ∧
    ∀ x : ℕ, x≤4*U → |value v x|≤(weight U i:ℤ) := by
  let P := (ChebyshevDivisorWindow.basis U i).comp (X-C (2*(U:ℤ)))
  have deg : P.natDegree=i := by
    dsimp only [P]
    rw [natDegree_comp,(ChebyshevDivisorWindow.degree_basis U i).1,natDegree_X_sub_C,mul_one]
  have mon : P.Monic := (ChebyshevDivisorWindow.degree_basis U i).2.comp (monic_X_sub_C _)
    (by rw [natDegree_X_sub_C]; decide)
  obtain ⟨b,eq,top⟩ := falling_expansion i P deg.le
  have last : b (Fin.last i)=1 := top.trans (deg ▸ mon.coeff_natDegree)
  let a := i.factorial
  let num (j : Fin (i+1)) : ℤ := b j*(j.val.factorial:ℤ)
  let v (j : Fin (i+1)) : ℤ := if j=Fin.last i then 1 else (num j).bdiv a
  refine ⟨v,by simp [v],?_⟩
  intro x hx
  have target : |P.eval (x:ℤ)|≤(ChebyshevDivisorWindow.weight U i:ℤ) := by
    simp only [P,eval_comp,eval_sub,eval_X,eval_C]
    exact ChebyshevDivisorWindow.eval_bound U i _ (abs_le.mpr (by omega))
  have ev : P.eval (x:ℤ)=∑ j, num j*(x.choose j.val:ℤ) := by
    rw [eq,eval_finset_sum]
    simp only [eval_mul,eval_C,descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul,num,mul_assoc]
  have diff : P.eval (x:ℤ)-(a:ℤ)*value v x =
      ∑ j : Fin i, (num j.castSucc).bmod a * (x.choose j.val:ℤ) := by
    rw [ev,value,mul_sum,←sum_sub_distrib,Fin.sum_univ_castSucc]
    have term (j : Fin i) :
        num j.castSucc*(x.choose j.val:ℤ)-(a:ℤ)*(v j.castSucc*(x.choose j.val:ℤ)) =
        (num j.castSucc).bmod a*(x.choose j.val:ℤ) := by
      rw [Int.bmod_eq_self_sub_mul_bdiv]
      simp [v,Fin.castSucc_ne_last]; ring
    simp only [Fin.coe_castSucc,term,Fin.val_last]
    have endterm : num (Fin.last i) = a := by simp [num,last,a]
    rw [endterm,show v (Fin.last i)=1 by simp [v],one_mul,sub_self,add_zero]
  have small (j : Fin i) : |(num j.castSucc).bmod a|≤(a:ℤ) := by
    have h := half_error (num j.castSucc) i.factorial_pos
    rw [←Int.bmod_eq_self_sub_mul_bdiv] at h
    change |(num j.castSucc).bmod i.factorial|≤(i.factorial:ℤ)
    omega
  have err : |P.eval (x:ℤ)-(a:ℤ)*value v x|≤(a:ℤ)*∑ j : Fin i, (((4*U)^j.val/j.val.factorial:ℕ):ℤ) := by
    rw [diff,mul_sum]
    refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun j _ => ?_)
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
    exact mul_le_mul (small j) (by exact_mod_cast (Nat.choose_le_choose j.val hx).trans (choose_upper _ _))
      (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have triangle := abs_sub_le ((a:ℤ)*value v x) (P.eval (x:ℤ)) 0
  rw [abs_sub_comm ((a:ℤ)*value v x) (P.eval (x:ℤ))] at triangle
  simp only [sub_zero,abs_mul,abs_of_nonneg (Int.natCast_nonneg a)] at triangle
  have hp : 0<(a:ℤ) := by exact_mod_cast i.factorial_pos
  have bound : |value v x|-(∑ j : Fin i, (((4*U)^j.val/j.val.factorial:ℕ):ℤ))≤
      (ChebyshevDivisorWindow.weight U i:ℤ)/(a:ℤ) := by
    apply (Int.le_ediv_iff_mul_le hp).mpr
    nlinarith only [triangle,target,err]
  rw [Fin.sum_univ_eq_sum_range (fun j => (((4*U)^j/j.factorial:ℕ):ℤ)) i] at bound
  simp only [weight,Nat.cast_add,Nat.cast_one,Nat.cast_sum,Int.natCast_ediv]
  dsimp [a] at bound
  omega

private theorem cleared_top (i : ℕ) (v : Fin (i+1) → ℤ) (last : v (Fin.last i)=1) :
    (cleared i v).natDegree=i ∧ (cleared i v).Monic := by
  have eq : (cleared i v).coeff i=1 := by
    rw [cleared,finset_sum_coeff,sum_eq_single (Fin.last i)]
    · have lead := (monic_descPochhammer ℤ i).coeff_natDegree
      rw [descPochhammer_natDegree] at lead
      have mul : BinomialDivisorWindow.multiplier i i=1 := Nat.div_self i.factorial_pos
      simp [coeff_C_mul,last,mul,lead]
    · intro j _ ne
      have lt : j.val < i := by
        have neq : j.val≠i := by intro h; exact ne (Fin.ext h)
        omega
      rw [coeff_C_mul,coeff_eq_zero_of_natDegree_lt ((descPochhammer_natDegree ℤ j.val).trans_lt lt),mul_zero]
    · simp
  have hd := natDegree_eq_of_le_of_coeff_ne_zero (BinomialDivisorWindow.degree_bound i v) (eq ▸ one_ne_zero)
  exact ⟨hd,by simpa only [Monic,leadingCoeff,hd] using eq⟩

/-- A single public relation with at most k roots covers every divisor in the
window whose factorial denominator can be canceled. -/
theorem relation_exists {k m n U D : ℕ} (hn : 0<n) (hd : 0<D)
    (room : n^(m+m.choose 2)*((k+1)^(k+1)*∏ i : Fin (k+1), weight U i.val)<(D^m)^(k+1))
    (t : ℤ) : ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤k ∧ ∀ (x : ℕ) (d : ℤ),
      d∣(n:ℤ) → d∣(x:ℤ)-t → (D:ℤ)≤d → IsCoprime d (k.factorial:ℤ) → x≤4*U → F.eval (x:ℤ)=0 := by
  classical
  choose row last small using rounded_row U
  let P (i : ℕ) := cleared i (row i)
  have deg (i : ℕ) := cleared_top i (row i) (last i)
  let seq : Polynomial.Sequence ℤ := ⟨P,fun i => by
    rw [Polynomial.degree_eq_natDegree (deg i).2.ne_zero,(deg i).1]⟩
  have li : LinearIndependent ℤ (fun i : Fin (k+1) => P i.val) :=
    seq.linearIndependent.comp (fun i : Fin (k+1) => i.val) Fin.val_injective
  let scale (i : Fin (k+1)) : ℤ := BinomialDivisorWindow.multiplier k i.val
  have sc (i : Fin (k+1)) : scale i*(i.val.factorial:ℤ)=k.factorial := by
    dsimp only [scale]
    exact_mod_cast BinomialDivisorWindow.multiplier_exact (show i.val≤k by omega)
  have nzScale (i : Fin (k+1)) : scale i≠0 := by
    intro h; have h' := sc i; rw [h,zero_mul] at h'
    exact k.factorial_ne_zero (by exact_mod_cast h'.symm)
  let F (v : Fin (k+1) → ℤ) := ∑ i, C (v i*scale i)*P i.val
  letI (i : Fin m) : NeZero (n^(m-i.val)) := ⟨(pow_pos hn _).ne'⟩
  let L := (i : Fin m) → ZMod (n^(m-i.val))
  let tag (v : Fin (k+1) → ℤ) : L := fun i => ((taylor t (F v)).coeff i.val:ℤ)
  have size : Fintype.card L * ((k+1)^(k+1)*∏ i : Fin (k+1), weight U i.val)<(D^m)^(k+1) := by
    simpa only [L,Fintype.card_pi,ZMod.card,prod_pow_eq_pow_sum,HigherDivisorWindow.tag_sum] using room
  obtain ⟨u,v,ne,eq,short⟩ := HigherDivisorWindow.finite_collision (by omega : 0<k+1) (pow_pos hd m)
    (fun i : Fin (k+1) => weight U i.val) (fun _ => Nat.succ_pos _) size tag
  let w := u-v
  have nonzero : F w≠0 := by
    intro h
    have z := (Fintype.linearIndependent_iff.mp li) (fun i => w i*scale i)
      (by simpa only [F,Polynomial.smul_eq_C_mul] using h)
    exact (sub_ne_zero.mpr ne) (_root_.funext fun i => (mul_eq_zero.mp (z i)).resolve_right (nzScale i))
  refine ⟨F w,nonzero,?_,?_⟩
  · apply (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_C_mul_le _ _).trans ((deg i.val).1.trans_le (by omega))
  · have jets : HigherDivisorWindow.Jets m n t (F w) := by
      have sub : F w=F u-F v := by simp [w,F,sub_mul,sum_sub_distrib]
      intro i
      rw [sub,map_sub,coeff_sub,←Nat.cast_pow,←ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,sub_eq_zero]
      exact congrFun eq i
    intro x d factor offset floor coprime near
    let y := ∑ i, w i*value (row i.val) x
    have ev : (F w).eval (x:ℤ) = (k.factorial:ℤ)*y := by
      simp only [F,P,eval_finset_sum,eval_mul,eval_C,BinomialDivisorWindow.eval_cleared,y,mul_sum]
      refine sum_congr rfl fun i _ => ?_
      linear_combination w i*value (row i.val) x*sc i
    have div := HigherDivisorWindow.dvd_eval_of_jets jets factor offset
    rw [ev] at div ⊢
    have smallVal : |y|≤∑ i, |u i - v i| * (weight U i.val:ℤ) := by
      refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (small i.val x near) (abs_nonneg _)
    have zero := Int.eq_zero_of_abs_lt_dvd (coprime.pow_left.dvd_of_dvd_mul_left div)
      ((smallVal.trans_lt (by simpa using short : _ < (D:ℤ)^m)).trans_le
        (pow_le_pow_left₀ (Int.natCast_nonneg D) floor m))
    rw [zero,mul_zero]

section Finite

set_option exponentiation.threshold 34000000
set_option maxRecDepth 16000
set_option maxHeartbeats 6000000

private theorem box_cost : 129^129*(∏ i ∈ range 129, weight (2^512) i)<2^4187605 := by
  decide +kernel

/-- Width H=2^514 in the index x, using the product-coupled lower divisor floor.
The degree is 128 and Taylor depth is 64. This is a finite-existence comparison. -/
theorem uniform_room {n : ℕ} (large : 2^2047≤n) :
    n^(64+(64:ℕ).choose 2)*(129^129*∏ i : Fin 129, weight (2^512) i.val)<
      ((CoupledDivisorWindow.lower n)^64)^129 := by
  rw [Fin.prod_univ_eq_prod_range (weight (2^512)) 129,mul_comm,←pow_mul]
  apply CoupledDivisorWindow.coupled_cost large box_cost <;> decide

/-- Compute an anchor before examining a divisor. One polynomial of degree at
most 128 covers all the odd progression indices through 2^514 inclusively. -/
theorem uniform_window {n : ℕ} (large : 2^2047≤n) {c s t : ℤ}
    (unit : IsCoprime s (n:ℤ)) (anchor : (n:ℤ)∣c+s*t) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤128 ∧ ∀ (x : ℕ) (d : ℤ),
      d∣(n:ℤ) → d=c+s*(x:ℤ) → (CoupledDivisorWindow.lower n:ℤ)≤d →
      IsCoprime d ((128:ℕ).factorial:ℤ) → x≤2^514 → F.eval (x:ℤ)=0 := by
  have hn := (by positivity : 0<(2:ℕ)^2047).trans_le large
  have hd := (by positivity : 0<(2:ℕ)^1023).trans_le (CoupledDivisorWindow.lower_size large)
  obtain ⟨F,nz,count,all⟩ := relation_exists (k:=128) (m:=64) hn hd (uniform_room large) t
  refine ⟨F,nz,count,?_⟩
  intro x d factor pos floor coprime near
  exact all x d factor (QuarticDivisorWindow.progression_offset unit anchor factor pos) floor coprime
    ((by decide : (2:ℕ)^514=4*2^512) ▸ near)

/-- At H=2^513 the same rounded basis also satisfies the separate classical
LLL numerical condition, even using independent worst-case endpoints. -/
theorem lll_envelope : 129^(2*129)*2^(128*129)*
    (((2^2048:ℕ)^(64+(64:ℕ).choose 2))*(∏ i ∈ range 129, weight (2^511) i))^4 <
    ((2^1023)^64)^(4*129) := by decide +kernel

/-- Product of the original one-sided binomial bounds, using only 128 descending
factors per column so huge upper binomial arguments evaluate efficiently. -/
private noncomputable def ordinary (H : ℕ) := ∏ i ∈ range 129, H.descFactorial i/i.factorial

private theorem ordinary_eq (H : ℕ) : (∏ i : Fin 129, H.choose i.val)=ordinary H := by
  rw [Fin.prod_univ_eq_prod_range H.choose 129]
  unfold ordinary
  apply prod_congr rfl
  intro i _
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.mul_div_cancel_left _ i.factorial_pos]

/-- Both controls at the same degree and depth pass the ordinary box at H=2^512
and fail at H=2^513, using each control's own ceiling N/2^1024. -/
theorem controls_ordinary : ∀ n ∈ [ChebyshevQuarticScale.fresh,ChebyshevQuarticScale.crossed],
    n^(64+(64:ℕ).choose 2)*(129^129*∏ i : Fin 129, (2^512:ℕ).choose i.val)<
      ((CoupledDivisorWindow.lower n)^64)^129 ∧
    ((CoupledDivisorWindow.lower n)^64)^129 ≤
      n^(64+(64:ℕ).choose 2)*(129^129*∏ i : Fin 129, (2^513:ℕ).choose i.val) := by
  rw [ordinary_eq,ordinary_eq]
  intro n mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl <;> decide +kernel

end Finite
end PrimeFactors.RoundedChebyshevWindows
