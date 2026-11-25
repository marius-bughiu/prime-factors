import PrimeFactors.RoundedChebyshevWindows

/-! Integer-valued polynomials on a translated 3-unit set. Two monic rows,
one for ordinary descending factorials and one for the quadratic unit map,
supply the least common multiple of their fixed divisors. -/

namespace PrimeFactors.ThreeUnitFactorialWindows

open Polynomial Finset

def quadraticDen (i : ℕ) : ℕ := 3^(i/2) * (i/2).factorial

def denominator (i : ℕ) : ℕ := i.factorial.lcm (quadraticDen i)

theorem denominator_pos (i : ℕ) : 0 < denominator i :=
  Nat.lcm_pos i.factorial_pos (Nat.mul_pos (by positivity) (Nat.factorial_pos _))

theorem denominator_dvd {i k : ℕ} (h : i≤k) : denominator i ∣ denominator k := by
  apply Nat.lcm_dvd ((Nat.factorial_dvd_factorial h).trans (Nat.dvd_lcm_left ..))
  apply Dvd.dvd.trans _ (Nat.dvd_lcm_right ..)
  have h' : i/2≤k/2 := by omega
  exact mul_dvd_mul (Nat.pow_dvd_pow 3 h') (Nat.factorial_dvd_factorial h')

private noncomputable def quad (s : ℤ) (j : ℕ) : ℤ[X] := (X+C s)^2-C (1+3*(j:ℤ))

private theorem quad_degree (s : ℤ) (j : ℕ) : (quad s j).natDegree=2 := by
  rw [quad,natDegree_sub_C,natDegree_pow,natDegree_X_add_C,mul_one]

private theorem quad_monic (s : ℤ) (j : ℕ) : (quad s j).Monic := by
  apply ((monic_X_add_C s).pow 2).sub_of_left
  refine degree_C_le.trans_lt ?_
  rw [degree_pow, degree_X_add_C]
  decide

private noncomputable def unitRaw (s : ℤ) (i : ℕ) : ℤ[X] :=
  X^(i%2)*∏ j ∈ range (i/2), quad s j

private theorem unitRaw_top (s : ℤ) (i : ℕ) :
    (unitRaw s i).natDegree=i ∧ (unitRaw s i).Monic := by
  have mon := monic_prod_of_monic (range (i/2)) (quad s) (fun j _ => quad_monic s j)
  refine ⟨?_,(monic_X_pow _).mul mon⟩
  rw [unitRaw,natDegree_mul (monic_X_pow _).ne_zero mon.ne_zero,natDegree_X_pow,
    natDegree_prod _ _ (fun j _ => (quad_monic s j).ne_zero)]
  simp only [quad_degree,sum_const,card_range,smul_eq_mul]
  omega

private theorem unitRaw_dvd (s : ℤ) (i x : ℕ) (unit : ¬(3:ℤ)∣(x:ℤ)+s) :
    (quadraticDen i:ℤ) ∣ (unitRaw s i).eval (x:ℤ) := by
  let z := (x:ℤ)+s
  have nz : z≠0 := by intro eq; exact unit (eq ▸ dvd_zero _ : (3:ℤ)∣z)
  have congr : z^2%3=1 := by
    rw [pow_two,Int.mul_emod]
    have r : z%3=1 ∨ z%3=2 := by change ¬(3:ℤ)∣z at unit; omega
    rcases r with e|e <;> rw [e] <;> decide
  let y := ((z^2-1)/3).toNat
  have non : 0≤(z^2-1)/3 := by
    apply Int.ediv_nonneg _ (by decide)
    rcases lt_or_gt_of_ne nz with neg|pos <;> nlinarith
  have eq : z^2=1+3*(y:ℤ) := by
    dsimp only [y]; rw [Int.toNat_of_nonneg non]; omega
  have ev (j : ℕ) : (quad s j).eval (x:ℤ)=3*((y:ℤ)-j) := by
    simp only [quad,eval_sub,eval_pow,eval_add,eval_X,eval_C]
    change z^2 - _ = _; rw [eq]; ring
  refine ⟨(x:ℤ)^(i%2)*(y.choose (i/2):ℤ),?_⟩
  simp only [unitRaw,eval_mul,eval_pow,eval_X,eval_prod,ev,prod_mul_distrib,prod_const,
    card_range,←descPochhammer_eval_eq_prod_range,descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose,quadraticDen,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

/-- Combine two monic fixed divisors at the level of the leading coefficient. -/
theorem combine {i A B : ℕ} (a : 0<A) (_b : 0<B) (S : ℕ → Prop)
    (P Q : ℤ[X]) (pdeg : P.natDegree=i) (qdeg : Q.natDegree=i)
    (pm : P.Monic) (qm : Q.Monic)
    (pdiv : ∀ x, S x → (A:ℤ)∣P.eval (x:ℤ)) (qdiv : ∀ x, S x → (B:ℤ)∣Q.eval (x:ℤ)) :
    ∃ F : ℤ[X], F.natDegree=i ∧ F.Monic ∧ ∀ x, S x → (A.lcm B:ℤ)∣F.eval (x:ℤ) := by
  let g := A.gcd B
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ a
  have cop := (Nat.coprime_div_gcd_div_gcd gp).isCoprime
  obtain ⟨u,v,bez⟩ := cop
  have gpA : g*(A/g)=A := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have gpB : g*(B/g)=B := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have lA : (A/g)*B=A.lcm B := by
    apply Nat.mul_left_cancel gp
    rw [←mul_assoc,gpA,Nat.gcd_mul_lcm]
  have lB : (B/g)*A=A.lcm B := by
    apply Nat.mul_left_cancel gp
    rw [←mul_assoc,gpB,Nat.gcd_mul_lcm,mul_comm]
  let F := C (u*(A/g:ℕ))*Q+C (v*(B/g:ℕ))*P
  have top : F.coeff i=1 := by
    simpa only [F,coeff_add,coeff_C_mul,←qdeg,qm.coeff_natDegree,
      show P.coeff Q.natDegree=1 by rw [qdeg,←pdeg,pm.coeff_natDegree],mul_one] using bez
  have lim : F.natDegree ≤ i := (natDegree_add_le ..).trans
    (max_le ((natDegree_C_mul_le ..).trans qdeg.le) ((natDegree_C_mul_le ..).trans pdeg.le))
  have deg := natDegree_eq_of_le_of_coeff_ne_zero lim (top ▸ one_ne_zero)
  refine ⟨F,deg,by simpa only [Monic,leadingCoeff,deg] using top,?_⟩
  intro x hx
  obtain ⟨p,ep⟩ := pdiv x hx
  obtain ⟨q,eq⟩ := qdiv x hx
  refine ⟨u*q+v*p,?_⟩
  simp only [F,eval_add,eval_mul,eval_C,ep,eq]
  have la : ((A/g:ℕ):ℤ)*B=(A.lcm B:ℤ) := by exact_mod_cast lA
  have lb : ((B/g:ℕ):ℤ)*A=(A.lcm B:ℤ) := by exact_mod_cast lB
  linear_combination u*q*la + v*p*lb

/-- At every degree the two classical fixed divisors can be realized together
by one monic integer polynomial on the translated units. -/
theorem monic_row (s : ℤ) (i : ℕ) : ∃ P : ℤ[X], P.natDegree=i ∧ P.Monic ∧
    ∀ x : ℕ, ¬(3:ℤ)∣(x:ℤ)+s → (denominator i:ℤ)∣P.eval (x:ℤ) := by
  apply combine i.factorial_pos (Nat.mul_pos (by positivity) (Nat.factorial_pos _)) _
    (descPochhammer ℤ i) (unitRaw s i) (descPochhammer_natDegree ..) (unitRaw_top s i).1
    (monic_descPochhammer ..) (unitRaw_top s i).2 _ (unitRaw_dvd s i)
  intro x _
  exact ⟨x.choose i,by rw [descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]⟩

noncomputable def weight (U i : ℕ) : ℕ := ChebyshevDivisorWindow.weight U i / denominator i +
  (∑ j ∈ range i, (4*U)^j/j.factorial)+1

/-- Round only the lower ordinary binomial coordinates. The size of the
Bézout multipliers in the starting monic row disappears from the bound. -/
theorem rounded_row (s : ℤ) (U i : ℕ) : ∃ F : ℤ[X], F.natDegree=i ∧ F.Monic ∧
    ∀ x : ℕ, ¬(3:ℤ)∣(x:ℤ)+s → x≤4*U →
    ∃ y : ℤ, F.eval (x:ℤ)=(denominator i:ℤ)*y ∧ |y|≤(weight U i:ℤ) := by
  classical
  let D := denominator i
  have pos : 0<D := denominator_pos i
  obtain ⟨S,ds,ms,div⟩ := monic_row s i
  let P := (ChebyshevDivisorWindow.basis U i).comp (X-C (2*(U:ℤ)))
  have deg : P.natDegree=i := by
    dsimp only [P]
    rw [natDegree_comp,(ChebyshevDivisorWindow.degree_basis U i).1,natDegree_X_sub_C,mul_one]
  have mon : P.Monic := (ChebyshevDivisorWindow.degree_basis U i).2.comp (monic_X_sub_C _)
    (by rw [natDegree_X_sub_C]; decide)
  obtain ⟨b,eq,top⟩ := RoundedChebyshevWindows.falling_expansion i (P-S)
    ((natDegree_sub_le ..).trans (max_le deg.le ds.le))
  have last : b (Fin.last i)=0 := by
    rw [top,coeff_sub,show P.coeff i=1 by rw [←deg,mon.coeff_natDegree],
      show S.coeff i=1 by rw [←ds,ms.coeff_natDegree],sub_self]
  let num (j : Fin i) : ℤ := b j.castSucc*(j.val.factorial:ℤ)
  let q (j : Fin i) := (num j).bdiv D
  let sc (j : Fin i) : ℤ := (D/j.val.factorial:ℕ)
  have scale (j : Fin i) : sc j*(j.val.factorial:ℤ)=D := by
    have h : j.val.factorial∣D := (Nat.factorial_dvd_factorial j.isLt.le).trans (Nat.dvd_lcm_left ..)
    dsimp only [sc]; exact_mod_cast Nat.div_mul_cancel h
  let Cj (j : Fin i) := C (q j*sc j)*descPochhammer ℤ j.val
  let F := S+∑ j, Cj j
  have low (j : Fin i) : (Cj j).natDegree < i :=
    (natDegree_C_mul_le ..).trans_lt ((descPochhammer_natDegree ..).trans_lt j.isLt)
  have lead : F.coeff i=1 := by
    have h (j : Fin i) : (Cj j).coeff i = 0 := coeff_eq_zero_of_natDegree_lt (low j)
    simp only [F,coeff_add,finset_sum_coeff,h,sum_const_zero,add_zero]
    rw [←ds,ms.coeff_natDegree]
  have lim : F.natDegree ≤ i := (natDegree_add_le ..).trans
    (max_le ds.le (natDegree_sum_le_of_forall_le _ _ (fun j _ => (low j).le)))
  have degree := natDegree_eq_of_le_of_coeff_ne_zero lim (lead ▸ one_ne_zero)
  refine ⟨F,degree,by simpa only [Monic,leadingCoeff,degree] using lead,?_⟩
  intro x unit near
  obtain ⟨v,hv⟩ := div x unit
  let y := v+∑ j, q j*(x.choose j.val:ℤ)
  have rowEval : F.eval (x:ℤ)=(D:ℤ)*y := by
    simp only [F,eval_add,hv,eval_finset_sum,Cj,eval_mul,eval_C,
      descPochhammer_eval_eq_descFactorial,Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul,
      y,mul_add,mul_sum]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    linear_combination q j*(x.choose j.val:ℤ)*scale j
  refine ⟨y,rowEval,?_⟩
  have ev : P.eval (x:ℤ)-S.eval (x:ℤ) = ∑ j : Fin i, num j*(x.choose j.val:ℤ) := by
    rw [←eval_sub,eq,eval_finset_sum,Fin.sum_univ_castSucc]
    simp only [eval_mul,eval_C,descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul,Fin.coe_castSucc,num,mul_assoc,last,
      zero_mul,add_zero]
  have diff : P.eval (x:ℤ)-(D:ℤ)*y=∑ j, (num j).bmod D*(x.choose j.val:ℤ) := by
    have base : P.eval (x:ℤ)-(D:ℤ)*v=∑ j, num j*(x.choose j.val:ℤ) := by simpa [hv,D] using ev
    simp only [y,mul_add,mul_sum,sub_add_eq_sub_sub,base,←sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [Int.bmod_eq_self_sub_mul_bdiv]; dsimp only [q]; ring
  have err : |P.eval (x:ℤ)-(D:ℤ)*y|≤(D:ℤ)*∑ j : Fin i, (((4*U)^j.val/j.val.factorial:ℕ):ℤ) := by
    rw [diff,mul_sum]
    refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun j _ => ?_)
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
    have small := RoundedChebyshevWindows.half_error (num j) pos
    rw [←Int.bmod_eq_self_sub_mul_bdiv] at small
    have bound : (4*U).choose j.val≤(4*U)^j.val/j.val.factorial := by
      apply (Nat.le_div_iff_mul_le j.val.factorial_pos).mpr
      simpa only [Nat.descFactorial_eq_factorial_mul_choose,mul_comm] using Nat.descFactorial_le_pow (4*U) j.val
    exact mul_le_mul (by omega) (by exact_mod_cast (Nat.choose_le_choose j.val near).trans bound)
      (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have target : |P.eval (x:ℤ)|≤(ChebyshevDivisorWindow.weight U i:ℤ) := by
    simp only [P,eval_comp,eval_sub,eval_X,eval_C]
    exact ChebyshevDivisorWindow.eval_bound U i _ (abs_le.mpr (by omega))
  have tri := abs_sub_le ((D:ℤ)*y) (P.eval (x:ℤ)) 0
  rw [abs_sub_comm ((D:ℤ)*y) (P.eval (x:ℤ))] at tri
  simp only [sub_zero,abs_mul,abs_of_nonneg (Int.natCast_nonneg D)] at tri
  have bound : |y|-(∑ j : Fin i, (((4*U)^j.val/j.val.factorial:ℕ):ℤ))≤
      (ChebyshevDivisorWindow.weight U i:ℤ)/(D:ℤ) := by
    apply (Int.le_ediv_iff_mul_le (by exact_mod_cast pos)).mpr
    nlinarith only [tri,target,err]
  rw [Fin.sum_univ_eq_sum_range (fun j => (((4*U)^j/j.factorial:ℕ):ℤ)) i] at bound
  simp only [weight,Nat.cast_add,Nat.cast_one,Nat.cast_sum,Int.natCast_ediv]
  dsimp only [D] at bound
  simp only [Int.natCast_ediv] at bound
  omega

/-- One input-only relation for the entire window. Divisors are restricted
to the translated unit set, and must be coprime to the last denominator. -/
theorem relation_exists {k m n U D : ℕ} (hn : 0<n) (hd : 0<D)
    (room : n^(m+m.choose 2)*((k+1)^(k+1)*∏ i : Fin (k+1), weight U i.val)<(D^m)^(k+1))
    (s t : ℤ) : ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤k ∧ ∀ (x : ℕ) (d : ℤ),
      d∣(n:ℤ) → d∣(x:ℤ)-t → (D:ℤ)≤d → IsCoprime d (denominator k:ℤ) →
      ¬(3:ℤ)∣(x:ℤ)+s → x≤4*U → F.eval (x:ℤ)=0 := by
  classical
  choose P degree mon small using rounded_row s U
  let seq : Polynomial.Sequence ℤ := ⟨P,fun i => by
    rw [Polynomial.degree_eq_natDegree (mon i).ne_zero,degree i]⟩
  have li : LinearIndependent ℤ (fun i : Fin (k+1) => P i.val) :=
    seq.linearIndependent.comp (fun i : Fin (k+1) => i.val) Fin.val_injective
  let scale (i : Fin (k+1)) : ℤ := (denominator k / denominator i.val:ℕ)
  have sc (i : Fin (k+1)) : scale i*(denominator i.val:ℤ)=denominator k := by
    dsimp only [scale]
    exact_mod_cast Nat.div_mul_cancel (denominator_dvd (show i.val≤k by omega))
  have nzScale (i : Fin (k+1)) : scale i≠0 := by
    intro h; have e := sc i; rw [h,zero_mul] at e
    exact (denominator_pos k).ne' (by exact_mod_cast e.symm)
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
    intro x d factor offset floor coprime unit near
    choose val eval bound using fun i : Fin (k+1) => small i.val x unit near
    let y := ∑ i, w i*val i
    have ev : (F w).eval (x:ℤ) = (denominator k:ℤ)*y := by
      simp only [F,eval_finset_sum,eval_mul,eval_C,y,mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [eval i]
      linear_combination w i*val i*sc i
    have div := HigherDivisorWindow.dvd_eval_of_jets jets factor offset
    rw [ev] at div ⊢
    have smallVal : |y|≤∑ i, |u i - v i| * (weight U i.val:ℤ) := by
      refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (bound i) (abs_nonneg _)
    have zero := Int.eq_zero_of_abs_lt_dvd (coprime.pow_left.dvd_of_dvd_mul_left div)
      ((smallVal.trans_lt (by simpa using short : _ < (D:ℤ)^m)).trans_le
        (pow_le_pow_left₀ (Int.natCast_nonneg D) floor m))
    rw [zero,mul_zero]

section Finite

set_option exponentiation.threshold 34000000
set_option maxRecDepth 16000
set_option maxHeartbeats 6000000

/-- Compare the two actual bounded row systems at fixed degree 144, depth 72
and width 2^515 in the progression index. -/
theorem box_comparison :
    145^145*(∏ i ∈ range 145, weight (2^513) i) < 2^5300604 ∧
    2^5300604 ≤ 145^145*(∏ i ∈ range 145, RoundedChebyshevWindows.weight (2^513) i) := by
  decide +kernel

theorem uniform_room {n : ℕ} (large : 2^2047≤n) :
    n^(72+(72:ℕ).choose 2)*(145^145*∏ i : Fin 145, weight (2^513) i.val)<
      ((CoupledDivisorWindow.lower n)^72)^145 := by
  rw [Fin.prod_univ_eq_prod_range (weight (2^513)) 145,mul_comm,←pow_mul]
  apply CoupledDivisorWindow.coupled_cost large box_comparison.1 <;> decide


/-- Both controls pass the public denominator check. The ordinary rounded system
already passes at this width on the fresh control and misses on the crossed one. -/
theorem control_comparison :
    ChebyshevQuarticScale.fresh.Coprime (denominator 144) ∧
    ChebyshevQuarticScale.crossed.Coprime (denominator 144) ∧
    ChebyshevQuarticScale.fresh^(72+(72:ℕ).choose 2) *
      (145^145*∏ i ∈ range 145, RoundedChebyshevWindows.weight (2^513) i) <
      ((CoupledDivisorWindow.lower ChebyshevQuarticScale.fresh)^72)^145 ∧
    ((CoupledDivisorWindow.lower ChebyshevQuarticScale.crossed)^72)^145 ≤
      ChebyshevQuarticScale.crossed^(72+(72:ℕ).choose 2) *
      (145^145*∏ i ∈ range 145, RoundedChebyshevWindows.weight (2^513) i) := by
  decide +kernel

/-- The offset and translated unit condition come entirely from the odd
progression's public anchor, its left endpoint and the input gcd. -/
theorem uniform_window {n : ℕ} (large : 2^2047≤n) (cop : n.Coprime (denominator 144))
    {c t : ℤ} (odd : IsCoprime (2:ℤ) (n:ℤ)) (anchor : (n:ℤ)∣c+2*t) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤144 ∧ ∀ (x : ℕ) (d : ℤ),
      d∣(n:ℤ) → d=c+2*(x:ℤ) → (CoupledDivisorWindow.lower n:ℤ)≤d →
      x≤2^515 → F.eval (x:ℤ)=0 := by
  have hn := (by positivity : 0<(2:ℕ)^2047).trans_le large
  have hd := (by positivity : 0<(2:ℕ)^1023).trans_le (CoupledDivisorWindow.lower_size large)
  obtain ⟨F,nz,count,all⟩ := relation_exists (k:=144) (m:=72) hn hd (uniform_room large) (2*c) t
  refine ⟨F,nz,count,?_⟩
  intro x d factor pos floor near
  have dc := cop.isCoprime.of_isCoprime_of_dvd_left factor
  have nonunit : ¬(3:ℤ)∣d := by
    intro h
    have impossible : (3:ℤ)∣1 := (dc.isUnit_of_dvd' h (by decide +kernel : (3:ℤ)∣(denominator 144:ℤ))).dvd
    exact (by decide : ¬(3:ℤ)∣1) impossible
  have unit : ¬(3:ℤ)∣(x:ℤ)+2*c := by omega
  exact all x d factor (QuarticDivisorWindow.progression_offset odd anchor factor pos) floor dc unit
    ((by decide : (2:ℕ)^515=4*2^513) ▸ near)

end Finite
end PrimeFactors.ThreeUnitFactorialWindows
