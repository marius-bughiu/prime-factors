import PrimeFactors.BinomialWindowCertificate
import PrimeFactors.FactorialCollision
import PrimeFactors.CoupledDivisorWindow
import Mathlib.Algebra.GCDMonoid.Finset

/-! Divisor windows on the integer arguments for which the candidate is a unit
modulo 3, 5 and 7. Six public interpolation nodes suffice for degree six. -/

namespace PrimeFactors.SiftedDivisorWindow

open Polynomial Finset

def nodes : Fin 6 → ℤ := ![-16, -17, -19, 22, -11, -22]

/-- Numerator of the ith Newton basis function at a translated index. -/
noncomputable def raw (i : Fin 7) (z : ℤ) : ℤ := ∏ j : Fin i.val, (z - nodes ⟨j.val, by omega⟩)

def denominator : Fin 7 → ℕ := ![1, 1, 6, 6, 360, 360, 45360]

private def twoPart : Fin 7 → ℕ := ![1, 1, 2, 2, 8, 8, 16]
private def threePart : Fin 7 → ℕ := ![1, 1, 3, 3, 9, 9, 81]
private def fivePart : Fin 7 → ℕ := ![1, 1, 1, 1, 5, 5, 5]
private def sevenPart : Fin 7 → ℕ := ![1, 1, 1, 1, 1, 1, 7]

noncomputable def numerator (i : Fin 7) (s : ℤ) : ℤ[X] :=
  ∏ j : Fin i.val, (X + C (s - nodes ⟨j.val, by omega⟩))

theorem eval_numerator (i : Fin 7) (x s : ℤ) : (numerator i s).eval x = raw i (x+s) := by
  simp only [numerator, raw, eval_prod, eval_add, eval_X, eval_C, add_sub_assoc]

private theorem raw_congr {m z y : ℤ} (h : z ≡ y [ZMOD m]) (i : Fin 7) :
    raw i z ≡ raw i y [ZMOD m] := by
  apply Int.modEq_iff_dvd.mpr
  simpa only [eval_numerator, add_zero] using
    (Int.modEq_iff_dvd.mp h).trans (Polynomial.sub_dvd_eval_sub y z (numerator i 0))

/-- A prime-power table needs at most 81 representative arguments. -/
private theorem lift_table (i : Fin 7) (m p a : ℕ) (hm : 0<m) (ha : a∣m)
    (hp : p∣m) (ok : p=1 ∨ ¬(p:ℤ)∣z)
    (table : ∀ j : Fin m, p=1 ∨ ¬p∣j.val → (a:ℤ)∣raw i j.val) :
    (a:ℤ)∣raw i z := by
  let y := z % (m:ℤ)
  have pos : (0:ℤ)<m := by exact_mod_cast hm
  have hy : 0≤y := Int.emod_nonneg _ pos.ne'
  have lt : y<(m:ℤ) := Int.emod_lt_of_pos _ pos
  let j : Fin m := ⟨y.toNat, by omega⟩
  have eq : (j.val:ℤ)=y := Int.toNat_of_nonneg hy
  have h : z ≡ y [ZMOD (m:ℤ)] := (Int.mod_modEq ..).symm
  have tab := table j (ok.imp_right fun no hdiv => by
    apply no
    have dy : (p:ℤ)∣y := eq ▸ (by exact_mod_cast hdiv : (p:ℤ)∣j.val)
    have diff := Int.modEq_iff_dvd.mp (h.of_dvd (by exact_mod_cast hp : (p:ℤ)∣m))
    simpa using dvd_sub dy diff)
  rw [eq] at tab
  have diff := Int.modEq_iff_dvd.mp (raw_congr (h.of_dvd (by exact_mod_cast ha : (a:ℤ)∣m)) i)
  simpa using dvd_sub tab diff

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every row is integer-valued at every index allowed by the three public unit tests. -/
theorem denominator_dvd (i : Fin 7) {z : ℤ}
    (h3 : ¬(3:ℤ)∣z) (h5 : ¬(5:ℤ)∣z) (h7 : ¬(7:ℤ)∣z) :
    (denominator i:ℤ)∣raw i z := by
  have h2 := lift_table (z:=z) i 16 1 (twoPart i) (by decide)
    ((by decide +kernel : ∀ k, twoPart k∣16) i) (by decide) (Or.inl rfl)
    ((by decide +kernel : ∀ k, ∀ j : Fin 16, 1=1 ∨ ¬1∣j.val → (twoPart k:ℤ)∣raw k j.val) i)
  have h3' := lift_table (z:=z) i 81 3 (threePart i) (by decide)
    ((by decide +kernel : ∀ k, threePart k∣81) i) (by decide) (Or.inr h3)
    ((by decide +kernel : ∀ k, ∀ j : Fin 81, 3=1 ∨ ¬3∣j.val → (threePart k:ℤ)∣raw k j.val) i)
  have h5' := lift_table (z:=z) i 5 5 (fivePart i) (by decide)
    ((by decide +kernel : ∀ k, fivePart k∣5) i) (by decide) (Or.inr h5)
    ((by decide +kernel : ∀ k, ∀ j : Fin 5, 5=1 ∨ ¬5∣j.val → (fivePart k:ℤ)∣raw k j.val) i)
  have h7' := lift_table (z:=z) i 7 7 (sevenPart i) (by decide)
    ((by decide +kernel : ∀ k, sevenPart k∣7) i) (by decide) (Or.inr h7)
    ((by decide +kernel : ∀ k, ∀ j : Fin 7, 7=1 ∨ ¬7∣j.val → (sevenPart k:ℤ)∣raw k j.val) i)
  have c1 : ∀ k, (twoPart k).Coprime (threePart k) := by decide +kernel
  have c2 : ∀ k, (twoPart k * threePart k).Coprime (fivePart k) := by decide +kernel
  have c3 : ∀ k, (twoPart k * threePart k * fivePart k).Coprime (sevenPart k) := by decide +kernel
  have decomp : ∀ k, denominator k = twoPart k * threePart k * fivePart k * sevenPart k := by decide +kernel
  rw [decomp, Nat.cast_mul]
  apply (c3 i).isCoprime.mul_dvd _ h7'
  rw [Nat.cast_mul]
  apply (c2 i).isCoprime.mul_dvd _ h5'
  rw [Nat.cast_mul]
  exact (c1 i).isCoprime.mul_dvd h2 h3'

private def samples : Fin 6 → ℕ := ![1, 2, 4, 13, 16, 23]

/-- This denominator is the greatest common divisor of all eligible evaluations of
this numerator. Six explicit positive arguments suffice for the reverse bound. -/
theorem common_divisor_dvd (i : Fin 7) (a : ℕ)
    (all : ∀ z : ℤ, ¬(3:ℤ)∣z → ¬(5:ℤ)∣z → ¬(7:ℤ)∣z → (a:ℤ)∣raw i z) :
    a∣denominator i := by
  have witness : ∀ k, univ.gcd (fun j : Fin 6 => (raw k (samples j)).natAbs) = denominator k := by
    decide +kernel
  have ok : ∀ j, ¬(3:ℤ)∣(samples j:ℤ) ∧ ¬(5:ℤ)∣(samples j:ℤ) ∧ ¬(7:ℤ)∣(samples j:ℤ) := by
    decide +kernel
  rw [←witness]
  apply Finset.dvd_gcd
  intro j _
  exact Int.natAbs_dvd_natAbs.mpr (all _ (ok j).1 (ok j).2.1 (ok j).2.2)

noncomputable def bound (i : Fin 7) (r : ℕ) (s : ℤ) : ℕ :=
  ∏ j : Fin i.val, (r+(s - nodes ⟨j.val, by omega⟩).natAbs)

noncomputable def weight (i : Fin 7) (r : ℕ) (s : ℤ) : ℕ :=
  max 1 (bound i r s / denominator i)

noncomputable def height (v : Fin 7 → ℤ) (r : ℕ) (s : ℤ) : ℤ :=
  ∑ i, |v i| * (weight i r s:ℤ)

private theorem raw_bound {r : ℕ} {x : ℤ} (s : ℤ) (i : Fin 7) (near : |x|≤(r:ℤ)) :
    |raw i (x+s)| ≤ (bound i r s:ℤ) := by
  rw [raw, bound, abs_prod, Nat.cast_prod]
  apply prod_le_prod
  · intro _ _
    exact abs_nonneg _
  · intro j _
    rw [Nat.cast_add, Int.natCast_natAbs, add_sub_assoc]
    exact (abs_add_le ..).trans (add_le_add_right near _)

private theorem scaled_value_bound {r : ℕ} {x : ℤ} (s : ℤ) (i : Fin 7) (q : ℤ)
    (near : |x|≤(r:ℤ)) (eqn : raw i (x+s)=(denominator i:ℤ)*q) :
    |q|≤(weight i r s:ℤ) := by
  have pos : ∀ k, 0<denominator k := by decide +kernel
  have b := raw_bound s i near
  rw [eqn, abs_mul, abs_of_nonneg (Int.natCast_nonneg _)] at b
  have div : |q|≤(bound i r s:ℤ)/(denominator i:ℤ) :=
    (Int.le_ediv_iff_mul_le (by exact_mod_cast pos i)).mpr (by simpa [mul_comm] using b)
  have nat := le_max_right 1 (bound i r s / denominator i)
  exact div.trans (by exact_mod_cast nat)

def scale (i : Fin 7) := 45360 / denominator i

noncomputable def cleared (v : Fin 7 → ℤ) (s : ℤ) : ℤ[X] :=
  ∑ i, C (v i * (scale i:ℤ)) * numerator i s

theorem eval_cleared (v : Fin 7 → ℤ) (s x : ℤ) :
    (cleared v s).eval x = ∑ i, v i * (scale i:ℤ) * raw i (x+s) := by
  simp only [cleared, eval_finset_sum, eval_mul, eval_C, eval_numerator]

theorem numerator_degree (i : Fin 7) (s : ℤ) : (numerator i s).natDegree ≤ i.val := by
  unfold numerator
  refine (natDegree_prod_le ..).trans ?_
  calc
    _ ≤ ∑ _ : Fin i.val, 1 := by
      apply sum_le_sum
      intro j _
      exact (natDegree_X_add_C _).le
    _ = _ := by simp

private theorem degree_bound (v : Fin 7 → ℤ) (s : ℤ) : (cleared v s).natDegree≤6 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le _ _).trans ((numerator_degree i s).trans (by omega))

noncomputable def sampleChecks (v w : Fin 7 → ℤ) (s : ℤ) : Prop :=
  ∀ x : Fin 7, (∑ i, v i*(scale i:ℤ)*raw i (x.val+s)) = ∑ i, w i*(x.val:ℤ)^i.val

theorem same_polynomial {v w : Fin 7 → ℤ} {s : ℤ} (samplesAgree : sampleChecks v w s) :
    cleared v s=ofFn 7 w := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (v:=fun i : Fin 7 => (i.val:ℤ)) univ
  · intro a _ b _ eq
    change (a.val:ℤ)=(b.val:ℤ) at eq
    exact Fin.ext (by exact_mod_cast eq)
  · rw [card_univ, Fintype.card_fin]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le (degree_bound v s))
  · rw [card_univ, Fintype.card_fin]
    exact ofFn_degree_lt w
  · intro i _
    rw [eval_cleared, HigherDivisorWindow.eval_coeff]
    exact samplesAgree i

/-- The public shift transfers all three unit tests to each actual divisor. -/
theorem eligible_divisibility {n d c s x : ℤ} (cop : IsCoprime n 45360) (div : d∣n)
    (position : d=c+2*x) (align : (105:ℤ)∣c-2*s) (i : Fin 7) :
    (denominator i:ℤ)∣raw i (x+s) := by
  obtain ⟨k,hk⟩ := align
  have unit : IsCoprime (x+s) (105:ℤ) := by
    obtain ⟨u,w,bez⟩ := (cop.of_isCoprime_of_dvd_left div).of_isCoprime_of_dvd_right
      (by decide : (105:ℤ)∣45360)
    refine ⟨2*u, w+u*k, ?_⟩
    linear_combination bez - u*position - u*hk
  have avoids (p : ℤ) (h : p∣105) (nonunit : ¬p∣1) : ¬p∣x+s := by
    intro both
    exact nonunit (unit.isUnit_of_dvd' both h).dvd
  exact denominator_dvd i (avoids 3 (by decide) (by decide)) (avoids 5 (by decide) (by decide))
    (avoids 7 (by decide) (by decide))

/-- At any actual divisor, the raw row is 45360 times a bounded integer. -/
theorem eligible_value {n d c s x : ℤ} {r : ℕ} (v : Fin 7 → ℤ)
    (cop : IsCoprime n 45360) (div : d∣n) (position : d=c+2*x)
    (align : (105:ℤ)∣c-2*s) (near : |x|≤(r:ℤ)) :
    ∃ a : ℤ, (cleared v s).eval x=45360*a ∧ |a|≤height v r s := by
  obtain ⟨q,hq⟩ := Classical.axiomOfChoice (eligible_divisibility cop div position align)
  refine ⟨∑ i, v i*q i, ?_, ?_⟩
  · rw [eval_cleared, mul_sum]
    apply sum_congr rfl
    intro i _
    have exactScale : ∀ j, (scale j:ℤ)*(denominator j:ℤ)=45360 := by decide +kernel
    rw [hq i]
    linear_combination v i*q i*exactScale i
  · apply (abs_sum_le_sum_abs ..).trans
    apply sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (scaled_value_bound s i _ near (hq i)) (abs_nonneg _)

/-- A kernel-checkable closed-interval exclusion for all divisors of an odd input. -/
theorem excludes {n first r depth modulus : ℕ} {v w : Fin 7 → ℤ} {t s h : ℤ}
    (hn : n%2=1) (oddFirst : first%2=1) (anchor : (n:ℤ)∣(first+2*r:ℕ)+2*t)
    (cop : n.Coprime 45360) (align : (105:ℤ)∣(first+2*r:ℕ)-2*s)
    (samplesAgree : sampleChecks v w s) (jets : HigherWindowCertificate.jetChecks w n depth t)
    (measured : height v r s=h) (small : h<(first:ℤ)^depth) (hm : 0<modulus)
    (miss : HigherWindowCertificate.rootChecks w modulus)
    (d : ℕ) (lo : first≤d) (hi : d≤first+4*r) : ¬ d∣n := by
  intro hd
  have odd := Nat.odd_iff.mpr hn
  have unit := (Nat.coprime_two_left.mpr odd).isCoprime
  obtain ⟨q,hq⟩ := hd
  obtain ⟨a,ha⟩ := (Nat.odd_mul.mp (hq ▸ odd)).1
  have dz : (d:ℤ)∣(n:ℤ) := by exact_mod_cast (show d∣n from ⟨q,hq⟩)
  let x := ((d:ℤ)-(first+2*r:ℕ))/2
  have position : (d:ℤ)=(first+2*r:ℕ)+2*x := by dsimp only [x]; omega
  have near : |x|≤(r:ℤ) := by rw [abs_le]; dsimp only [x]; omega
  have eqn := same_polynomial samplesAgree
  have translated : HigherDivisorWindow.Jets depth n t (cleared v s) := by
    intro j
    rw [eqn,HigherDivisorWindow.jet_coeff]
    exact jets j
  have dvd := HigherDivisorWindow.dvd_eval_of_jets translated dz
    (QuarticDivisorWindow.progression_offset unit anchor dz position)
  obtain ⟨b,eb,bnd⟩ := eligible_value v cop.isCoprime dz position align near
  rw [eb] at dvd
  have hit : (d:ℤ)^depth∣b := (cop.isCoprime.of_isCoprime_of_dvd_left dz).pow_left.dvd_of_dvd_mul_left dvd
  have floor := pow_le_pow_left₀ (Int.natCast_nonneg first) (by exact_mod_cast lo : (first:ℤ)≤d) depth
  have zero := Int.eq_zero_of_abs_lt_dvd hit (bnd.trans_lt (measured.trans_lt (small.trans_le floor)))
  apply HigherWindowCertificate.no_integer_root hm miss x
  rw [←eqn, eb, zero, mul_zero]


private def point : Fin 7 → ℤ := ![-16, -17, -19, 22, -11, -22, 0]

private theorem cleared_nonzero {v : Fin 7 → ℤ} (nz : v≠0) (s : ℤ) : cleared v s≠0 := by
  intro h
  apply nz
  funext i
  change v i=0
  induction i using (measure (Fin.val : Fin 7 → ℕ)).wf.induction with
  | h i ih =>
    have e := eval_cleared v s (point i - s)
    rw [h, eval_zero, sub_add_cancel] at e
    have upper : ∀ i j : Fin 7, i<j → raw j (point i)=0 := by decide +kernel
    rw [sum_eq_single i] at e
    · have diag : ∀ i, (scale i:ℤ) * raw i (point i)≠0 := by decide +kernel
      rw [mul_assoc] at e
      exact (mul_eq_zero.mp e.symm).resolve_right (diag i)
    · intro j _ ne
      rcases lt_or_gt_of_ne ne with lt|gt
      · rw [ih j lt,zero_mul,zero_mul]
      · rw [upper i j gt,mul_zero]
    · simp

/-- An equation for every chosen odd center using just seven coefficients. -/
theorem relation_exists_factorial {n D r m : ℕ} (hn : 0<n) (hd : 0<D) (cop : n.Coprime 45360)
    {s c t : ℤ} (align : (105:ℤ)∣c-2*s) (anchor : (n:ℤ)∣c+2*t) (unit : IsCoprime (2:ℤ) (n:ℤ))
    (room : n^(m+m.choose 2)*((7:ℕ).factorial*∏ i : Fin 7, weight i r s)<(D^m)^7) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤6 ∧ ∀ x d : ℤ,
      d∣(n:ℤ) → d=c+2*x → (D:ℤ)≤d → |x|≤(r:ℤ) → F.eval x=0 := by
  classical
  letI (i : Fin m) : NeZero (n^(m-i.val)) := ⟨(pow_pos hn _).ne'⟩
  let L := (i : Fin m) → ZMod (n^(m-i.val))
  let tag (v : Fin 7 → ℤ) : L := fun i => ((taylor t (cleared v s)).coeff i.val:ℤ)
  have size : Fintype.card L * ((7:ℕ).factorial*∏ i : Fin 7, weight i r s)<(D^m)^7 := by
    simpa only [L,Fintype.card_pi,ZMod.card,prod_pow_eq_pow_sum,HigherDivisorWindow.tag_sum] using room
  obtain ⟨u,v,ne,eq,short⟩ := FactorialCollision.finite_collision (by decide : 0<7) (pow_pos hd m)
    (fun i : Fin 7 => weight i r s) (fun i => (by decide : 0<1).trans_le (le_max_left ..)) size tag
  let w := u-v
  have sub : cleared w s=cleared u s-cleared v s := by simp [w,cleared,sub_mul,sum_sub_distrib]
  have jets : HigherDivisorWindow.Jets m n t (cleared w s) := by
    intro i
    rw [sub,map_sub,coeff_sub,←Nat.cast_pow,←ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,sub_eq_zero]
    exact congrFun eq i
  refine ⟨cleared w s, cleared_nonzero (sub_ne_zero.mpr ne) s,
    (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (degree_bound w s)),?_⟩
  intro x d dv pos floor close
  have offset := QuarticDivisorWindow.progression_offset unit anchor dv pos
  have dvd := HigherDivisorWindow.dvd_eval_of_jets jets dv offset
  obtain ⟨a,h,bnd⟩ := eligible_value w cop.isCoprime dv pos align close
  rw [h] at dvd ⊢
  have hit := (cop.isCoprime.of_isCoprime_of_dvd_left dv).pow_left.dvd_of_dvd_mul_left dvd
  have lim : height w r s<(D:ℤ)^m := by simpa only [height,w,Pi.sub_apply,Nat.cast_pow] using short
  rw [Int.eq_zero_of_abs_lt_dvd hit (bnd.trans_lt (lim.trans_le
    (pow_le_pow_left₀ (Int.natCast_nonneg _) floor m))),mul_zero]

/-- The earlier box criterion is a sufficient special case. -/
theorem relation_exists {n D r m : ℕ} (hn : 0<n) (hd : 0<D) (cop : n.Coprime 45360)
    {s c t : ℤ} (align : (105:ℤ)∣c-2*s) (anchor : (n:ℤ)∣c+2*t) (unit : IsCoprime (2:ℤ) (n:ℤ))
    (room : n^(m+m.choose 2)*(7^7*∏ i : Fin 7, weight i r s)<(D^m)^7) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤6 ∧ ∀ x d : ℤ,
      d∣(n:ℤ) → d=c+2*x → (D:ℤ)≤d → |x|≤(r:ℤ) → F.eval x=0 := by
  apply relation_exists_factorial hn hd cop align anchor unit
  exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by decide : (7:ℕ).factorial≤7^7))).trans_lt room

/-- Worst-case shift overhead is at most 74 units against a radius hundreds of bits wide. -/
theorem weight_upper {s : ℤ} (small : |s|≤52) (r : ℕ) (i : Fin 7) :
    weight i r s ≤ max 1 ((r+74)^i.val / denominator i) := by
  apply max_le_max_left
  apply Nat.div_le_div_right
  unfold bound
  have eqn : (∏ _ : Fin i.val, (r+74))=(r+74)^i.val := by simp
  rw [←eqn]
  apply prod_le_prod'
  intro j _
  have nodeBound : ∀ j, |nodes j|≤22 := by decide +kernel
  have ht := (abs_sub_le s 0 (nodes ⟨j.val,by omega⟩))
  simp only [sub_zero,zero_sub,abs_neg] at ht
  have h : (s - nodes ⟨j.val,by omega⟩).natAbs≤74 := by
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs]
    exact ht.trans (add_le_add small (nodeBound _))
  omega

def shift (c : ℤ) := (158*c+52)%105-52

theorem shift_spec (c : ℤ) : |shift c|≤52 ∧ (105:ℤ)∣c-2*shift c := by
  unfold shift
  constructor
  · rw [abs_le]; omega
  · use 2*((158*c+52)/105)-3*c
    omega

set_option exponentiation.threshold 26000

private theorem window_of_budget {n D r : ℕ} (hn : 0<n) (hd : 0<D) (cop : n.Coprime 45360)
    (odd : Odd n) (c : ℤ) (hc : Odd c)
    (room : n^6*((7:ℕ).factorial*∏ i : Fin 7, max 1 ((r+74)^i.val/denominator i)) < D^21) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤6 ∧ ∀ x d : ℤ,
      d∣(n:ℤ) → d=c+2*x → (D:ℤ)≤d → |x|≤(r:ℤ) → F.eval x=0 := by
  let t := ((n:ℤ)-c)/2
  have anchor : (n:ℤ)∣c+2*t := by
    obtain ⟨b,hb⟩ := odd
    obtain ⟨a,ha⟩ := hc
    refine ⟨1,?_⟩
    dsimp only [t]; omega
  have wh := Finset.prod_le_prod' (fun i (_ : i ∈ (univ : Finset (Fin 7))) => weight_upper (shift_spec c).1 r i)
  have bound := (Nat.mul_le_mul_left (n^6) (Nat.mul_le_mul_left (7:ℕ).factorial wh)).trans_lt room
  apply relation_exists_factorial (m:=3) hn hd cop (shift_spec c).2 anchor (Nat.coprime_two_left.mpr odd).isCoprime
  simpa only [←pow_mul] using bound

/-- Public size bounds alone guarantee a radius just above 2^439 in parity indices. -/
theorem uniform_factorial_window {n : ℕ} (hn : 0<n) (nb : n≤2^2048) (cop : n.Coprime 45360)
    (odd : Odd n) (c : ℤ) (hc : Odd c) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤6 ∧ ∀ x d : ℤ,
      d∣(n:ℤ) → d=c+2*x → (2:ℤ)^1023≤d → |x|≤267*2^431 → F.eval x=0 := by
  let r : ℕ := 267*2^431
  have room : ((2:ℕ)^2048)^6*((7:ℕ).factorial*∏ i : Fin 7,
      max 1 ((r+74)^i.val / denominator i)) < ((2:ℕ)^1023)^21 := by decide +kernel
  have bound := (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left nb 6)).trans_lt room
  simpa only [r,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
    window_of_budget hn (by decide : 0<(2:ℕ)^1023) cop odd c hc bound

/-- Coupling N with the public divisor floor ceil(N/2^1024) proves a larger
radius for inputs with an at-most-1,024-bit cofactor. -/
theorem coupled_factorial_window {n : ℕ} (large : 2^2047≤n) (cop : n.Coprime 45360)
    (odd : Odd n) (c : ℤ) (hc : Odd c) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤6 ∧ ∀ x d : ℤ,
      d∣(n:ℤ) → d=c+2*x → (CoupledDivisorWindow.lower n:ℤ)≤d →
      |x|≤5*2^437 → F.eval x=0 := by
  let r : ℕ := 5*2^437
  have cheap : (7:ℕ).factorial*(∏ i : Fin 7, max 1 ((r+74)^i.val/denominator i)) < 2^9201 := by
    decide +kernel
  have bound := CoupledDivisorWindow.coupled_cost (t:=6) (c:=21) large cheap (by decide) (by decide)
  have hd := (by decide : 0<(2:ℕ)^1023).trans_le (CoupledDivisorWindow.lower_size large)
  have hn := (by decide : 0<(2:ℕ)^2047).trans_le large
  rw [Nat.mul_comm _ (n^6)] at bound
  simpa only [r,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using window_of_budget hn hd cop odd c hc bound

/-- A universal 2048-bit size budget. The 13/8 multiplier is measured relative to
2^438 in parity indices. The hypotheses use only the public input size. -/
theorem uniform_window {n : ℕ} (hn : 0<n) (nb : n≤2^2048) (cop : n.Coprime 45360)
    (odd : Odd n) (c : ℤ) (hc : Odd c) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤6 ∧ ∀ x d : ℤ,
      d∣(n:ℤ) → d=c+2*x → (2:ℤ)^1023≤d → |x|≤13*2^435 → F.eval x=0 := by
  obtain ⟨F,nz,roots,cover⟩ := uniform_factorial_window hn nb cop odd c hc
  refine ⟨F,nz,roots,?_⟩
  intro x d divides offset floor near
  exact cover x d divides offset floor (near.trans (by decide +kernel))

end PrimeFactors.SiftedDivisorWindow
